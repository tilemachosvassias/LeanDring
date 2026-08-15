/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C039
import LeanDring.P5.Data.ColRestCheap.C159
import LeanDring.P5.Data.ColRestCheap.C160
import LeanDring.P5.Data.ColRestCheap.C161
import LeanDring.P5.Data.ColRestCheap.C162
import LeanDring.P5.Data.ColRestCheap.C163
import LeanDring.P5.Data.EntryK.C016
import LeanDring.P5.Data.EntryK.C017
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C047

/-! # Stage-5 leaves, chunk 9 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_69_26_5 (hp : 5 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 5 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp)) T69_26
      hfix69_26 hinj69_26 hcardT69_26
      (fun i => conj_mem_of_fixedPoints _ _ (T69_26 i) (hfix69_26 i) _)
      ⟨69, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 5 hp) Q2.T69_26_2 Q2.hfix69_26_2 Q2.hinj69_26_2
      Q2.hcardT69_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_26_2 i) (Q2.hfix69_26_2 i) _)
      colCert_69_26_5.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_26_10 (hp : 10 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 10 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp)) T69_26
      hfix69_26 hinj69_26 hcardT69_26
      (fun i => conj_mem_of_fixedPoints _ _ (T69_26 i) (hfix69_26 i) _)
      ⟨69, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 10 hp) Q2.T69_26_2 Q2.hfix69_26_2 Q2.hinj69_26_2
      Q2.hcardT69_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_26_2 i) (Q2.hfix69_26_2 i) _)
      colCert_69_26_10.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_26_15 (hp : 15 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 15 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp)) T69_26
      hfix69_26 hinj69_26 hcardT69_26
      (fun i => conj_mem_of_fixedPoints _ _ (T69_26 i) (hfix69_26 i) _)
      ⟨69, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 15 hp) Q2.T69_26_2 Q2.hfix69_26_2 Q2.hinj69_26_2
      Q2.hcardT69_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_26_2 i) (Q2.hfix69_26_2 i) _)
      colCert_69_26_15.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_26_20 (hp : 20 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 20 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp)) T69_26
      hfix69_26 hinj69_26 hcardT69_26
      (fun i => conj_mem_of_fixedPoints _ _ (T69_26 i) (hfix69_26 i) _)
      ⟨69, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 20 hp) Q2.T69_26_2 Q2.hfix69_26_2 Q2.hinj69_26_2
      Q2.hcardT69_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_26_2 i) (Q2.hfix69_26_2 i) _)
      colCert_69_26_20.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_30_0 (hp : 0 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 0 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp)) T69_30
      hfix69_30 hinj69_30 hcardT69_30
      (fun i => conj_mem_of_fixedPoints _ _ (T69_30 i) (hfix69_30 i) _)
      ⟨69, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 0 hp) Q2.T69_30_2 Q2.hfix69_30_2 Q2.hinj69_30_2
      Q2.hcardT69_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_30_2 i) (Q2.hfix69_30_2 i) _)
      colCert_69_30_0.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_30_1 (hp : 1 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 1 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp)) T69_30
      hfix69_30 hinj69_30 hcardT69_30
      (fun i => conj_mem_of_fixedPoints _ _ (T69_30 i) (hfix69_30 i) _)
      ⟨69, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 1 hp) Q2.T69_30_2 Q2.hfix69_30_2 Q2.hinj69_30_2
      Q2.hcardT69_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_30_2 i) (Q2.hfix69_30_2 i) _)
      colCert_69_30_1.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_30_2 (hp : 2 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 2 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp)) T69_30
      hfix69_30 hinj69_30 hcardT69_30
      (fun i => conj_mem_of_fixedPoints _ _ (T69_30 i) (hfix69_30 i) _)
      ⟨69, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 2 hp) Q2.T69_30_2 Q2.hfix69_30_2 Q2.hinj69_30_2
      Q2.hcardT69_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_30_2 i) (Q2.hfix69_30_2 i) _)
      colCert_69_30_2.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_30_3 (hp : 3 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 3 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp)) T69_30
      hfix69_30 hinj69_30 hcardT69_30
      (fun i => conj_mem_of_fixedPoints _ _ (T69_30 i) (hfix69_30 i) _)
      ⟨69, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 3 hp) Q2.T69_30_2 Q2.hfix69_30_2 Q2.hinj69_30_2
      Q2.hcardT69_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_30_2 i) (Q2.hfix69_30_2 i) _)
      colCert_69_30_3.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_30_4 (hp : 4 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 4 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp)) T69_30
      hfix69_30 hinj69_30 hcardT69_30
      (fun i => conj_mem_of_fixedPoints _ _ (T69_30 i) (hfix69_30 i) _)
      ⟨69, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 4 hp) Q2.T69_30_2 Q2.hfix69_30_2 Q2.hinj69_30_2
      Q2.hcardT69_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_30_2 i) (Q2.hfix69_30_2 i) _)
      colCert_69_30_4.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_30_5 (hp : 5 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 5 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨69, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp)) T69_30
      hfix69_30 hinj69_30 hcardT69_30
      (fun i => conj_mem_of_fixedPoints _ _ (T69_30 i) (hfix69_30 i) _)
      ⟨69, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 5 hp) Q2.T69_30_2 Q2.hfix69_30_2 Q2.hinj69_30_2
      Q2.hcardT69_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_30_2 i) (Q2.hfix69_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨69, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T69_30 = colFn colCertDiv_69_30_5.D1 (m := 5) from colCertDiv_69_30_5.bind1,
    show colData2 (⟨69, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 5 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T69_30_2 = colFn colCertDiv_69_30_5.D2 (m := 5) from colCertDiv_69_30_5.bind2]
  rw [alnId_69 j hj]
  exact fastcode_of_div ⟨69, by decide⟩ _ _ _
    ((alnId_69 j hj) ▸ Q2.listedAt (⟨69, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨69, by decide⟩ : Fin 148) hj hq).1) colCertDiv_69_30_5_match


theorem leaf_69_30_10 (hp : 10 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 10 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨69, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp)) T69_30
      hfix69_30 hinj69_30 hcardT69_30
      (fun i => conj_mem_of_fixedPoints _ _ (T69_30 i) (hfix69_30 i) _)
      ⟨69, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 10 hp) Q2.T69_30_2 Q2.hfix69_30_2 Q2.hinj69_30_2
      Q2.hcardT69_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_30_2 i) (Q2.hfix69_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨69, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T69_30 = colFn colCertDiv_69_30_10.D1 (m := 5) from colCertDiv_69_30_10.bind1,
    show colData2 (⟨69, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 10 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T69_30_2 = colFn colCertDiv_69_30_10.D2 (m := 5) from colCertDiv_69_30_10.bind2]
  rw [alnId_69 j hj]
  exact fastcode_of_div ⟨69, by decide⟩ _ _ _
    ((alnId_69 j hj) ▸ Q2.listedAt (⟨69, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨69, by decide⟩ : Fin 148) hj hq).1) colCertDiv_69_30_10_match


theorem leaf_69_30_15 (hp : 15 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 15 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨69, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp)) T69_30
      hfix69_30 hinj69_30 hcardT69_30
      (fun i => conj_mem_of_fixedPoints _ _ (T69_30 i) (hfix69_30 i) _)
      ⟨69, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 15 hp) Q2.T69_30_2 Q2.hfix69_30_2 Q2.hinj69_30_2
      Q2.hcardT69_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_30_2 i) (Q2.hfix69_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨69, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T69_30 = colFn colCertDiv_69_30_15.D1 (m := 5) from colCertDiv_69_30_15.bind1,
    show colData2 (⟨69, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 15 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T69_30_2 = colFn colCertDiv_69_30_15.D2 (m := 5) from colCertDiv_69_30_15.bind2]
  rw [alnId_69 j hj]
  exact fastcode_of_div ⟨69, by decide⟩ _ _ _
    ((alnId_69 j hj) ▸ Q2.listedAt (⟨69, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨69, by decide⟩ : Fin 148) hj hq).1) colCertDiv_69_30_15_match


theorem leaf_69_30_20 (hp : 20 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 20 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨69, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp)) T69_30
      hfix69_30 hinj69_30 hcardT69_30
      (fun i => conj_mem_of_fixedPoints _ _ (T69_30 i) (hfix69_30 i) _)
      ⟨69, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 20 hp) Q2.T69_30_2 Q2.hfix69_30_2 Q2.hinj69_30_2
      Q2.hcardT69_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_30_2 i) (Q2.hfix69_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨69, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T69_30 = colFn colCertDiv_69_30_20.D1 (m := 5) from colCertDiv_69_30_20.bind1,
    show colData2 (⟨69, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 20 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T69_30_2 = colFn colCertDiv_69_30_20.D2 (m := 5) from colCertDiv_69_30_20.bind2]
  rw [alnId_69 j hj]
  exact fastcode_of_div ⟨69, by decide⟩ _ _ _
    ((alnId_69 j hj) ▸ Q2.listedAt (⟨69, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨69, by decide⟩ : Fin 148) hj hq).1) colCertDiv_69_30_20_match


theorem leaf_69_35_0 (hp : 0 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 0 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp)) T69_35
      hfix69_35 hinj69_35 hcardT69_35
      (fun i => conj_mem_of_fixedPoints _ _ (T69_35 i) (hfix69_35 i) _)
      ⟨69, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 0 hp) Q2.T69_35_2 Q2.hfix69_35_2 Q2.hinj69_35_2
      Q2.hcardT69_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_35_2 i) (Q2.hfix69_35_2 i) _)
      colCert_69_35_0.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_35_1 (hp : 1 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 1 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp)) T69_35
      hfix69_35 hinj69_35 hcardT69_35
      (fun i => conj_mem_of_fixedPoints _ _ (T69_35 i) (hfix69_35 i) _)
      ⟨69, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 1 hp) Q2.T69_35_2 Q2.hfix69_35_2 Q2.hinj69_35_2
      Q2.hcardT69_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_35_2 i) (Q2.hfix69_35_2 i) _)
      colCert_69_35_1.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_35_2 (hp : 2 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 2 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp)) T69_35
      hfix69_35 hinj69_35 hcardT69_35
      (fun i => conj_mem_of_fixedPoints _ _ (T69_35 i) (hfix69_35 i) _)
      ⟨69, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 2 hp) Q2.T69_35_2 Q2.hfix69_35_2 Q2.hinj69_35_2
      Q2.hcardT69_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_35_2 i) (Q2.hfix69_35_2 i) _)
      colCert_69_35_2.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_35_3 (hp : 3 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 3 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp)) T69_35
      hfix69_35 hinj69_35 hcardT69_35
      (fun i => conj_mem_of_fixedPoints _ _ (T69_35 i) (hfix69_35 i) _)
      ⟨69, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 3 hp) Q2.T69_35_2 Q2.hfix69_35_2 Q2.hinj69_35_2
      Q2.hcardT69_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_35_2 i) (Q2.hfix69_35_2 i) _)
      colCert_69_35_3.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_35_4 (hp : 4 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 4 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp)) T69_35
      hfix69_35 hinj69_35 hcardT69_35
      (fun i => conj_mem_of_fixedPoints _ _ (T69_35 i) (hfix69_35 i) _)
      ⟨69, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 4 hp) Q2.T69_35_2 Q2.hfix69_35_2 Q2.hinj69_35_2
      Q2.hcardT69_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_35_2 i) (Q2.hfix69_35_2 i) _)
      colCert_69_35_4.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_35_5 (hp : 5 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 5 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨69, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp)) T69_35
      hfix69_35 hinj69_35 hcardT69_35
      (fun i => conj_mem_of_fixedPoints _ _ (T69_35 i) (hfix69_35 i) _)
      ⟨69, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 5 hp) Q2.T69_35_2 Q2.hfix69_35_2 Q2.hinj69_35_2
      Q2.hcardT69_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_35_2 i) (Q2.hfix69_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨69, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T69_35 = colFn colCertDiv_69_35_5.D1 (m := 5) from colCertDiv_69_35_5.bind1,
    show colData2 (⟨69, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 5 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T69_35_2 = colFn colCertDiv_69_35_5.D2 (m := 5) from colCertDiv_69_35_5.bind2]
  rw [alnId_69 j hj]
  exact fastcode_of_div ⟨69, by decide⟩ _ _ _
    ((alnId_69 j hj) ▸ Q2.listedAt (⟨69, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨69, by decide⟩ : Fin 148) hj hq).1) colCertDiv_69_35_5_match


theorem leaf_69_35_10 (hp : 10 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 10 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨69, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp)) T69_35
      hfix69_35 hinj69_35 hcardT69_35
      (fun i => conj_mem_of_fixedPoints _ _ (T69_35 i) (hfix69_35 i) _)
      ⟨69, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 10 hp) Q2.T69_35_2 Q2.hfix69_35_2 Q2.hinj69_35_2
      Q2.hcardT69_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_35_2 i) (Q2.hfix69_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨69, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T69_35 = colFn colCertDiv_69_35_10.D1 (m := 5) from colCertDiv_69_35_10.bind1,
    show colData2 (⟨69, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 10 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T69_35_2 = colFn colCertDiv_69_35_10.D2 (m := 5) from colCertDiv_69_35_10.bind2]
  rw [alnId_69 j hj]
  exact fastcode_of_div ⟨69, by decide⟩ _ _ _
    ((alnId_69 j hj) ▸ Q2.listedAt (⟨69, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨69, by decide⟩ : Fin 148) hj hq).1) colCertDiv_69_35_10_match


theorem leaf_69_35_15 (hp : 15 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 15 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨69, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp)) T69_35
      hfix69_35 hinj69_35 hcardT69_35
      (fun i => conj_mem_of_fixedPoints _ _ (T69_35 i) (hfix69_35 i) _)
      ⟨69, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 15 hp) Q2.T69_35_2 Q2.hfix69_35_2 Q2.hinj69_35_2
      Q2.hcardT69_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_35_2 i) (Q2.hfix69_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨69, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T69_35 = colFn colCertDiv_69_35_15.D1 (m := 5) from colCertDiv_69_35_15.bind1,
    show colData2 (⟨69, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 15 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T69_35_2 = colFn colCertDiv_69_35_15.D2 (m := 5) from colCertDiv_69_35_15.bind2]
  rw [alnId_69 j hj]
  exact fastcode_of_div ⟨69, by decide⟩ _ _ _
    ((alnId_69 j hj) ▸ Q2.listedAt (⟨69, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨69, by decide⟩ : Fin 148) hj hq).1) colCertDiv_69_35_15_match


theorem leaf_69_35_20 (hp : 20 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 20 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨69, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp)) T69_35
      hfix69_35 hinj69_35 hcardT69_35
      (fun i => conj_mem_of_fixedPoints _ _ (T69_35 i) (hfix69_35 i) _)
      ⟨69, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 20 hp) Q2.T69_35_2 Q2.hfix69_35_2 Q2.hinj69_35_2
      Q2.hcardT69_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_35_2 i) (Q2.hfix69_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨69, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T69_35 = colFn colCertDiv_69_35_20.D1 (m := 5) from colCertDiv_69_35_20.bind1,
    show colData2 (⟨69, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 20 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T69_35_2 = colFn colCertDiv_69_35_20.D2 (m := 5) from colCertDiv_69_35_20.bind2]
  rw [alnId_69 j hj]
  exact fastcode_of_div ⟨69, by decide⟩ _ _ _
    ((alnId_69 j hj) ▸ Q2.listedAt (⟨69, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨69, by decide⟩ : Fin 148) hj hq).1) colCertDiv_69_35_20_match


theorem leaf_69_40_0 (hp : 0 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 0 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp)) T69_40
      hfix69_40 hinj69_40 hcardT69_40
      (fun i => conj_mem_of_fixedPoints _ _ (T69_40 i) (hfix69_40 i) _)
      ⟨69, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 0 hp) Q2.T69_40_2 Q2.hfix69_40_2 Q2.hinj69_40_2
      Q2.hcardT69_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_40_2 i) (Q2.hfix69_40_2 i) _)
      colCert_69_40_0.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_40_1 (hp : 1 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 1 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp)) T69_40
      hfix69_40 hinj69_40 hcardT69_40
      (fun i => conj_mem_of_fixedPoints _ _ (T69_40 i) (hfix69_40 i) _)
      ⟨69, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 1 hp) Q2.T69_40_2 Q2.hfix69_40_2 Q2.hinj69_40_2
      Q2.hcardT69_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_40_2 i) (Q2.hfix69_40_2 i) _)
      colCert_69_40_1.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_40_2 (hp : 2 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 2 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp)) T69_40
      hfix69_40 hinj69_40 hcardT69_40
      (fun i => conj_mem_of_fixedPoints _ _ (T69_40 i) (hfix69_40 i) _)
      ⟨69, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 2 hp) Q2.T69_40_2 Q2.hfix69_40_2 Q2.hinj69_40_2
      Q2.hcardT69_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_40_2 i) (Q2.hfix69_40_2 i) _)
      colCert_69_40_2.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_40_3 (hp : 3 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 3 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp)) T69_40
      hfix69_40 hinj69_40 hcardT69_40
      (fun i => conj_mem_of_fixedPoints _ _ (T69_40 i) (hfix69_40 i) _)
      ⟨69, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 3 hp) Q2.T69_40_2 Q2.hfix69_40_2 Q2.hinj69_40_2
      Q2.hcardT69_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_40_2 i) (Q2.hfix69_40_2 i) _)
      colCert_69_40_3.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_40_4 (hp : 4 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 4 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp)) T69_40
      hfix69_40 hinj69_40 hcardT69_40
      (fun i => conj_mem_of_fixedPoints _ _ (T69_40 i) (hfix69_40 i) _)
      ⟨69, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 4 hp) Q2.T69_40_2 Q2.hfix69_40_2 Q2.hinj69_40_2
      Q2.hcardT69_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_40_2 i) (Q2.hfix69_40_2 i) _)
      colCert_69_40_4.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_40_5 (hp : 5 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 5 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨69, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp)) T69_40
      hfix69_40 hinj69_40 hcardT69_40
      (fun i => conj_mem_of_fixedPoints _ _ (T69_40 i) (hfix69_40 i) _)
      ⟨69, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 5 hp) Q2.T69_40_2 Q2.hfix69_40_2 Q2.hinj69_40_2
      Q2.hcardT69_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_40_2 i) (Q2.hfix69_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨69, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T69_40 = colFn colCertDiv_69_40_5.D1 (m := 5) from colCertDiv_69_40_5.bind1,
    show colData2 (⟨69, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 5 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T69_40_2 = colFn colCertDiv_69_40_5.D2 (m := 5) from colCertDiv_69_40_5.bind2]
  rw [alnId_69 j hj]
  exact fastcode_of_div ⟨69, by decide⟩ _ _ _
    ((alnId_69 j hj) ▸ Q2.listedAt (⟨69, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨69, by decide⟩ : Fin 148) hj hq).1) colCertDiv_69_40_5_match


theorem leaf_69_40_10 (hp : 10 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 10 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨69, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp)) T69_40
      hfix69_40 hinj69_40 hcardT69_40
      (fun i => conj_mem_of_fixedPoints _ _ (T69_40 i) (hfix69_40 i) _)
      ⟨69, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 10 hp) Q2.T69_40_2 Q2.hfix69_40_2 Q2.hinj69_40_2
      Q2.hcardT69_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_40_2 i) (Q2.hfix69_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨69, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T69_40 = colFn colCertDiv_69_40_10.D1 (m := 5) from colCertDiv_69_40_10.bind1,
    show colData2 (⟨69, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 10 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T69_40_2 = colFn colCertDiv_69_40_10.D2 (m := 5) from colCertDiv_69_40_10.bind2]
  rw [alnId_69 j hj]
  exact fastcode_of_div ⟨69, by decide⟩ _ _ _
    ((alnId_69 j hj) ▸ Q2.listedAt (⟨69, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨69, by decide⟩ : Fin 148) hj hq).1) colCertDiv_69_40_10_match


theorem leaf_69_40_15 (hp : 15 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 15 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨69, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp)) T69_40
      hfix69_40 hinj69_40 hcardT69_40
      (fun i => conj_mem_of_fixedPoints _ _ (T69_40 i) (hfix69_40 i) _)
      ⟨69, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 15 hp) Q2.T69_40_2 Q2.hfix69_40_2 Q2.hinj69_40_2
      Q2.hcardT69_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_40_2 i) (Q2.hfix69_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨69, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T69_40 = colFn colCertDiv_69_40_15.D1 (m := 5) from colCertDiv_69_40_15.bind1,
    show colData2 (⟨69, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 15 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T69_40_2 = colFn colCertDiv_69_40_15.D2 (m := 5) from colCertDiv_69_40_15.bind2]
  rw [alnId_69 j hj]
  exact fastcode_of_div ⟨69, by decide⟩ _ _ _
    ((alnId_69 j hj) ▸ Q2.listedAt (⟨69, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨69, by decide⟩ : Fin 148) hj hq).1) colCertDiv_69_40_15_match


theorem leaf_69_40_20 (hp : 20 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 20 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨69, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp)) T69_40
      hfix69_40 hinj69_40 hcardT69_40
      (fun i => conj_mem_of_fixedPoints _ _ (T69_40 i) (hfix69_40 i) _)
      ⟨69, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 20 hp) Q2.T69_40_2 Q2.hfix69_40_2 Q2.hinj69_40_2
      Q2.hcardT69_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_40_2 i) (Q2.hfix69_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨69, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T69_40 = colFn colCertDiv_69_40_20.D1 (m := 5) from colCertDiv_69_40_20.bind1,
    show colData2 (⟨69, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 20 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T69_40_2 = colFn colCertDiv_69_40_20.D2 (m := 5) from colCertDiv_69_40_20.bind2]
  rw [alnId_69 j hj]
  exact fastcode_of_div ⟨69, by decide⟩ _ _ _
    ((alnId_69 j hj) ▸ Q2.listedAt (⟨69, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨69, by decide⟩ : Fin 148) hj hq).1) colCertDiv_69_40_20_match


theorem leaf_69_45_0 (hp : 0 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 0 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp)) T69_45
      hfix69_45 hinj69_45 hcardT69_45
      (fun i => conj_mem_of_fixedPoints _ _ (T69_45 i) (hfix69_45 i) _)
      ⟨69, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 0 hp) Q2.T69_45_2 Q2.hfix69_45_2 Q2.hinj69_45_2
      Q2.hcardT69_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_45_2 i) (Q2.hfix69_45_2 i) _)
      colCert_69_45_0.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_45_1 (hp : 1 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 1 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp)) T69_45
      hfix69_45 hinj69_45 hcardT69_45
      (fun i => conj_mem_of_fixedPoints _ _ (T69_45 i) (hfix69_45 i) _)
      ⟨69, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 1 hp) Q2.T69_45_2 Q2.hfix69_45_2 Q2.hinj69_45_2
      Q2.hcardT69_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_45_2 i) (Q2.hfix69_45_2 i) _)
      colCert_69_45_1.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_45_2 (hp : 2 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 2 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp)) T69_45
      hfix69_45 hinj69_45 hcardT69_45
      (fun i => conj_mem_of_fixedPoints _ _ (T69_45 i) (hfix69_45 i) _)
      ⟨69, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 2 hp) Q2.T69_45_2 Q2.hfix69_45_2 Q2.hinj69_45_2
      Q2.hcardT69_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_45_2 i) (Q2.hfix69_45_2 i) _)
      colCert_69_45_2.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_45_3 (hp : 3 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 3 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp)) T69_45
      hfix69_45 hinj69_45 hcardT69_45
      (fun i => conj_mem_of_fixedPoints _ _ (T69_45 i) (hfix69_45 i) _)
      ⟨69, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 3 hp) Q2.T69_45_2 Q2.hfix69_45_2 Q2.hinj69_45_2
      Q2.hcardT69_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_45_2 i) (Q2.hfix69_45_2 i) _)
      colCert_69_45_3.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_45_4 (hp : 4 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 4 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp)) T69_45
      hfix69_45 hinj69_45 hcardT69_45
      (fun i => conj_mem_of_fixedPoints _ _ (T69_45 i) (hfix69_45 i) _)
      ⟨69, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 4 hp) Q2.T69_45_2 Q2.hfix69_45_2 Q2.hinj69_45_2
      Q2.hcardT69_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_45_2 i) (Q2.hfix69_45_2 i) _)
      colCert_69_45_4.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_45_5 (hp : 5 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 5 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨69, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp)) T69_45
      hfix69_45 hinj69_45 hcardT69_45
      (fun i => conj_mem_of_fixedPoints _ _ (T69_45 i) (hfix69_45 i) _)
      ⟨69, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 5 hp) Q2.T69_45_2 Q2.hfix69_45_2 Q2.hinj69_45_2
      Q2.hcardT69_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_45_2 i) (Q2.hfix69_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨69, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T69_45 = colFn colCertDiv_69_45_5.D1 (m := 5) from colCertDiv_69_45_5.bind1,
    show colData2 (⟨69, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 5 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T69_45_2 = colFn colCertDiv_69_45_5.D2 (m := 5) from colCertDiv_69_45_5.bind2]
  rw [alnId_69 j hj]
  exact fastcode_of_div ⟨69, by decide⟩ _ _ _
    ((alnId_69 j hj) ▸ Q2.listedAt (⟨69, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨69, by decide⟩ : Fin 148) hj hq).1) colCertDiv_69_45_5_match


theorem leaf_69_45_10 (hp : 10 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 10 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨69, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp)) T69_45
      hfix69_45 hinj69_45 hcardT69_45
      (fun i => conj_mem_of_fixedPoints _ _ (T69_45 i) (hfix69_45 i) _)
      ⟨69, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 10 hp) Q2.T69_45_2 Q2.hfix69_45_2 Q2.hinj69_45_2
      Q2.hcardT69_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_45_2 i) (Q2.hfix69_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨69, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T69_45 = colFn colCertDiv_69_45_10.D1 (m := 5) from colCertDiv_69_45_10.bind1,
    show colData2 (⟨69, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 10 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T69_45_2 = colFn colCertDiv_69_45_10.D2 (m := 5) from colCertDiv_69_45_10.bind2]
  rw [alnId_69 j hj]
  exact fastcode_of_div ⟨69, by decide⟩ _ _ _
    ((alnId_69 j hj) ▸ Q2.listedAt (⟨69, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨69, by decide⟩ : Fin 148) hj hq).1) colCertDiv_69_45_10_match


theorem leaf_69_45_15 (hp : 15 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 15 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨69, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp)) T69_45
      hfix69_45 hinj69_45 hcardT69_45
      (fun i => conj_mem_of_fixedPoints _ _ (T69_45 i) (hfix69_45 i) _)
      ⟨69, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 15 hp) Q2.T69_45_2 Q2.hfix69_45_2 Q2.hinj69_45_2
      Q2.hcardT69_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_45_2 i) (Q2.hfix69_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨69, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T69_45 = colFn colCertDiv_69_45_15.D1 (m := 5) from colCertDiv_69_45_15.bind1,
    show colData2 (⟨69, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 15 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T69_45_2 = colFn colCertDiv_69_45_15.D2 (m := 5) from colCertDiv_69_45_15.bind2]
  rw [alnId_69 j hj]
  exact fastcode_of_div ⟨69, by decide⟩ _ _ _
    ((alnId_69 j hj) ▸ Q2.listedAt (⟨69, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨69, by decide⟩ : Fin 148) hj hq).1) colCertDiv_69_45_15_match


theorem leaf_69_45_20 (hp : 20 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 20 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨69, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp)) T69_45
      hfix69_45 hinj69_45 hcardT69_45
      (fun i => conj_mem_of_fixedPoints _ _ (T69_45 i) (hfix69_45 i) _)
      ⟨69, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 20 hp) Q2.T69_45_2 Q2.hfix69_45_2 Q2.hinj69_45_2
      Q2.hcardT69_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_45_2 i) (Q2.hfix69_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨69, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T69_45 = colFn colCertDiv_69_45_20.D1 (m := 5) from colCertDiv_69_45_20.bind1,
    show colData2 (⟨69, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 20 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T69_45_2 = colFn colCertDiv_69_45_20.D2 (m := 5) from colCertDiv_69_45_20.bind2]
  rw [alnId_69 j hj]
  exact fastcode_of_div ⟨69, by decide⟩ _ _ _
    ((alnId_69 j hj) ▸ Q2.listedAt (⟨69, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨69, by decide⟩ : Fin 148) hj hq).1) colCertDiv_69_45_20_match


theorem leaf_69_50_0 (hp : 0 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 0 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp)) T69_50
      hfix69_50 hinj69_50 hcardT69_50
      (fun i => conj_mem_of_fixedPoints _ _ (T69_50 i) (hfix69_50 i) _)
      ⟨69, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 0 hp) Q2.T69_50_2 Q2.hfix69_50_2 Q2.hinj69_50_2
      Q2.hcardT69_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_50_2 i) (Q2.hfix69_50_2 i) _)
      colCert_69_50_0.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_50_1 (hp : 1 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 1 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp)) T69_50
      hfix69_50 hinj69_50 hcardT69_50
      (fun i => conj_mem_of_fixedPoints _ _ (T69_50 i) (hfix69_50 i) _)
      ⟨69, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 1 hp) Q2.T69_50_2 Q2.hfix69_50_2 Q2.hinj69_50_2
      Q2.hcardT69_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_50_2 i) (Q2.hfix69_50_2 i) _)
      colCert_69_50_1.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_50_2 (hp : 2 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 2 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp)) T69_50
      hfix69_50 hinj69_50 hcardT69_50
      (fun i => conj_mem_of_fixedPoints _ _ (T69_50 i) (hfix69_50 i) _)
      ⟨69, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 2 hp) Q2.T69_50_2 Q2.hfix69_50_2 Q2.hinj69_50_2
      Q2.hcardT69_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_50_2 i) (Q2.hfix69_50_2 i) _)
      colCert_69_50_2.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_50_3 (hp : 3 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 3 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp)) T69_50
      hfix69_50 hinj69_50 hcardT69_50
      (fun i => conj_mem_of_fixedPoints _ _ (T69_50 i) (hfix69_50 i) _)
      ⟨69, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 3 hp) Q2.T69_50_2 Q2.hfix69_50_2 Q2.hinj69_50_2
      Q2.hcardT69_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_50_2 i) (Q2.hfix69_50_2 i) _)
      colCert_69_50_3.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_50_4 (hp : 4 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 4 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp)) T69_50
      hfix69_50 hinj69_50 hcardT69_50
      (fun i => conj_mem_of_fixedPoints _ _ (T69_50 i) (hfix69_50 i) _)
      ⟨69, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 4 hp) Q2.T69_50_2 Q2.hfix69_50_2 Q2.hinj69_50_2
      Q2.hcardT69_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_50_2 i) (Q2.hfix69_50_2 i) _)
      colCert_69_50_4.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_50_5 (hp : 5 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 5 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨69, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp)) T69_50
      hfix69_50 hinj69_50 hcardT69_50
      (fun i => conj_mem_of_fixedPoints _ _ (T69_50 i) (hfix69_50 i) _)
      ⟨69, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 5 hp) Q2.T69_50_2 Q2.hfix69_50_2 Q2.hinj69_50_2
      Q2.hcardT69_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_50_2 i) (Q2.hfix69_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨69, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T69_50 = colFn colCertDiv_69_50_5.D1 (m := 5) from colCertDiv_69_50_5.bind1,
    show colData2 (⟨69, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 5 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T69_50_2 = colFn colCertDiv_69_50_5.D2 (m := 5) from colCertDiv_69_50_5.bind2]
  rw [alnId_69 j hj]
  exact fastcode_of_div ⟨69, by decide⟩ _ _ _
    ((alnId_69 j hj) ▸ Q2.listedAt (⟨69, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨69, by decide⟩ : Fin 148) hj hq).1) colCertDiv_69_50_5_match


theorem leaf_69_50_10 (hp : 10 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 10 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨69, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp)) T69_50
      hfix69_50 hinj69_50 hcardT69_50
      (fun i => conj_mem_of_fixedPoints _ _ (T69_50 i) (hfix69_50 i) _)
      ⟨69, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 10 hp) Q2.T69_50_2 Q2.hfix69_50_2 Q2.hinj69_50_2
      Q2.hcardT69_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_50_2 i) (Q2.hfix69_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨69, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T69_50 = colFn colCertDiv_69_50_10.D1 (m := 5) from colCertDiv_69_50_10.bind1,
    show colData2 (⟨69, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 10 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T69_50_2 = colFn colCertDiv_69_50_10.D2 (m := 5) from colCertDiv_69_50_10.bind2]
  rw [alnId_69 j hj]
  exact fastcode_of_div ⟨69, by decide⟩ _ _ _
    ((alnId_69 j hj) ▸ Q2.listedAt (⟨69, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨69, by decide⟩ : Fin 148) hj hq).1) colCertDiv_69_50_10_match


theorem leaf_69_50_15 (hp : 15 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 15 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨69, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp)) T69_50
      hfix69_50 hinj69_50 hcardT69_50
      (fun i => conj_mem_of_fixedPoints _ _ (T69_50 i) (hfix69_50 i) _)
      ⟨69, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 15 hp) Q2.T69_50_2 Q2.hfix69_50_2 Q2.hinj69_50_2
      Q2.hcardT69_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_50_2 i) (Q2.hfix69_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨69, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T69_50 = colFn colCertDiv_69_50_15.D1 (m := 5) from colCertDiv_69_50_15.bind1,
    show colData2 (⟨69, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 15 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T69_50_2 = colFn colCertDiv_69_50_15.D2 (m := 5) from colCertDiv_69_50_15.bind2]
  rw [alnId_69 j hj]
  exact fastcode_of_div ⟨69, by decide⟩ _ _ _
    ((alnId_69 j hj) ▸ Q2.listedAt (⟨69, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨69, by decide⟩ : Fin 148) hj hq).1) colCertDiv_69_50_15_match


theorem leaf_69_50_20 (hp : 20 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 20 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨69, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp)) T69_50
      hfix69_50 hinj69_50 hcardT69_50
      (fun i => conj_mem_of_fixedPoints _ _ (T69_50 i) (hfix69_50 i) _)
      ⟨69, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 20 hp) Q2.T69_50_2 Q2.hfix69_50_2 Q2.hinj69_50_2
      Q2.hcardT69_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_50_2 i) (Q2.hfix69_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨69, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T69_50 = colFn colCertDiv_69_50_20.D1 (m := 5) from colCertDiv_69_50_20.bind1,
    show colData2 (⟨69, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 20 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T69_50_2 = colFn colCertDiv_69_50_20.D2 (m := 5) from colCertDiv_69_50_20.bind2]
  rw [alnId_69 j hj]
  exact fastcode_of_div ⟨69, by decide⟩ _ _ _
    ((alnId_69 j hj) ▸ Q2.listedAt (⟨69, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨69, by decide⟩ : Fin 148) hj hq).1) colCertDiv_69_50_20_match


theorem leaf_69_69_0 (hp : 0 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 0 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 0 (transLenTr ⟨69, by decide⟩ 0 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 0 (transLenTr ⟨69, by decide⟩ 0 hp)) T69_69
      hfix69_69 hinj69_69 hcardT69_69
      (fun i => conj_mem_of_fixedPoints _ _ (T69_69 i) (hfix69_69 i) _)
      ⟨69, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 0 hp) Q2.T69_69_2 Q2.hfix69_69_2 Q2.hinj69_69_2
      Q2.hcardT69_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_69_2 i) (Q2.hfix69_69_2 i) _)
      colCert_69_69_0.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_69_1 (hp : 1 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 1 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 1 (transLenTr ⟨69, by decide⟩ 1 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 1 (transLenTr ⟨69, by decide⟩ 1 hp)) T69_69
      hfix69_69 hinj69_69 hcardT69_69
      (fun i => conj_mem_of_fixedPoints _ _ (T69_69 i) (hfix69_69 i) _)
      ⟨69, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 1 hp) Q2.T69_69_2 Q2.hfix69_69_2 Q2.hinj69_69_2
      Q2.hcardT69_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_69_2 i) (Q2.hfix69_69_2 i) _)
      colCert_69_69_1.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_69_2 (hp : 2 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 2 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 2 (transLenTr ⟨69, by decide⟩ 2 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 2 (transLenTr ⟨69, by decide⟩ 2 hp)) T69_69
      hfix69_69 hinj69_69 hcardT69_69
      (fun i => conj_mem_of_fixedPoints _ _ (T69_69 i) (hfix69_69 i) _)
      ⟨69, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 2 hp) Q2.T69_69_2 Q2.hfix69_69_2 Q2.hinj69_69_2
      Q2.hcardT69_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_69_2 i) (Q2.hfix69_69_2 i) _)
      colCert_69_69_2.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_69_3 (hp : 3 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 3 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 3 (transLenTr ⟨69, by decide⟩ 3 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 3 (transLenTr ⟨69, by decide⟩ 3 hp)) T69_69
      hfix69_69 hinj69_69 hcardT69_69
      (fun i => conj_mem_of_fixedPoints _ _ (T69_69 i) (hfix69_69 i) _)
      ⟨69, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 3 hp) Q2.T69_69_2 Q2.hfix69_69_2 Q2.hinj69_69_2
      Q2.hcardT69_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_69_2 i) (Q2.hfix69_69_2 i) _)
      colCert_69_69_3.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_69_4 (hp : 4 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 4 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 4 (transLenTr ⟨69, by decide⟩ 4 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 4 (transLenTr ⟨69, by decide⟩ 4 hp)) T69_69
      hfix69_69 hinj69_69 hcardT69_69
      (fun i => conj_mem_of_fixedPoints _ _ (T69_69 i) (hfix69_69 i) _)
      ⟨69, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 4 hp) Q2.T69_69_2 Q2.hfix69_69_2 Q2.hinj69_69_2
      Q2.hcardT69_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_69_2 i) (Q2.hfix69_69_2 i) _)
      colCert_69_69_4.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_69_5 (hp : 5 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 5 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 5 (transLenTr ⟨69, by decide⟩ 5 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 5 (transLenTr ⟨69, by decide⟩ 5 hp)) T69_69
      hfix69_69 hinj69_69 hcardT69_69
      (fun i => conj_mem_of_fixedPoints _ _ (T69_69 i) (hfix69_69 i) _)
      ⟨69, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 5 hp) Q2.T69_69_2 Q2.hfix69_69_2 Q2.hinj69_69_2
      Q2.hcardT69_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_69_2 i) (Q2.hfix69_69_2 i) _)
      colCert_69_69_5.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_69_6 (hp : 6 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 6 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 6 (transLenTr ⟨69, by decide⟩ 6 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 6 (transLenTr ⟨69, by decide⟩ 6 hp)) T69_69
      hfix69_69 hinj69_69 hcardT69_69
      (fun i => conj_mem_of_fixedPoints _ _ (T69_69 i) (hfix69_69 i) _)
      ⟨69, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 6 hp) Q2.T69_69_2 Q2.hfix69_69_2 Q2.hinj69_69_2
      Q2.hcardT69_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_69_2 i) (Q2.hfix69_69_2 i) _)
      colCert_69_69_6.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_69_7 (hp : 7 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 7 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 7 (transLenTr ⟨69, by decide⟩ 7 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 7 (transLenTr ⟨69, by decide⟩ 7 hp)) T69_69
      hfix69_69 hinj69_69 hcardT69_69
      (fun i => conj_mem_of_fixedPoints _ _ (T69_69 i) (hfix69_69 i) _)
      ⟨69, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 7 hp) Q2.T69_69_2 Q2.hfix69_69_2 Q2.hinj69_69_2
      Q2.hcardT69_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_69_2 i) (Q2.hfix69_69_2 i) _)
      colCert_69_69_7.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_69_8 (hp : 8 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 8 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 8 (transLenTr ⟨69, by decide⟩ 8 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 8 (transLenTr ⟨69, by decide⟩ 8 hp)) T69_69
      hfix69_69 hinj69_69 hcardT69_69
      (fun i => conj_mem_of_fixedPoints _ _ (T69_69 i) (hfix69_69 i) _)
      ⟨69, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 8 hp) Q2.T69_69_2 Q2.hfix69_69_2 Q2.hinj69_69_2
      Q2.hcardT69_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_69_2 i) (Q2.hfix69_69_2 i) _)
      colCert_69_69_8.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_69_9 (hp : 9 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 9 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 9 (transLenTr ⟨69, by decide⟩ 9 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 9 (transLenTr ⟨69, by decide⟩ 9 hp)) T69_69
      hfix69_69 hinj69_69 hcardT69_69
      (fun i => conj_mem_of_fixedPoints _ _ (T69_69 i) (hfix69_69 i) _)
      ⟨69, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 9 hp) Q2.T69_69_2 Q2.hfix69_69_2 Q2.hinj69_69_2
      Q2.hcardT69_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_69_2 i) (Q2.hfix69_69_2 i) _)
      colCert_69_69_9.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_69_10 (hp : 10 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 10 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 10 (transLenTr ⟨69, by decide⟩ 10 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 10 (transLenTr ⟨69, by decide⟩ 10 hp)) T69_69
      hfix69_69 hinj69_69 hcardT69_69
      (fun i => conj_mem_of_fixedPoints _ _ (T69_69 i) (hfix69_69 i) _)
      ⟨69, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 10 hp) Q2.T69_69_2 Q2.hfix69_69_2 Q2.hinj69_69_2
      Q2.hcardT69_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_69_2 i) (Q2.hfix69_69_2 i) _)
      colCert_69_69_10.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_69_11 (hp : 11 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 11 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 11 (transLenTr ⟨69, by decide⟩ 11 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 11 (transLenTr ⟨69, by decide⟩ 11 hp)) T69_69
      hfix69_69 hinj69_69 hcardT69_69
      (fun i => conj_mem_of_fixedPoints _ _ (T69_69 i) (hfix69_69 i) _)
      ⟨69, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 11 hp) Q2.T69_69_2 Q2.hfix69_69_2 Q2.hinj69_69_2
      Q2.hcardT69_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_69_2 i) (Q2.hfix69_69_2 i) _)
      colCert_69_69_11.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_69_12 (hp : 12 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 12 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 12 (transLenTr ⟨69, by decide⟩ 12 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 12 (transLenTr ⟨69, by decide⟩ 12 hp)) T69_69
      hfix69_69 hinj69_69 hcardT69_69
      (fun i => conj_mem_of_fixedPoints _ _ (T69_69 i) (hfix69_69 i) _)
      ⟨69, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 12 hp) Q2.T69_69_2 Q2.hfix69_69_2 Q2.hinj69_69_2
      Q2.hcardT69_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_69_2 i) (Q2.hfix69_69_2 i) _)
      colCert_69_69_12.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_69_13 (hp : 13 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 13 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 13 (transLenTr ⟨69, by decide⟩ 13 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 13 (transLenTr ⟨69, by decide⟩ 13 hp)) T69_69
      hfix69_69 hinj69_69 hcardT69_69
      (fun i => conj_mem_of_fixedPoints _ _ (T69_69 i) (hfix69_69 i) _)
      ⟨69, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 13 hp) Q2.T69_69_2 Q2.hfix69_69_2 Q2.hinj69_69_2
      Q2.hcardT69_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_69_2 i) (Q2.hfix69_69_2 i) _)
      colCert_69_69_13.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_69_14 (hp : 14 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 14 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 14 (transLenTr ⟨69, by decide⟩ 14 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 14 (transLenTr ⟨69, by decide⟩ 14 hp)) T69_69
      hfix69_69 hinj69_69 hcardT69_69
      (fun i => conj_mem_of_fixedPoints _ _ (T69_69 i) (hfix69_69 i) _)
      ⟨69, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 14 hp) Q2.T69_69_2 Q2.hfix69_69_2 Q2.hinj69_69_2
      Q2.hcardT69_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_69_2 i) (Q2.hfix69_69_2 i) _)
      colCert_69_69_14.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_69_15 (hp : 15 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 15 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 15 (transLenTr ⟨69, by decide⟩ 15 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 15 (transLenTr ⟨69, by decide⟩ 15 hp)) T69_69
      hfix69_69 hinj69_69 hcardT69_69
      (fun i => conj_mem_of_fixedPoints _ _ (T69_69 i) (hfix69_69 i) _)
      ⟨69, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 15 hp) Q2.T69_69_2 Q2.hfix69_69_2 Q2.hinj69_69_2
      Q2.hcardT69_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_69_2 i) (Q2.hfix69_69_2 i) _)
      colCert_69_69_15.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_69_16 (hp : 16 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 16 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 16 (transLenTr ⟨69, by decide⟩ 16 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 16 (transLenTr ⟨69, by decide⟩ 16 hp)) T69_69
      hfix69_69 hinj69_69 hcardT69_69
      (fun i => conj_mem_of_fixedPoints _ _ (T69_69 i) (hfix69_69 i) _)
      ⟨69, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 16 hp) Q2.T69_69_2 Q2.hfix69_69_2 Q2.hinj69_69_2
      Q2.hcardT69_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_69_2 i) (Q2.hfix69_69_2 i) _)
      colCert_69_69_16.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_69_17 (hp : 17 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 17 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 17 (transLenTr ⟨69, by decide⟩ 17 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 17 (transLenTr ⟨69, by decide⟩ 17 hp)) T69_69
      hfix69_69 hinj69_69 hcardT69_69
      (fun i => conj_mem_of_fixedPoints _ _ (T69_69 i) (hfix69_69 i) _)
      ⟨69, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 17 hp) Q2.T69_69_2 Q2.hfix69_69_2 Q2.hinj69_69_2
      Q2.hcardT69_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_69_2 i) (Q2.hfix69_69_2 i) _)
      colCert_69_69_17.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_69_18 (hp : 18 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 18 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 18 (transLenTr ⟨69, by decide⟩ 18 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 18 (transLenTr ⟨69, by decide⟩ 18 hp)) T69_69
      hfix69_69 hinj69_69 hcardT69_69
      (fun i => conj_mem_of_fixedPoints _ _ (T69_69 i) (hfix69_69 i) _)
      ⟨69, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 18 hp) Q2.T69_69_2 Q2.hfix69_69_2 Q2.hinj69_69_2
      Q2.hcardT69_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_69_2 i) (Q2.hfix69_69_2 i) _)
      colCert_69_69_18.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_69_19 (hp : 19 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 19 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 19 (transLenTr ⟨69, by decide⟩ 19 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 19 (transLenTr ⟨69, by decide⟩ 19 hp)) T69_69
      hfix69_69 hinj69_69 hcardT69_69
      (fun i => conj_mem_of_fixedPoints _ _ (T69_69 i) (hfix69_69 i) _)
      ⟨69, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 19 hp) Q2.T69_69_2 Q2.hfix69_69_2 Q2.hinj69_69_2
      Q2.hcardT69_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_69_2 i) (Q2.hfix69_69_2 i) _)
      colCert_69_69_19.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_69_20 (hp : 20 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 20 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 20 (transLenTr ⟨69, by decide⟩ 20 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 20 (transLenTr ⟨69, by decide⟩ 20 hp)) T69_69
      hfix69_69 hinj69_69 hcardT69_69
      (fun i => conj_mem_of_fixedPoints _ _ (T69_69 i) (hfix69_69 i) _)
      ⟨69, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 20 hp) Q2.T69_69_2 Q2.hfix69_69_2 Q2.hinj69_69_2
      Q2.hcardT69_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_69_2 i) (Q2.hfix69_69_2 i) _)
      colCert_69_69_20.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_69_21 (hp : 21 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 21 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 21 (transLenTr ⟨69, by decide⟩ 21 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 21 (transLenTr ⟨69, by decide⟩ 21 hp)) T69_69
      hfix69_69 hinj69_69 hcardT69_69
      (fun i => conj_mem_of_fixedPoints _ _ (T69_69 i) (hfix69_69 i) _)
      ⟨69, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 21 hp) Q2.T69_69_2 Q2.hfix69_69_2 Q2.hinj69_69_2
      Q2.hcardT69_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_69_2 i) (Q2.hfix69_69_2 i) _)
      colCert_69_69_21.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_69_22 (hp : 22 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 22 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 22 (transLenTr ⟨69, by decide⟩ 22 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 22 (transLenTr ⟨69, by decide⟩ 22 hp)) T69_69
      hfix69_69 hinj69_69 hcardT69_69
      (fun i => conj_mem_of_fixedPoints _ _ (T69_69 i) (hfix69_69 i) _)
      ⟨69, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 22 hp) Q2.T69_69_2 Q2.hfix69_69_2 Q2.hinj69_69_2
      Q2.hcardT69_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_69_2 i) (Q2.hfix69_69_2 i) _)
      colCert_69_69_22.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_69_23 (hp : 23 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 23 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 23 (transLenTr ⟨69, by decide⟩ 23 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 23 (transLenTr ⟨69, by decide⟩ 23 hp)) T69_69
      hfix69_69 hinj69_69 hcardT69_69
      (fun i => conj_mem_of_fixedPoints _ _ (T69_69 i) (hfix69_69 i) _)
      ⟨69, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 23 hp) Q2.T69_69_2 Q2.hfix69_69_2 Q2.hinj69_69_2
      Q2.hcardT69_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_69_2 i) (Q2.hfix69_69_2 i) _)
      colCert_69_69_23.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_69_24 (hp : 24 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 24 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 24 (transLenTr ⟨69, by decide⟩ 24 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 24 (transLenTr ⟨69, by decide⟩ 24 hp)) T69_69
      hfix69_69 hinj69_69 hcardT69_69
      (fun i => conj_mem_of_fixedPoints _ _ (T69_69 i) (hfix69_69 i) _)
      ⟨69, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 24 hp) Q2.T69_69_2 Q2.hfix69_69_2 Q2.hinj69_69_2
      Q2.hcardT69_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_69_2 i) (Q2.hfix69_69_2 i) _)
      colCert_69_69_24.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_70_9_0 (hp : 0 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 0 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp)) T70_9
      hfix70_9 hinj70_9 hcardT70_9
      (fun i => conj_mem_of_fixedPoints _ _ (T70_9 i) (hfix70_9 i) _)
      ⟨70, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 0 hp) Q2.T70_9_2 Q2.hfix70_9_2 Q2.hinj70_9_2
      Q2.hcardT70_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_9_2 i) (Q2.hfix70_9_2 i) _)
      colCert_70_9_0.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_9_1 (hp : 1 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 1 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp)) T70_9
      hfix70_9 hinj70_9 hcardT70_9
      (fun i => conj_mem_of_fixedPoints _ _ (T70_9 i) (hfix70_9 i) _)
      ⟨70, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 1 hp) Q2.T70_9_2 Q2.hfix70_9_2 Q2.hinj70_9_2
      Q2.hcardT70_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_9_2 i) (Q2.hfix70_9_2 i) _)
      colCert_70_9_1.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_9_2 (hp : 2 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 2 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp)) T70_9
      hfix70_9 hinj70_9 hcardT70_9
      (fun i => conj_mem_of_fixedPoints _ _ (T70_9 i) (hfix70_9 i) _)
      ⟨70, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 2 hp) Q2.T70_9_2 Q2.hfix70_9_2 Q2.hinj70_9_2
      Q2.hcardT70_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_9_2 i) (Q2.hfix70_9_2 i) _)
      colCert_70_9_2.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_9_3 (hp : 3 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 3 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp)) T70_9
      hfix70_9 hinj70_9 hcardT70_9
      (fun i => conj_mem_of_fixedPoints _ _ (T70_9 i) (hfix70_9 i) _)
      ⟨70, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 3 hp) Q2.T70_9_2 Q2.hfix70_9_2 Q2.hinj70_9_2
      Q2.hcardT70_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_9_2 i) (Q2.hfix70_9_2 i) _)
      colCert_70_9_3.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_9_4 (hp : 4 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 4 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp)) T70_9
      hfix70_9 hinj70_9 hcardT70_9
      (fun i => conj_mem_of_fixedPoints _ _ (T70_9 i) (hfix70_9 i) _)
      ⟨70, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 4 hp) Q2.T70_9_2 Q2.hfix70_9_2 Q2.hinj70_9_2
      Q2.hcardT70_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_9_2 i) (Q2.hfix70_9_2 i) _)
      colCert_70_9_4.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T70_12
      hfix70_12 hinj70_12 hcardT70_12
      (fun i => conj_mem_of_fixedPoints _ _ (T70_12 i) (hfix70_12 i) _)
      ⟨70, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T70_12_2 Q2.hfix70_12_2 Q2.hinj70_12_2
      Q2.hcardT70_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_12_2 i) (Q2.hfix70_12_2 i) _)
      colCert_70_12_0.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T70_12
      hfix70_12 hinj70_12 hcardT70_12
      (fun i => conj_mem_of_fixedPoints _ _ (T70_12 i) (hfix70_12 i) _)
      ⟨70, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T70_12_2 Q2.hfix70_12_2 Q2.hinj70_12_2
      Q2.hcardT70_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_12_2 i) (Q2.hfix70_12_2 i) _)
      colCert_70_12_1.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T70_12
      hfix70_12 hinj70_12 hcardT70_12
      (fun i => conj_mem_of_fixedPoints _ _ (T70_12 i) (hfix70_12 i) _)
      ⟨70, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T70_12_2 Q2.hfix70_12_2 Q2.hinj70_12_2
      Q2.hcardT70_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_12_2 i) (Q2.hfix70_12_2 i) _)
      colCert_70_12_2.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T70_12
      hfix70_12 hinj70_12 hcardT70_12
      (fun i => conj_mem_of_fixedPoints _ _ (T70_12 i) (hfix70_12 i) _)
      ⟨70, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T70_12_2 Q2.hfix70_12_2 Q2.hinj70_12_2
      Q2.hcardT70_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_12_2 i) (Q2.hfix70_12_2 i) _)
      colCert_70_12_3.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T70_12
      hfix70_12 hinj70_12 hcardT70_12
      (fun i => conj_mem_of_fixedPoints _ _ (T70_12 i) (hfix70_12 i) _)
      ⟨70, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T70_12_2 Q2.hfix70_12_2 Q2.hinj70_12_2
      Q2.hcardT70_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_12_2 i) (Q2.hfix70_12_2 i) _)
      colCert_70_12_4.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_27_0 (hp : 0 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 0 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp)) T70_27
      hfix70_27 hinj70_27 hcardT70_27
      (fun i => conj_mem_of_fixedPoints _ _ (T70_27 i) (hfix70_27 i) _)
      ⟨70, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 0 hp) Q2.T70_27_2 Q2.hfix70_27_2 Q2.hinj70_27_2
      Q2.hcardT70_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_27_2 i) (Q2.hfix70_27_2 i) _)
      colCert_70_27_0.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_27_1 (hp : 1 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 1 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp)) T70_27
      hfix70_27 hinj70_27 hcardT70_27
      (fun i => conj_mem_of_fixedPoints _ _ (T70_27 i) (hfix70_27 i) _)
      ⟨70, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 1 hp) Q2.T70_27_2 Q2.hfix70_27_2 Q2.hinj70_27_2
      Q2.hcardT70_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_27_2 i) (Q2.hfix70_27_2 i) _)
      colCert_70_27_1.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_27_2 (hp : 2 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 2 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp)) T70_27
      hfix70_27 hinj70_27 hcardT70_27
      (fun i => conj_mem_of_fixedPoints _ _ (T70_27 i) (hfix70_27 i) _)
      ⟨70, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 2 hp) Q2.T70_27_2 Q2.hfix70_27_2 Q2.hinj70_27_2
      Q2.hcardT70_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_27_2 i) (Q2.hfix70_27_2 i) _)
      colCert_70_27_2.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_27_3 (hp : 3 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 3 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp)) T70_27
      hfix70_27 hinj70_27 hcardT70_27
      (fun i => conj_mem_of_fixedPoints _ _ (T70_27 i) (hfix70_27 i) _)
      ⟨70, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 3 hp) Q2.T70_27_2 Q2.hfix70_27_2 Q2.hinj70_27_2
      Q2.hcardT70_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_27_2 i) (Q2.hfix70_27_2 i) _)
      colCert_70_27_3.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_27_4 (hp : 4 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 4 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp)) T70_27
      hfix70_27 hinj70_27 hcardT70_27
      (fun i => conj_mem_of_fixedPoints _ _ (T70_27 i) (hfix70_27 i) _)
      ⟨70, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 4 hp) Q2.T70_27_2 Q2.hfix70_27_2 Q2.hinj70_27_2
      Q2.hcardT70_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_27_2 i) (Q2.hfix70_27_2 i) _)
      colCert_70_27_4.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_27_5 (hp : 5 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 5 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp)) T70_27
      hfix70_27 hinj70_27 hcardT70_27
      (fun i => conj_mem_of_fixedPoints _ _ (T70_27 i) (hfix70_27 i) _)
      ⟨70, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 5 hp) Q2.T70_27_2 Q2.hfix70_27_2 Q2.hinj70_27_2
      Q2.hcardT70_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_27_2 i) (Q2.hfix70_27_2 i) _)
      colCert_70_27_5.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_27_10 (hp : 10 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 10 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp)) T70_27
      hfix70_27 hinj70_27 hcardT70_27
      (fun i => conj_mem_of_fixedPoints _ _ (T70_27 i) (hfix70_27 i) _)
      ⟨70, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 10 hp) Q2.T70_27_2 Q2.hfix70_27_2 Q2.hinj70_27_2
      Q2.hcardT70_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_27_2 i) (Q2.hfix70_27_2 i) _)
      colCert_70_27_10.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_27_15 (hp : 15 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 15 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp)) T70_27
      hfix70_27 hinj70_27 hcardT70_27
      (fun i => conj_mem_of_fixedPoints _ _ (T70_27 i) (hfix70_27 i) _)
      ⟨70, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 15 hp) Q2.T70_27_2 Q2.hfix70_27_2 Q2.hinj70_27_2
      Q2.hcardT70_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_27_2 i) (Q2.hfix70_27_2 i) _)
      colCert_70_27_15.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_27_20 (hp : 20 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 20 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp)) T70_27
      hfix70_27 hinj70_27 hcardT70_27
      (fun i => conj_mem_of_fixedPoints _ _ (T70_27 i) (hfix70_27 i) _)
      ⟨70, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 20 hp) Q2.T70_27_2 Q2.hfix70_27_2 Q2.hinj70_27_2
      Q2.hcardT70_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_27_2 i) (Q2.hfix70_27_2 i) _)
      colCert_70_27_20.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_31_0 (hp : 0 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 0 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp)) T70_31
      hfix70_31 hinj70_31 hcardT70_31
      (fun i => conj_mem_of_fixedPoints _ _ (T70_31 i) (hfix70_31 i) _)
      ⟨70, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 0 hp) Q2.T70_31_2 Q2.hfix70_31_2 Q2.hinj70_31_2
      Q2.hcardT70_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_31_2 i) (Q2.hfix70_31_2 i) _)
      colCert_70_31_0.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_31_1 (hp : 1 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 1 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp)) T70_31
      hfix70_31 hinj70_31 hcardT70_31
      (fun i => conj_mem_of_fixedPoints _ _ (T70_31 i) (hfix70_31 i) _)
      ⟨70, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 1 hp) Q2.T70_31_2 Q2.hfix70_31_2 Q2.hinj70_31_2
      Q2.hcardT70_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_31_2 i) (Q2.hfix70_31_2 i) _)
      colCert_70_31_1.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_31_2 (hp : 2 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 2 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp)) T70_31
      hfix70_31 hinj70_31 hcardT70_31
      (fun i => conj_mem_of_fixedPoints _ _ (T70_31 i) (hfix70_31 i) _)
      ⟨70, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 2 hp) Q2.T70_31_2 Q2.hfix70_31_2 Q2.hinj70_31_2
      Q2.hcardT70_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_31_2 i) (Q2.hfix70_31_2 i) _)
      colCert_70_31_2.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_31_3 (hp : 3 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 3 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp)) T70_31
      hfix70_31 hinj70_31 hcardT70_31
      (fun i => conj_mem_of_fixedPoints _ _ (T70_31 i) (hfix70_31 i) _)
      ⟨70, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 3 hp) Q2.T70_31_2 Q2.hfix70_31_2 Q2.hinj70_31_2
      Q2.hcardT70_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_31_2 i) (Q2.hfix70_31_2 i) _)
      colCert_70_31_3.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_31_4 (hp : 4 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 4 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp)) T70_31
      hfix70_31 hinj70_31 hcardT70_31
      (fun i => conj_mem_of_fixedPoints _ _ (T70_31 i) (hfix70_31 i) _)
      ⟨70, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 4 hp) Q2.T70_31_2 Q2.hfix70_31_2 Q2.hinj70_31_2
      Q2.hcardT70_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_31_2 i) (Q2.hfix70_31_2 i) _)
      colCert_70_31_4.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_31_5 (hp : 5 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 5 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp)) T70_31
      hfix70_31 hinj70_31 hcardT70_31
      (fun i => conj_mem_of_fixedPoints _ _ (T70_31 i) (hfix70_31 i) _)
      ⟨70, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 5 hp) Q2.T70_31_2 Q2.hfix70_31_2 Q2.hinj70_31_2
      Q2.hcardT70_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_31_2 i) (Q2.hfix70_31_2 i) _)
      colCert_70_31_5.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_31_10 (hp : 10 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 10 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp)) T70_31
      hfix70_31 hinj70_31 hcardT70_31
      (fun i => conj_mem_of_fixedPoints _ _ (T70_31 i) (hfix70_31 i) _)
      ⟨70, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 10 hp) Q2.T70_31_2 Q2.hfix70_31_2 Q2.hinj70_31_2
      Q2.hcardT70_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_31_2 i) (Q2.hfix70_31_2 i) _)
      colCert_70_31_10.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_31_15 (hp : 15 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 15 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp)) T70_31
      hfix70_31 hinj70_31 hcardT70_31
      (fun i => conj_mem_of_fixedPoints _ _ (T70_31 i) (hfix70_31 i) _)
      ⟨70, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 15 hp) Q2.T70_31_2 Q2.hfix70_31_2 Q2.hinj70_31_2
      Q2.hcardT70_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_31_2 i) (Q2.hfix70_31_2 i) _)
      colCert_70_31_15.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_31_20 (hp : 20 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 20 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp)) T70_31
      hfix70_31 hinj70_31 hcardT70_31
      (fun i => conj_mem_of_fixedPoints _ _ (T70_31 i) (hfix70_31 i) _)
      ⟨70, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 20 hp) Q2.T70_31_2 Q2.hfix70_31_2 Q2.hinj70_31_2
      Q2.hcardT70_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_31_2 i) (Q2.hfix70_31_2 i) _)
      colCert_70_31_20.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_36_0 (hp : 0 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 0 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp)) T70_36
      hfix70_36 hinj70_36 hcardT70_36
      (fun i => conj_mem_of_fixedPoints _ _ (T70_36 i) (hfix70_36 i) _)
      ⟨70, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 0 hp) Q2.T70_36_2 Q2.hfix70_36_2 Q2.hinj70_36_2
      Q2.hcardT70_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_36_2 i) (Q2.hfix70_36_2 i) _)
      colCert_70_36_0.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_36_1 (hp : 1 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 1 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp)) T70_36
      hfix70_36 hinj70_36 hcardT70_36
      (fun i => conj_mem_of_fixedPoints _ _ (T70_36 i) (hfix70_36 i) _)
      ⟨70, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 1 hp) Q2.T70_36_2 Q2.hfix70_36_2 Q2.hinj70_36_2
      Q2.hcardT70_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_36_2 i) (Q2.hfix70_36_2 i) _)
      colCert_70_36_1.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_36_2 (hp : 2 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 2 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp)) T70_36
      hfix70_36 hinj70_36 hcardT70_36
      (fun i => conj_mem_of_fixedPoints _ _ (T70_36 i) (hfix70_36 i) _)
      ⟨70, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 2 hp) Q2.T70_36_2 Q2.hfix70_36_2 Q2.hinj70_36_2
      Q2.hcardT70_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_36_2 i) (Q2.hfix70_36_2 i) _)
      colCert_70_36_2.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_36_3 (hp : 3 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 3 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp)) T70_36
      hfix70_36 hinj70_36 hcardT70_36
      (fun i => conj_mem_of_fixedPoints _ _ (T70_36 i) (hfix70_36 i) _)
      ⟨70, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 3 hp) Q2.T70_36_2 Q2.hfix70_36_2 Q2.hinj70_36_2
      Q2.hcardT70_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_36_2 i) (Q2.hfix70_36_2 i) _)
      colCert_70_36_3.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_36_4 (hp : 4 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 4 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp)) T70_36
      hfix70_36 hinj70_36 hcardT70_36
      (fun i => conj_mem_of_fixedPoints _ _ (T70_36 i) (hfix70_36 i) _)
      ⟨70, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 4 hp) Q2.T70_36_2 Q2.hfix70_36_2 Q2.hinj70_36_2
      Q2.hcardT70_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_36_2 i) (Q2.hfix70_36_2 i) _)
      colCert_70_36_4.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_36_5 (hp : 5 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 5 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp)) T70_36
      hfix70_36 hinj70_36 hcardT70_36
      (fun i => conj_mem_of_fixedPoints _ _ (T70_36 i) (hfix70_36 i) _)
      ⟨70, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 5 hp) Q2.T70_36_2 Q2.hfix70_36_2 Q2.hinj70_36_2
      Q2.hcardT70_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_36_2 i) (Q2.hfix70_36_2 i) _)
      colCert_70_36_5.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_36_10 (hp : 10 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 10 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp)) T70_36
      hfix70_36 hinj70_36 hcardT70_36
      (fun i => conj_mem_of_fixedPoints _ _ (T70_36 i) (hfix70_36 i) _)
      ⟨70, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 10 hp) Q2.T70_36_2 Q2.hfix70_36_2 Q2.hinj70_36_2
      Q2.hcardT70_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_36_2 i) (Q2.hfix70_36_2 i) _)
      colCert_70_36_10.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_36_15 (hp : 15 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 15 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp)) T70_36
      hfix70_36 hinj70_36 hcardT70_36
      (fun i => conj_mem_of_fixedPoints _ _ (T70_36 i) (hfix70_36 i) _)
      ⟨70, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 15 hp) Q2.T70_36_2 Q2.hfix70_36_2 Q2.hinj70_36_2
      Q2.hcardT70_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_36_2 i) (Q2.hfix70_36_2 i) _)
      colCert_70_36_15.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_36_20 (hp : 20 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 20 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp)) T70_36
      hfix70_36 hinj70_36 hcardT70_36
      (fun i => conj_mem_of_fixedPoints _ _ (T70_36 i) (hfix70_36 i) _)
      ⟨70, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 20 hp) Q2.T70_36_2 Q2.hfix70_36_2 Q2.hinj70_36_2
      Q2.hcardT70_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_36_2 i) (Q2.hfix70_36_2 i) _)
      colCert_70_36_20.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_41_0 (hp : 0 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 0 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp)) T70_41
      hfix70_41 hinj70_41 hcardT70_41
      (fun i => conj_mem_of_fixedPoints _ _ (T70_41 i) (hfix70_41 i) _)
      ⟨70, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 0 hp) Q2.T70_41_2 Q2.hfix70_41_2 Q2.hinj70_41_2
      Q2.hcardT70_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_41_2 i) (Q2.hfix70_41_2 i) _)
      colCert_70_41_0.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_41_1 (hp : 1 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 1 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp)) T70_41
      hfix70_41 hinj70_41 hcardT70_41
      (fun i => conj_mem_of_fixedPoints _ _ (T70_41 i) (hfix70_41 i) _)
      ⟨70, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 1 hp) Q2.T70_41_2 Q2.hfix70_41_2 Q2.hinj70_41_2
      Q2.hcardT70_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_41_2 i) (Q2.hfix70_41_2 i) _)
      colCert_70_41_1.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_41_2 (hp : 2 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 2 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp)) T70_41
      hfix70_41 hinj70_41 hcardT70_41
      (fun i => conj_mem_of_fixedPoints _ _ (T70_41 i) (hfix70_41 i) _)
      ⟨70, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 2 hp) Q2.T70_41_2 Q2.hfix70_41_2 Q2.hinj70_41_2
      Q2.hcardT70_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_41_2 i) (Q2.hfix70_41_2 i) _)
      colCert_70_41_2.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_41_3 (hp : 3 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 3 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp)) T70_41
      hfix70_41 hinj70_41 hcardT70_41
      (fun i => conj_mem_of_fixedPoints _ _ (T70_41 i) (hfix70_41 i) _)
      ⟨70, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 3 hp) Q2.T70_41_2 Q2.hfix70_41_2 Q2.hinj70_41_2
      Q2.hcardT70_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_41_2 i) (Q2.hfix70_41_2 i) _)
      colCert_70_41_3.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_41_4 (hp : 4 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 4 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp)) T70_41
      hfix70_41 hinj70_41 hcardT70_41
      (fun i => conj_mem_of_fixedPoints _ _ (T70_41 i) (hfix70_41 i) _)
      ⟨70, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 4 hp) Q2.T70_41_2 Q2.hfix70_41_2 Q2.hinj70_41_2
      Q2.hcardT70_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_41_2 i) (Q2.hfix70_41_2 i) _)
      colCert_70_41_4.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_41_5 (hp : 5 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 5 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp)) T70_41
      hfix70_41 hinj70_41 hcardT70_41
      (fun i => conj_mem_of_fixedPoints _ _ (T70_41 i) (hfix70_41 i) _)
      ⟨70, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 5 hp) Q2.T70_41_2 Q2.hfix70_41_2 Q2.hinj70_41_2
      Q2.hcardT70_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_41_2 i) (Q2.hfix70_41_2 i) _)
      colCert_70_41_5.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_41_10 (hp : 10 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 10 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp)) T70_41
      hfix70_41 hinj70_41 hcardT70_41
      (fun i => conj_mem_of_fixedPoints _ _ (T70_41 i) (hfix70_41 i) _)
      ⟨70, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 10 hp) Q2.T70_41_2 Q2.hfix70_41_2 Q2.hinj70_41_2
      Q2.hcardT70_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_41_2 i) (Q2.hfix70_41_2 i) _)
      colCert_70_41_10.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_41_15 (hp : 15 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 15 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp)) T70_41
      hfix70_41 hinj70_41 hcardT70_41
      (fun i => conj_mem_of_fixedPoints _ _ (T70_41 i) (hfix70_41 i) _)
      ⟨70, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 15 hp) Q2.T70_41_2 Q2.hfix70_41_2 Q2.hinj70_41_2
      Q2.hcardT70_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_41_2 i) (Q2.hfix70_41_2 i) _)
      colCert_70_41_15.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_41_20 (hp : 20 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 20 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp)) T70_41
      hfix70_41 hinj70_41 hcardT70_41
      (fun i => conj_mem_of_fixedPoints _ _ (T70_41 i) (hfix70_41 i) _)
      ⟨70, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 20 hp) Q2.T70_41_2 Q2.hfix70_41_2 Q2.hinj70_41_2
      Q2.hcardT70_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_41_2 i) (Q2.hfix70_41_2 i) _)
      colCert_70_41_20.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_46_0 (hp : 0 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 0 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp)) T70_46
      hfix70_46 hinj70_46 hcardT70_46
      (fun i => conj_mem_of_fixedPoints _ _ (T70_46 i) (hfix70_46 i) _)
      ⟨70, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 0 hp) Q2.T70_46_2 Q2.hfix70_46_2 Q2.hinj70_46_2
      Q2.hcardT70_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_46_2 i) (Q2.hfix70_46_2 i) _)
      colCert_70_46_0.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_46_1 (hp : 1 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 1 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp)) T70_46
      hfix70_46 hinj70_46 hcardT70_46
      (fun i => conj_mem_of_fixedPoints _ _ (T70_46 i) (hfix70_46 i) _)
      ⟨70, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 1 hp) Q2.T70_46_2 Q2.hfix70_46_2 Q2.hinj70_46_2
      Q2.hcardT70_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_46_2 i) (Q2.hfix70_46_2 i) _)
      colCert_70_46_1.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_46_2 (hp : 2 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 2 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp)) T70_46
      hfix70_46 hinj70_46 hcardT70_46
      (fun i => conj_mem_of_fixedPoints _ _ (T70_46 i) (hfix70_46 i) _)
      ⟨70, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 2 hp) Q2.T70_46_2 Q2.hfix70_46_2 Q2.hinj70_46_2
      Q2.hcardT70_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_46_2 i) (Q2.hfix70_46_2 i) _)
      colCert_70_46_2.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_46_3 (hp : 3 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 3 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp)) T70_46
      hfix70_46 hinj70_46 hcardT70_46
      (fun i => conj_mem_of_fixedPoints _ _ (T70_46 i) (hfix70_46 i) _)
      ⟨70, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 3 hp) Q2.T70_46_2 Q2.hfix70_46_2 Q2.hinj70_46_2
      Q2.hcardT70_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_46_2 i) (Q2.hfix70_46_2 i) _)
      colCert_70_46_3.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_46_4 (hp : 4 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 4 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp)) T70_46
      hfix70_46 hinj70_46 hcardT70_46
      (fun i => conj_mem_of_fixedPoints _ _ (T70_46 i) (hfix70_46 i) _)
      ⟨70, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 4 hp) Q2.T70_46_2 Q2.hfix70_46_2 Q2.hinj70_46_2
      Q2.hcardT70_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_46_2 i) (Q2.hfix70_46_2 i) _)
      colCert_70_46_4.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_46_5 (hp : 5 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 5 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp)) T70_46
      hfix70_46 hinj70_46 hcardT70_46
      (fun i => conj_mem_of_fixedPoints _ _ (T70_46 i) (hfix70_46 i) _)
      ⟨70, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 5 hp) Q2.T70_46_2 Q2.hfix70_46_2 Q2.hinj70_46_2
      Q2.hcardT70_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_46_2 i) (Q2.hfix70_46_2 i) _)
      colCert_70_46_5.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_46_10 (hp : 10 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 10 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp)) T70_46
      hfix70_46 hinj70_46 hcardT70_46
      (fun i => conj_mem_of_fixedPoints _ _ (T70_46 i) (hfix70_46 i) _)
      ⟨70, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 10 hp) Q2.T70_46_2 Q2.hfix70_46_2 Q2.hinj70_46_2
      Q2.hcardT70_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_46_2 i) (Q2.hfix70_46_2 i) _)
      colCert_70_46_10.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_46_15 (hp : 15 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 15 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp)) T70_46
      hfix70_46 hinj70_46 hcardT70_46
      (fun i => conj_mem_of_fixedPoints _ _ (T70_46 i) (hfix70_46 i) _)
      ⟨70, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 15 hp) Q2.T70_46_2 Q2.hfix70_46_2 Q2.hinj70_46_2
      Q2.hcardT70_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_46_2 i) (Q2.hfix70_46_2 i) _)
      colCert_70_46_15.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_46_20 (hp : 20 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 20 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp)) T70_46
      hfix70_46 hinj70_46 hcardT70_46
      (fun i => conj_mem_of_fixedPoints _ _ (T70_46 i) (hfix70_46 i) _)
      ⟨70, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 20 hp) Q2.T70_46_2 Q2.hfix70_46_2 Q2.hinj70_46_2
      Q2.hcardT70_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_46_2 i) (Q2.hfix70_46_2 i) _)
      colCert_70_46_20.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_51_0 (hp : 0 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 0 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp)) T70_51
      hfix70_51 hinj70_51 hcardT70_51
      (fun i => conj_mem_of_fixedPoints _ _ (T70_51 i) (hfix70_51 i) _)
      ⟨70, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 0 hp) Q2.T70_51_2 Q2.hfix70_51_2 Q2.hinj70_51_2
      Q2.hcardT70_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_51_2 i) (Q2.hfix70_51_2 i) _)
      colCert_70_51_0.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_51_1 (hp : 1 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 1 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp)) T70_51
      hfix70_51 hinj70_51 hcardT70_51
      (fun i => conj_mem_of_fixedPoints _ _ (T70_51 i) (hfix70_51 i) _)
      ⟨70, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 1 hp) Q2.T70_51_2 Q2.hfix70_51_2 Q2.hinj70_51_2
      Q2.hcardT70_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_51_2 i) (Q2.hfix70_51_2 i) _)
      colCert_70_51_1.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_51_2 (hp : 2 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 2 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp)) T70_51
      hfix70_51 hinj70_51 hcardT70_51
      (fun i => conj_mem_of_fixedPoints _ _ (T70_51 i) (hfix70_51 i) _)
      ⟨70, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 2 hp) Q2.T70_51_2 Q2.hfix70_51_2 Q2.hinj70_51_2
      Q2.hcardT70_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_51_2 i) (Q2.hfix70_51_2 i) _)
      colCert_70_51_2.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_51_3 (hp : 3 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 3 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp)) T70_51
      hfix70_51 hinj70_51 hcardT70_51
      (fun i => conj_mem_of_fixedPoints _ _ (T70_51 i) (hfix70_51 i) _)
      ⟨70, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 3 hp) Q2.T70_51_2 Q2.hfix70_51_2 Q2.hinj70_51_2
      Q2.hcardT70_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_51_2 i) (Q2.hfix70_51_2 i) _)
      colCert_70_51_3.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_51_4 (hp : 4 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 4 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp)) T70_51
      hfix70_51 hinj70_51 hcardT70_51
      (fun i => conj_mem_of_fixedPoints _ _ (T70_51 i) (hfix70_51 i) _)
      ⟨70, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 4 hp) Q2.T70_51_2 Q2.hfix70_51_2 Q2.hinj70_51_2
      Q2.hcardT70_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_51_2 i) (Q2.hfix70_51_2 i) _)
      colCert_70_51_4.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_51_5 (hp : 5 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 5 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp)) T70_51
      hfix70_51 hinj70_51 hcardT70_51
      (fun i => conj_mem_of_fixedPoints _ _ (T70_51 i) (hfix70_51 i) _)
      ⟨70, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 5 hp) Q2.T70_51_2 Q2.hfix70_51_2 Q2.hinj70_51_2
      Q2.hcardT70_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_51_2 i) (Q2.hfix70_51_2 i) _)
      colCert_70_51_5.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_51_10 (hp : 10 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 10 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp)) T70_51
      hfix70_51 hinj70_51 hcardT70_51
      (fun i => conj_mem_of_fixedPoints _ _ (T70_51 i) (hfix70_51 i) _)
      ⟨70, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 10 hp) Q2.T70_51_2 Q2.hfix70_51_2 Q2.hinj70_51_2
      Q2.hcardT70_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_51_2 i) (Q2.hfix70_51_2 i) _)
      colCert_70_51_10.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_51_15 (hp : 15 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 15 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp)) T70_51
      hfix70_51 hinj70_51 hcardT70_51
      (fun i => conj_mem_of_fixedPoints _ _ (T70_51 i) (hfix70_51 i) _)
      ⟨70, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 15 hp) Q2.T70_51_2 Q2.hfix70_51_2 Q2.hinj70_51_2
      Q2.hcardT70_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_51_2 i) (Q2.hfix70_51_2 i) _)
      colCert_70_51_15.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_51_20 (hp : 20 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 20 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp)) T70_51
      hfix70_51 hinj70_51 hcardT70_51
      (fun i => conj_mem_of_fixedPoints _ _ (T70_51 i) (hfix70_51 i) _)
      ⟨70, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 20 hp) Q2.T70_51_2 Q2.hfix70_51_2 Q2.hinj70_51_2
      Q2.hcardT70_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_51_2 i) (Q2.hfix70_51_2 i) _)
      colCert_70_51_20.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_70_0 (hp : 0 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 0 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 0 (transLenTr ⟨70, by decide⟩ 0 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 0 (transLenTr ⟨70, by decide⟩ 0 hp)) T70_70
      hfix70_70 hinj70_70 hcardT70_70
      (fun i => conj_mem_of_fixedPoints _ _ (T70_70 i) (hfix70_70 i) _)
      ⟨70, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 0 hp) Q2.T70_70_2 Q2.hfix70_70_2 Q2.hinj70_70_2
      Q2.hcardT70_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_70_2 i) (Q2.hfix70_70_2 i) _)
      colCert_70_70_0.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_70_1 (hp : 1 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 1 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 1 (transLenTr ⟨70, by decide⟩ 1 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 1 (transLenTr ⟨70, by decide⟩ 1 hp)) T70_70
      hfix70_70 hinj70_70 hcardT70_70
      (fun i => conj_mem_of_fixedPoints _ _ (T70_70 i) (hfix70_70 i) _)
      ⟨70, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 1 hp) Q2.T70_70_2 Q2.hfix70_70_2 Q2.hinj70_70_2
      Q2.hcardT70_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_70_2 i) (Q2.hfix70_70_2 i) _)
      colCert_70_70_1.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_70_2 (hp : 2 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 2 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 2 (transLenTr ⟨70, by decide⟩ 2 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 2 (transLenTr ⟨70, by decide⟩ 2 hp)) T70_70
      hfix70_70 hinj70_70 hcardT70_70
      (fun i => conj_mem_of_fixedPoints _ _ (T70_70 i) (hfix70_70 i) _)
      ⟨70, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 2 hp) Q2.T70_70_2 Q2.hfix70_70_2 Q2.hinj70_70_2
      Q2.hcardT70_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_70_2 i) (Q2.hfix70_70_2 i) _)
      colCert_70_70_2.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_70_3 (hp : 3 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 3 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 3 (transLenTr ⟨70, by decide⟩ 3 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 3 (transLenTr ⟨70, by decide⟩ 3 hp)) T70_70
      hfix70_70 hinj70_70 hcardT70_70
      (fun i => conj_mem_of_fixedPoints _ _ (T70_70 i) (hfix70_70 i) _)
      ⟨70, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 3 hp) Q2.T70_70_2 Q2.hfix70_70_2 Q2.hinj70_70_2
      Q2.hcardT70_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_70_2 i) (Q2.hfix70_70_2 i) _)
      colCert_70_70_3.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_70_4 (hp : 4 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 4 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 4 (transLenTr ⟨70, by decide⟩ 4 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 4 (transLenTr ⟨70, by decide⟩ 4 hp)) T70_70
      hfix70_70 hinj70_70 hcardT70_70
      (fun i => conj_mem_of_fixedPoints _ _ (T70_70 i) (hfix70_70 i) _)
      ⟨70, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 4 hp) Q2.T70_70_2 Q2.hfix70_70_2 Q2.hinj70_70_2
      Q2.hcardT70_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_70_2 i) (Q2.hfix70_70_2 i) _)
      colCert_70_70_4.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_70_5 (hp : 5 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 5 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 5 (transLenTr ⟨70, by decide⟩ 5 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 5 (transLenTr ⟨70, by decide⟩ 5 hp)) T70_70
      hfix70_70 hinj70_70 hcardT70_70
      (fun i => conj_mem_of_fixedPoints _ _ (T70_70 i) (hfix70_70 i) _)
      ⟨70, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 5 hp) Q2.T70_70_2 Q2.hfix70_70_2 Q2.hinj70_70_2
      Q2.hcardT70_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_70_2 i) (Q2.hfix70_70_2 i) _)
      colCert_70_70_5.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_70_6 (hp : 6 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 6 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 6 (transLenTr ⟨70, by decide⟩ 6 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 6 (transLenTr ⟨70, by decide⟩ 6 hp)) T70_70
      hfix70_70 hinj70_70 hcardT70_70
      (fun i => conj_mem_of_fixedPoints _ _ (T70_70 i) (hfix70_70 i) _)
      ⟨70, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 6 hp) Q2.T70_70_2 Q2.hfix70_70_2 Q2.hinj70_70_2
      Q2.hcardT70_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_70_2 i) (Q2.hfix70_70_2 i) _)
      colCert_70_70_6.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_70_7 (hp : 7 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 7 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 7 (transLenTr ⟨70, by decide⟩ 7 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 7 (transLenTr ⟨70, by decide⟩ 7 hp)) T70_70
      hfix70_70 hinj70_70 hcardT70_70
      (fun i => conj_mem_of_fixedPoints _ _ (T70_70 i) (hfix70_70 i) _)
      ⟨70, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 7 hp) Q2.T70_70_2 Q2.hfix70_70_2 Q2.hinj70_70_2
      Q2.hcardT70_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_70_2 i) (Q2.hfix70_70_2 i) _)
      colCert_70_70_7.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_70_8 (hp : 8 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 8 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 8 (transLenTr ⟨70, by decide⟩ 8 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 8 (transLenTr ⟨70, by decide⟩ 8 hp)) T70_70
      hfix70_70 hinj70_70 hcardT70_70
      (fun i => conj_mem_of_fixedPoints _ _ (T70_70 i) (hfix70_70 i) _)
      ⟨70, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 8 hp) Q2.T70_70_2 Q2.hfix70_70_2 Q2.hinj70_70_2
      Q2.hcardT70_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_70_2 i) (Q2.hfix70_70_2 i) _)
      colCert_70_70_8.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_70_9 (hp : 9 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 9 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 9 (transLenTr ⟨70, by decide⟩ 9 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 9 (transLenTr ⟨70, by decide⟩ 9 hp)) T70_70
      hfix70_70 hinj70_70 hcardT70_70
      (fun i => conj_mem_of_fixedPoints _ _ (T70_70 i) (hfix70_70 i) _)
      ⟨70, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 9 hp) Q2.T70_70_2 Q2.hfix70_70_2 Q2.hinj70_70_2
      Q2.hcardT70_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_70_2 i) (Q2.hfix70_70_2 i) _)
      colCert_70_70_9.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_70_10 (hp : 10 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 10 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 10 (transLenTr ⟨70, by decide⟩ 10 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 10 (transLenTr ⟨70, by decide⟩ 10 hp)) T70_70
      hfix70_70 hinj70_70 hcardT70_70
      (fun i => conj_mem_of_fixedPoints _ _ (T70_70 i) (hfix70_70 i) _)
      ⟨70, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 10 hp) Q2.T70_70_2 Q2.hfix70_70_2 Q2.hinj70_70_2
      Q2.hcardT70_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_70_2 i) (Q2.hfix70_70_2 i) _)
      colCert_70_70_10.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_70_11 (hp : 11 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 11 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 11 (transLenTr ⟨70, by decide⟩ 11 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 11 (transLenTr ⟨70, by decide⟩ 11 hp)) T70_70
      hfix70_70 hinj70_70 hcardT70_70
      (fun i => conj_mem_of_fixedPoints _ _ (T70_70 i) (hfix70_70 i) _)
      ⟨70, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 11 hp) Q2.T70_70_2 Q2.hfix70_70_2 Q2.hinj70_70_2
      Q2.hcardT70_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_70_2 i) (Q2.hfix70_70_2 i) _)
      colCert_70_70_11.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_70_12 (hp : 12 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 12 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 12 (transLenTr ⟨70, by decide⟩ 12 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 12 (transLenTr ⟨70, by decide⟩ 12 hp)) T70_70
      hfix70_70 hinj70_70 hcardT70_70
      (fun i => conj_mem_of_fixedPoints _ _ (T70_70 i) (hfix70_70 i) _)
      ⟨70, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 12 hp) Q2.T70_70_2 Q2.hfix70_70_2 Q2.hinj70_70_2
      Q2.hcardT70_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_70_2 i) (Q2.hfix70_70_2 i) _)
      colCert_70_70_12.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_70_13 (hp : 13 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 13 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 13 (transLenTr ⟨70, by decide⟩ 13 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 13 (transLenTr ⟨70, by decide⟩ 13 hp)) T70_70
      hfix70_70 hinj70_70 hcardT70_70
      (fun i => conj_mem_of_fixedPoints _ _ (T70_70 i) (hfix70_70 i) _)
      ⟨70, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 13 hp) Q2.T70_70_2 Q2.hfix70_70_2 Q2.hinj70_70_2
      Q2.hcardT70_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_70_2 i) (Q2.hfix70_70_2 i) _)
      colCert_70_70_13.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_70_14 (hp : 14 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 14 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 14 (transLenTr ⟨70, by decide⟩ 14 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 14 (transLenTr ⟨70, by decide⟩ 14 hp)) T70_70
      hfix70_70 hinj70_70 hcardT70_70
      (fun i => conj_mem_of_fixedPoints _ _ (T70_70 i) (hfix70_70 i) _)
      ⟨70, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 14 hp) Q2.T70_70_2 Q2.hfix70_70_2 Q2.hinj70_70_2
      Q2.hcardT70_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_70_2 i) (Q2.hfix70_70_2 i) _)
      colCert_70_70_14.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_70_15 (hp : 15 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 15 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 15 (transLenTr ⟨70, by decide⟩ 15 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 15 (transLenTr ⟨70, by decide⟩ 15 hp)) T70_70
      hfix70_70 hinj70_70 hcardT70_70
      (fun i => conj_mem_of_fixedPoints _ _ (T70_70 i) (hfix70_70 i) _)
      ⟨70, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 15 hp) Q2.T70_70_2 Q2.hfix70_70_2 Q2.hinj70_70_2
      Q2.hcardT70_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_70_2 i) (Q2.hfix70_70_2 i) _)
      colCert_70_70_15.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_70_16 (hp : 16 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 16 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 16 (transLenTr ⟨70, by decide⟩ 16 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 16 (transLenTr ⟨70, by decide⟩ 16 hp)) T70_70
      hfix70_70 hinj70_70 hcardT70_70
      (fun i => conj_mem_of_fixedPoints _ _ (T70_70 i) (hfix70_70 i) _)
      ⟨70, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 16 hp) Q2.T70_70_2 Q2.hfix70_70_2 Q2.hinj70_70_2
      Q2.hcardT70_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_70_2 i) (Q2.hfix70_70_2 i) _)
      colCert_70_70_16.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_70_17 (hp : 17 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 17 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 17 (transLenTr ⟨70, by decide⟩ 17 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 17 (transLenTr ⟨70, by decide⟩ 17 hp)) T70_70
      hfix70_70 hinj70_70 hcardT70_70
      (fun i => conj_mem_of_fixedPoints _ _ (T70_70 i) (hfix70_70 i) _)
      ⟨70, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 17 hp) Q2.T70_70_2 Q2.hfix70_70_2 Q2.hinj70_70_2
      Q2.hcardT70_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_70_2 i) (Q2.hfix70_70_2 i) _)
      colCert_70_70_17.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_70_18 (hp : 18 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 18 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 18 (transLenTr ⟨70, by decide⟩ 18 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 18 (transLenTr ⟨70, by decide⟩ 18 hp)) T70_70
      hfix70_70 hinj70_70 hcardT70_70
      (fun i => conj_mem_of_fixedPoints _ _ (T70_70 i) (hfix70_70 i) _)
      ⟨70, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 18 hp) Q2.T70_70_2 Q2.hfix70_70_2 Q2.hinj70_70_2
      Q2.hcardT70_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_70_2 i) (Q2.hfix70_70_2 i) _)
      colCert_70_70_18.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_70_19 (hp : 19 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 19 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 19 (transLenTr ⟨70, by decide⟩ 19 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 19 (transLenTr ⟨70, by decide⟩ 19 hp)) T70_70
      hfix70_70 hinj70_70 hcardT70_70
      (fun i => conj_mem_of_fixedPoints _ _ (T70_70 i) (hfix70_70 i) _)
      ⟨70, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 19 hp) Q2.T70_70_2 Q2.hfix70_70_2 Q2.hinj70_70_2
      Q2.hcardT70_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_70_2 i) (Q2.hfix70_70_2 i) _)
      colCert_70_70_19.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_70_20 (hp : 20 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 20 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 20 (transLenTr ⟨70, by decide⟩ 20 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 20 (transLenTr ⟨70, by decide⟩ 20 hp)) T70_70
      hfix70_70 hinj70_70 hcardT70_70
      (fun i => conj_mem_of_fixedPoints _ _ (T70_70 i) (hfix70_70 i) _)
      ⟨70, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 20 hp) Q2.T70_70_2 Q2.hfix70_70_2 Q2.hinj70_70_2
      Q2.hcardT70_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_70_2 i) (Q2.hfix70_70_2 i) _)
      colCert_70_70_20.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_70_21 (hp : 21 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 21 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 21 (transLenTr ⟨70, by decide⟩ 21 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 21 (transLenTr ⟨70, by decide⟩ 21 hp)) T70_70
      hfix70_70 hinj70_70 hcardT70_70
      (fun i => conj_mem_of_fixedPoints _ _ (T70_70 i) (hfix70_70 i) _)
      ⟨70, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 21 hp) Q2.T70_70_2 Q2.hfix70_70_2 Q2.hinj70_70_2
      Q2.hcardT70_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_70_2 i) (Q2.hfix70_70_2 i) _)
      colCert_70_70_21.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_70_22 (hp : 22 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 22 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 22 (transLenTr ⟨70, by decide⟩ 22 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 22 (transLenTr ⟨70, by decide⟩ 22 hp)) T70_70
      hfix70_70 hinj70_70 hcardT70_70
      (fun i => conj_mem_of_fixedPoints _ _ (T70_70 i) (hfix70_70 i) _)
      ⟨70, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 22 hp) Q2.T70_70_2 Q2.hfix70_70_2 Q2.hinj70_70_2
      Q2.hcardT70_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_70_2 i) (Q2.hfix70_70_2 i) _)
      colCert_70_70_22.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_70_23 (hp : 23 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 23 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 23 (transLenTr ⟨70, by decide⟩ 23 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 23 (transLenTr ⟨70, by decide⟩ 23 hp)) T70_70
      hfix70_70 hinj70_70 hcardT70_70
      (fun i => conj_mem_of_fixedPoints _ _ (T70_70 i) (hfix70_70 i) _)
      ⟨70, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 23 hp) Q2.T70_70_2 Q2.hfix70_70_2 Q2.hinj70_70_2
      Q2.hcardT70_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_70_2 i) (Q2.hfix70_70_2 i) _)
      colCert_70_70_23.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_70_70_24 (hp : 24 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 24 hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 24 (transLenTr ⟨70, by decide⟩ 24 hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨70, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨70, by decide⟩ (listedAt ⟨70, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 24 (transLenTr ⟨70, by decide⟩ 24 hp)) T70_70
      hfix70_70 hinj70_70 hcardT70_70
      (fun i => conj_mem_of_fixedPoints _ _ (T70_70 i) (hfix70_70 i) _)
      ⟨70, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨70, by decide⟩ (Q2.listedAt ⟨70, by decide⟩
        (alnCheck_rep ⟨70, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 24 hp) Q2.T70_70_2 Q2.hfix70_70_2 Q2.hinj70_70_2
      Q2.hcardT70_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T70_70_2 i) (Q2.hfix70_70_2 i) _)
      colCert_70_70_24.hD ?_).symm
  rw [alnId_70 j hj]


theorem leaf_71_1_0 (hp : 0 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 0 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp)) T71_1
      hfix71_1 hinj71_1 hcardT71_1
      (fun i => conj_mem_of_fixedPoints _ _ (T71_1 i) (hfix71_1 i) _)
      ⟨71, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 0 hp) Q2.T71_1_2 Q2.hfix71_1_2 Q2.hinj71_1_2
      Q2.hcardT71_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_1_2 i) (Q2.hfix71_1_2 i) _)
      colCert_71_1_0.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_1_1 (hp : 1 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 1 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp)) T71_1
      hfix71_1 hinj71_1 hcardT71_1
      (fun i => conj_mem_of_fixedPoints _ _ (T71_1 i) (hfix71_1 i) _)
      ⟨71, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 1 hp) Q2.T71_1_2 Q2.hfix71_1_2 Q2.hinj71_1_2
      Q2.hcardT71_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_1_2 i) (Q2.hfix71_1_2 i) _)
      colCert_71_1_1.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_1_2 (hp : 2 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 2 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp)) T71_1
      hfix71_1 hinj71_1 hcardT71_1
      (fun i => conj_mem_of_fixedPoints _ _ (T71_1 i) (hfix71_1 i) _)
      ⟨71, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 2 hp) Q2.T71_1_2 Q2.hfix71_1_2 Q2.hinj71_1_2
      Q2.hcardT71_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_1_2 i) (Q2.hfix71_1_2 i) _)
      colCert_71_1_2.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_1_3 (hp : 3 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 3 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp)) T71_1
      hfix71_1 hinj71_1 hcardT71_1
      (fun i => conj_mem_of_fixedPoints _ _ (T71_1 i) (hfix71_1 i) _)
      ⟨71, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 3 hp) Q2.T71_1_2 Q2.hfix71_1_2 Q2.hinj71_1_2
      Q2.hcardT71_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_1_2 i) (Q2.hfix71_1_2 i) _)
      colCert_71_1_3.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_1_4 (hp : 4 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 4 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp)) T71_1
      hfix71_1 hinj71_1 hcardT71_1
      (fun i => conj_mem_of_fixedPoints _ _ (T71_1 i) (hfix71_1 i) _)
      ⟨71, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 4 hp) Q2.T71_1_2 Q2.hfix71_1_2 Q2.hinj71_1_2
      Q2.hcardT71_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_1_2 i) (Q2.hfix71_1_2 i) _)
      colCert_71_1_4.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T71_12
      hfix71_12 hinj71_12 hcardT71_12
      (fun i => conj_mem_of_fixedPoints _ _ (T71_12 i) (hfix71_12 i) _)
      ⟨71, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T71_12_2 Q2.hfix71_12_2 Q2.hinj71_12_2
      Q2.hcardT71_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_12_2 i) (Q2.hfix71_12_2 i) _)
      colCert_71_12_0.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T71_12
      hfix71_12 hinj71_12 hcardT71_12
      (fun i => conj_mem_of_fixedPoints _ _ (T71_12 i) (hfix71_12 i) _)
      ⟨71, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T71_12_2 Q2.hfix71_12_2 Q2.hinj71_12_2
      Q2.hcardT71_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_12_2 i) (Q2.hfix71_12_2 i) _)
      colCert_71_12_1.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T71_12
      hfix71_12 hinj71_12 hcardT71_12
      (fun i => conj_mem_of_fixedPoints _ _ (T71_12 i) (hfix71_12 i) _)
      ⟨71, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T71_12_2 Q2.hfix71_12_2 Q2.hinj71_12_2
      Q2.hcardT71_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_12_2 i) (Q2.hfix71_12_2 i) _)
      colCert_71_12_2.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T71_12
      hfix71_12 hinj71_12 hcardT71_12
      (fun i => conj_mem_of_fixedPoints _ _ (T71_12 i) (hfix71_12 i) _)
      ⟨71, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T71_12_2 Q2.hfix71_12_2 Q2.hinj71_12_2
      Q2.hcardT71_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_12_2 i) (Q2.hfix71_12_2 i) _)
      colCert_71_12_3.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T71_12
      hfix71_12 hinj71_12 hcardT71_12
      (fun i => conj_mem_of_fixedPoints _ _ (T71_12 i) (hfix71_12 i) _)
      ⟨71, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T71_12_2 Q2.hfix71_12_2 Q2.hinj71_12_2
      Q2.hcardT71_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_12_2 i) (Q2.hfix71_12_2 i) _)
      colCert_71_12_4.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_19_0 (hp : 0 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 0 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp)) T71_19
      hfix71_19 hinj71_19 hcardT71_19
      (fun i => conj_mem_of_fixedPoints _ _ (T71_19 i) (hfix71_19 i) _)
      ⟨71, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 0 hp) Q2.T71_19_2 Q2.hfix71_19_2 Q2.hinj71_19_2
      Q2.hcardT71_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_19_2 i) (Q2.hfix71_19_2 i) _)
      colCert_71_19_0.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_19_1 (hp : 1 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 1 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp)) T71_19
      hfix71_19 hinj71_19 hcardT71_19
      (fun i => conj_mem_of_fixedPoints _ _ (T71_19 i) (hfix71_19 i) _)
      ⟨71, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 1 hp) Q2.T71_19_2 Q2.hfix71_19_2 Q2.hinj71_19_2
      Q2.hcardT71_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_19_2 i) (Q2.hfix71_19_2 i) _)
      colCert_71_19_1.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_19_2 (hp : 2 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 2 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp)) T71_19
      hfix71_19 hinj71_19 hcardT71_19
      (fun i => conj_mem_of_fixedPoints _ _ (T71_19 i) (hfix71_19 i) _)
      ⟨71, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 2 hp) Q2.T71_19_2 Q2.hfix71_19_2 Q2.hinj71_19_2
      Q2.hcardT71_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_19_2 i) (Q2.hfix71_19_2 i) _)
      colCert_71_19_2.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_19_3 (hp : 3 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 3 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp)) T71_19
      hfix71_19 hinj71_19 hcardT71_19
      (fun i => conj_mem_of_fixedPoints _ _ (T71_19 i) (hfix71_19 i) _)
      ⟨71, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 3 hp) Q2.T71_19_2 Q2.hfix71_19_2 Q2.hinj71_19_2
      Q2.hcardT71_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_19_2 i) (Q2.hfix71_19_2 i) _)
      colCert_71_19_3.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_19_4 (hp : 4 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 4 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp)) T71_19
      hfix71_19 hinj71_19 hcardT71_19
      (fun i => conj_mem_of_fixedPoints _ _ (T71_19 i) (hfix71_19 i) _)
      ⟨71, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 4 hp) Q2.T71_19_2 Q2.hfix71_19_2 Q2.hinj71_19_2
      Q2.hcardT71_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_19_2 i) (Q2.hfix71_19_2 i) _)
      colCert_71_19_4.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_19_5 (hp : 5 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 5 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp)) T71_19
      hfix71_19 hinj71_19 hcardT71_19
      (fun i => conj_mem_of_fixedPoints _ _ (T71_19 i) (hfix71_19 i) _)
      ⟨71, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 5 hp) Q2.T71_19_2 Q2.hfix71_19_2 Q2.hinj71_19_2
      Q2.hcardT71_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_19_2 i) (Q2.hfix71_19_2 i) _)
      colCert_71_19_5.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_19_10 (hp : 10 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 10 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp)) T71_19
      hfix71_19 hinj71_19 hcardT71_19
      (fun i => conj_mem_of_fixedPoints _ _ (T71_19 i) (hfix71_19 i) _)
      ⟨71, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 10 hp) Q2.T71_19_2 Q2.hfix71_19_2 Q2.hinj71_19_2
      Q2.hcardT71_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_19_2 i) (Q2.hfix71_19_2 i) _)
      colCert_71_19_10.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_19_15 (hp : 15 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 15 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp)) T71_19
      hfix71_19 hinj71_19 hcardT71_19
      (fun i => conj_mem_of_fixedPoints _ _ (T71_19 i) (hfix71_19 i) _)
      ⟨71, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 15 hp) Q2.T71_19_2 Q2.hfix71_19_2 Q2.hinj71_19_2
      Q2.hcardT71_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_19_2 i) (Q2.hfix71_19_2 i) _)
      colCert_71_19_15.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_19_20 (hp : 20 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 20 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp)) T71_19
      hfix71_19 hinj71_19 hcardT71_19
      (fun i => conj_mem_of_fixedPoints _ _ (T71_19 i) (hfix71_19 i) _)
      ⟨71, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 20 hp) Q2.T71_19_2 Q2.hfix71_19_2 Q2.hinj71_19_2
      Q2.hcardT71_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_19_2 i) (Q2.hfix71_19_2 i) _)
      colCert_71_19_20.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_31_0 (hp : 0 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 0 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp)) T71_31
      hfix71_31 hinj71_31 hcardT71_31
      (fun i => conj_mem_of_fixedPoints _ _ (T71_31 i) (hfix71_31 i) _)
      ⟨71, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 0 hp) Q2.T71_31_2 Q2.hfix71_31_2 Q2.hinj71_31_2
      Q2.hcardT71_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_31_2 i) (Q2.hfix71_31_2 i) _)
      colCert_71_31_0.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_31_1 (hp : 1 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 1 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp)) T71_31
      hfix71_31 hinj71_31 hcardT71_31
      (fun i => conj_mem_of_fixedPoints _ _ (T71_31 i) (hfix71_31 i) _)
      ⟨71, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 1 hp) Q2.T71_31_2 Q2.hfix71_31_2 Q2.hinj71_31_2
      Q2.hcardT71_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_31_2 i) (Q2.hfix71_31_2 i) _)
      colCert_71_31_1.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_31_2 (hp : 2 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 2 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp)) T71_31
      hfix71_31 hinj71_31 hcardT71_31
      (fun i => conj_mem_of_fixedPoints _ _ (T71_31 i) (hfix71_31 i) _)
      ⟨71, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 2 hp) Q2.T71_31_2 Q2.hfix71_31_2 Q2.hinj71_31_2
      Q2.hcardT71_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_31_2 i) (Q2.hfix71_31_2 i) _)
      colCert_71_31_2.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_31_3 (hp : 3 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 3 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp)) T71_31
      hfix71_31 hinj71_31 hcardT71_31
      (fun i => conj_mem_of_fixedPoints _ _ (T71_31 i) (hfix71_31 i) _)
      ⟨71, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 3 hp) Q2.T71_31_2 Q2.hfix71_31_2 Q2.hinj71_31_2
      Q2.hcardT71_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_31_2 i) (Q2.hfix71_31_2 i) _)
      colCert_71_31_3.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_31_4 (hp : 4 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 4 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp)) T71_31
      hfix71_31 hinj71_31 hcardT71_31
      (fun i => conj_mem_of_fixedPoints _ _ (T71_31 i) (hfix71_31 i) _)
      ⟨71, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 4 hp) Q2.T71_31_2 Q2.hfix71_31_2 Q2.hinj71_31_2
      Q2.hcardT71_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_31_2 i) (Q2.hfix71_31_2 i) _)
      colCert_71_31_4.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_31_5 (hp : 5 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 5 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp)) T71_31
      hfix71_31 hinj71_31 hcardT71_31
      (fun i => conj_mem_of_fixedPoints _ _ (T71_31 i) (hfix71_31 i) _)
      ⟨71, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 5 hp) Q2.T71_31_2 Q2.hfix71_31_2 Q2.hinj71_31_2
      Q2.hcardT71_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_31_2 i) (Q2.hfix71_31_2 i) _)
      colCert_71_31_5.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_31_10 (hp : 10 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 10 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp)) T71_31
      hfix71_31 hinj71_31 hcardT71_31
      (fun i => conj_mem_of_fixedPoints _ _ (T71_31 i) (hfix71_31 i) _)
      ⟨71, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 10 hp) Q2.T71_31_2 Q2.hfix71_31_2 Q2.hinj71_31_2
      Q2.hcardT71_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_31_2 i) (Q2.hfix71_31_2 i) _)
      colCert_71_31_10.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_31_15 (hp : 15 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 15 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp)) T71_31
      hfix71_31 hinj71_31 hcardT71_31
      (fun i => conj_mem_of_fixedPoints _ _ (T71_31 i) (hfix71_31 i) _)
      ⟨71, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 15 hp) Q2.T71_31_2 Q2.hfix71_31_2 Q2.hinj71_31_2
      Q2.hcardT71_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_31_2 i) (Q2.hfix71_31_2 i) _)
      colCert_71_31_15.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_31_20 (hp : 20 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 20 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp)) T71_31
      hfix71_31 hinj71_31 hcardT71_31
      (fun i => conj_mem_of_fixedPoints _ _ (T71_31 i) (hfix71_31 i) _)
      ⟨71, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 20 hp) Q2.T71_31_2 Q2.hfix71_31_2 Q2.hinj71_31_2
      Q2.hcardT71_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_31_2 i) (Q2.hfix71_31_2 i) _)
      colCert_71_31_20.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_36_0 (hp : 0 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 0 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp)) T71_36
      hfix71_36 hinj71_36 hcardT71_36
      (fun i => conj_mem_of_fixedPoints _ _ (T71_36 i) (hfix71_36 i) _)
      ⟨71, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 0 hp) Q2.T71_36_2 Q2.hfix71_36_2 Q2.hinj71_36_2
      Q2.hcardT71_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_36_2 i) (Q2.hfix71_36_2 i) _)
      colCert_71_36_0.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_36_1 (hp : 1 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 1 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp)) T71_36
      hfix71_36 hinj71_36 hcardT71_36
      (fun i => conj_mem_of_fixedPoints _ _ (T71_36 i) (hfix71_36 i) _)
      ⟨71, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 1 hp) Q2.T71_36_2 Q2.hfix71_36_2 Q2.hinj71_36_2
      Q2.hcardT71_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_36_2 i) (Q2.hfix71_36_2 i) _)
      colCert_71_36_1.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_36_2 (hp : 2 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 2 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp)) T71_36
      hfix71_36 hinj71_36 hcardT71_36
      (fun i => conj_mem_of_fixedPoints _ _ (T71_36 i) (hfix71_36 i) _)
      ⟨71, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 2 hp) Q2.T71_36_2 Q2.hfix71_36_2 Q2.hinj71_36_2
      Q2.hcardT71_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_36_2 i) (Q2.hfix71_36_2 i) _)
      colCert_71_36_2.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_36_3 (hp : 3 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 3 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp)) T71_36
      hfix71_36 hinj71_36 hcardT71_36
      (fun i => conj_mem_of_fixedPoints _ _ (T71_36 i) (hfix71_36 i) _)
      ⟨71, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 3 hp) Q2.T71_36_2 Q2.hfix71_36_2 Q2.hinj71_36_2
      Q2.hcardT71_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_36_2 i) (Q2.hfix71_36_2 i) _)
      colCert_71_36_3.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_36_4 (hp : 4 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 4 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp)) T71_36
      hfix71_36 hinj71_36 hcardT71_36
      (fun i => conj_mem_of_fixedPoints _ _ (T71_36 i) (hfix71_36 i) _)
      ⟨71, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 4 hp) Q2.T71_36_2 Q2.hfix71_36_2 Q2.hinj71_36_2
      Q2.hcardT71_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_36_2 i) (Q2.hfix71_36_2 i) _)
      colCert_71_36_4.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_36_5 (hp : 5 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 5 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp)) T71_36
      hfix71_36 hinj71_36 hcardT71_36
      (fun i => conj_mem_of_fixedPoints _ _ (T71_36 i) (hfix71_36 i) _)
      ⟨71, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 5 hp) Q2.T71_36_2 Q2.hfix71_36_2 Q2.hinj71_36_2
      Q2.hcardT71_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_36_2 i) (Q2.hfix71_36_2 i) _)
      colCert_71_36_5.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_36_10 (hp : 10 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 10 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp)) T71_36
      hfix71_36 hinj71_36 hcardT71_36
      (fun i => conj_mem_of_fixedPoints _ _ (T71_36 i) (hfix71_36 i) _)
      ⟨71, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 10 hp) Q2.T71_36_2 Q2.hfix71_36_2 Q2.hinj71_36_2
      Q2.hcardT71_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_36_2 i) (Q2.hfix71_36_2 i) _)
      colCert_71_36_10.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_36_15 (hp : 15 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 15 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp)) T71_36
      hfix71_36 hinj71_36 hcardT71_36
      (fun i => conj_mem_of_fixedPoints _ _ (T71_36 i) (hfix71_36 i) _)
      ⟨71, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 15 hp) Q2.T71_36_2 Q2.hfix71_36_2 Q2.hinj71_36_2
      Q2.hcardT71_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_36_2 i) (Q2.hfix71_36_2 i) _)
      colCert_71_36_15.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_36_20 (hp : 20 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 20 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp)) T71_36
      hfix71_36 hinj71_36 hcardT71_36
      (fun i => conj_mem_of_fixedPoints _ _ (T71_36 i) (hfix71_36 i) _)
      ⟨71, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 20 hp) Q2.T71_36_2 Q2.hfix71_36_2 Q2.hinj71_36_2
      Q2.hcardT71_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_36_2 i) (Q2.hfix71_36_2 i) _)
      colCert_71_36_20.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_41_0 (hp : 0 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 0 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp)) T71_41
      hfix71_41 hinj71_41 hcardT71_41
      (fun i => conj_mem_of_fixedPoints _ _ (T71_41 i) (hfix71_41 i) _)
      ⟨71, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 0 hp) Q2.T71_41_2 Q2.hfix71_41_2 Q2.hinj71_41_2
      Q2.hcardT71_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_41_2 i) (Q2.hfix71_41_2 i) _)
      colCert_71_41_0.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_41_1 (hp : 1 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 1 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp)) T71_41
      hfix71_41 hinj71_41 hcardT71_41
      (fun i => conj_mem_of_fixedPoints _ _ (T71_41 i) (hfix71_41 i) _)
      ⟨71, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 1 hp) Q2.T71_41_2 Q2.hfix71_41_2 Q2.hinj71_41_2
      Q2.hcardT71_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_41_2 i) (Q2.hfix71_41_2 i) _)
      colCert_71_41_1.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_41_2 (hp : 2 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 2 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp)) T71_41
      hfix71_41 hinj71_41 hcardT71_41
      (fun i => conj_mem_of_fixedPoints _ _ (T71_41 i) (hfix71_41 i) _)
      ⟨71, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 2 hp) Q2.T71_41_2 Q2.hfix71_41_2 Q2.hinj71_41_2
      Q2.hcardT71_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_41_2 i) (Q2.hfix71_41_2 i) _)
      colCert_71_41_2.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_41_3 (hp : 3 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 3 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp)) T71_41
      hfix71_41 hinj71_41 hcardT71_41
      (fun i => conj_mem_of_fixedPoints _ _ (T71_41 i) (hfix71_41 i) _)
      ⟨71, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 3 hp) Q2.T71_41_2 Q2.hfix71_41_2 Q2.hinj71_41_2
      Q2.hcardT71_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_41_2 i) (Q2.hfix71_41_2 i) _)
      colCert_71_41_3.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_41_4 (hp : 4 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 4 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp)) T71_41
      hfix71_41 hinj71_41 hcardT71_41
      (fun i => conj_mem_of_fixedPoints _ _ (T71_41 i) (hfix71_41 i) _)
      ⟨71, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 4 hp) Q2.T71_41_2 Q2.hfix71_41_2 Q2.hinj71_41_2
      Q2.hcardT71_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_41_2 i) (Q2.hfix71_41_2 i) _)
      colCert_71_41_4.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_41_5 (hp : 5 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 5 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp)) T71_41
      hfix71_41 hinj71_41 hcardT71_41
      (fun i => conj_mem_of_fixedPoints _ _ (T71_41 i) (hfix71_41 i) _)
      ⟨71, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 5 hp) Q2.T71_41_2 Q2.hfix71_41_2 Q2.hinj71_41_2
      Q2.hcardT71_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_41_2 i) (Q2.hfix71_41_2 i) _)
      colCert_71_41_5.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_41_10 (hp : 10 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 10 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp)) T71_41
      hfix71_41 hinj71_41 hcardT71_41
      (fun i => conj_mem_of_fixedPoints _ _ (T71_41 i) (hfix71_41 i) _)
      ⟨71, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 10 hp) Q2.T71_41_2 Q2.hfix71_41_2 Q2.hinj71_41_2
      Q2.hcardT71_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_41_2 i) (Q2.hfix71_41_2 i) _)
      colCert_71_41_10.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_41_15 (hp : 15 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 15 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp)) T71_41
      hfix71_41 hinj71_41 hcardT71_41
      (fun i => conj_mem_of_fixedPoints _ _ (T71_41 i) (hfix71_41 i) _)
      ⟨71, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 15 hp) Q2.T71_41_2 Q2.hfix71_41_2 Q2.hinj71_41_2
      Q2.hcardT71_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_41_2 i) (Q2.hfix71_41_2 i) _)
      colCert_71_41_15.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_41_20 (hp : 20 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 20 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp)) T71_41
      hfix71_41 hinj71_41 hcardT71_41
      (fun i => conj_mem_of_fixedPoints _ _ (T71_41 i) (hfix71_41 i) _)
      ⟨71, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 20 hp) Q2.T71_41_2 Q2.hfix71_41_2 Q2.hinj71_41_2
      Q2.hcardT71_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_41_2 i) (Q2.hfix71_41_2 i) _)
      colCert_71_41_20.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_46_0 (hp : 0 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 0 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp)) T71_46
      hfix71_46 hinj71_46 hcardT71_46
      (fun i => conj_mem_of_fixedPoints _ _ (T71_46 i) (hfix71_46 i) _)
      ⟨71, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 0 hp) Q2.T71_46_2 Q2.hfix71_46_2 Q2.hinj71_46_2
      Q2.hcardT71_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_46_2 i) (Q2.hfix71_46_2 i) _)
      colCert_71_46_0.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_46_1 (hp : 1 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 1 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp)) T71_46
      hfix71_46 hinj71_46 hcardT71_46
      (fun i => conj_mem_of_fixedPoints _ _ (T71_46 i) (hfix71_46 i) _)
      ⟨71, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 1 hp) Q2.T71_46_2 Q2.hfix71_46_2 Q2.hinj71_46_2
      Q2.hcardT71_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_46_2 i) (Q2.hfix71_46_2 i) _)
      colCert_71_46_1.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_46_2 (hp : 2 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 2 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp)) T71_46
      hfix71_46 hinj71_46 hcardT71_46
      (fun i => conj_mem_of_fixedPoints _ _ (T71_46 i) (hfix71_46 i) _)
      ⟨71, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 2 hp) Q2.T71_46_2 Q2.hfix71_46_2 Q2.hinj71_46_2
      Q2.hcardT71_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_46_2 i) (Q2.hfix71_46_2 i) _)
      colCert_71_46_2.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_46_3 (hp : 3 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 3 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp)) T71_46
      hfix71_46 hinj71_46 hcardT71_46
      (fun i => conj_mem_of_fixedPoints _ _ (T71_46 i) (hfix71_46 i) _)
      ⟨71, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 3 hp) Q2.T71_46_2 Q2.hfix71_46_2 Q2.hinj71_46_2
      Q2.hcardT71_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_46_2 i) (Q2.hfix71_46_2 i) _)
      colCert_71_46_3.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_46_4 (hp : 4 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 4 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp)) T71_46
      hfix71_46 hinj71_46 hcardT71_46
      (fun i => conj_mem_of_fixedPoints _ _ (T71_46 i) (hfix71_46 i) _)
      ⟨71, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 4 hp) Q2.T71_46_2 Q2.hfix71_46_2 Q2.hinj71_46_2
      Q2.hcardT71_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_46_2 i) (Q2.hfix71_46_2 i) _)
      colCert_71_46_4.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_46_5 (hp : 5 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 5 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp)) T71_46
      hfix71_46 hinj71_46 hcardT71_46
      (fun i => conj_mem_of_fixedPoints _ _ (T71_46 i) (hfix71_46 i) _)
      ⟨71, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 5 hp) Q2.T71_46_2 Q2.hfix71_46_2 Q2.hinj71_46_2
      Q2.hcardT71_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_46_2 i) (Q2.hfix71_46_2 i) _)
      colCert_71_46_5.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_46_10 (hp : 10 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 10 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp)) T71_46
      hfix71_46 hinj71_46 hcardT71_46
      (fun i => conj_mem_of_fixedPoints _ _ (T71_46 i) (hfix71_46 i) _)
      ⟨71, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 10 hp) Q2.T71_46_2 Q2.hfix71_46_2 Q2.hinj71_46_2
      Q2.hcardT71_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_46_2 i) (Q2.hfix71_46_2 i) _)
      colCert_71_46_10.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_46_15 (hp : 15 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 15 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp)) T71_46
      hfix71_46 hinj71_46 hcardT71_46
      (fun i => conj_mem_of_fixedPoints _ _ (T71_46 i) (hfix71_46 i) _)
      ⟨71, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 15 hp) Q2.T71_46_2 Q2.hfix71_46_2 Q2.hinj71_46_2
      Q2.hcardT71_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_46_2 i) (Q2.hfix71_46_2 i) _)
      colCert_71_46_15.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_46_20 (hp : 20 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 20 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp)) T71_46
      hfix71_46 hinj71_46 hcardT71_46
      (fun i => conj_mem_of_fixedPoints _ _ (T71_46 i) (hfix71_46 i) _)
      ⟨71, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 20 hp) Q2.T71_46_2 Q2.hfix71_46_2 Q2.hinj71_46_2
      Q2.hcardT71_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_46_2 i) (Q2.hfix71_46_2 i) _)
      colCert_71_46_20.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_51_0 (hp : 0 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 0 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp)) T71_51
      hfix71_51 hinj71_51 hcardT71_51
      (fun i => conj_mem_of_fixedPoints _ _ (T71_51 i) (hfix71_51 i) _)
      ⟨71, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 0 hp) Q2.T71_51_2 Q2.hfix71_51_2 Q2.hinj71_51_2
      Q2.hcardT71_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_51_2 i) (Q2.hfix71_51_2 i) _)
      colCert_71_51_0.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_51_1 (hp : 1 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 1 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp)) T71_51
      hfix71_51 hinj71_51 hcardT71_51
      (fun i => conj_mem_of_fixedPoints _ _ (T71_51 i) (hfix71_51 i) _)
      ⟨71, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 1 hp) Q2.T71_51_2 Q2.hfix71_51_2 Q2.hinj71_51_2
      Q2.hcardT71_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_51_2 i) (Q2.hfix71_51_2 i) _)
      colCert_71_51_1.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_51_2 (hp : 2 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 2 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp)) T71_51
      hfix71_51 hinj71_51 hcardT71_51
      (fun i => conj_mem_of_fixedPoints _ _ (T71_51 i) (hfix71_51 i) _)
      ⟨71, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 2 hp) Q2.T71_51_2 Q2.hfix71_51_2 Q2.hinj71_51_2
      Q2.hcardT71_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_51_2 i) (Q2.hfix71_51_2 i) _)
      colCert_71_51_2.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_51_3 (hp : 3 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 3 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp)) T71_51
      hfix71_51 hinj71_51 hcardT71_51
      (fun i => conj_mem_of_fixedPoints _ _ (T71_51 i) (hfix71_51 i) _)
      ⟨71, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 3 hp) Q2.T71_51_2 Q2.hfix71_51_2 Q2.hinj71_51_2
      Q2.hcardT71_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_51_2 i) (Q2.hfix71_51_2 i) _)
      colCert_71_51_3.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_51_4 (hp : 4 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 4 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp)) T71_51
      hfix71_51 hinj71_51 hcardT71_51
      (fun i => conj_mem_of_fixedPoints _ _ (T71_51 i) (hfix71_51 i) _)
      ⟨71, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 4 hp) Q2.T71_51_2 Q2.hfix71_51_2 Q2.hinj71_51_2
      Q2.hcardT71_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_51_2 i) (Q2.hfix71_51_2 i) _)
      colCert_71_51_4.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_51_5 (hp : 5 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 5 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp)) T71_51
      hfix71_51 hinj71_51 hcardT71_51
      (fun i => conj_mem_of_fixedPoints _ _ (T71_51 i) (hfix71_51 i) _)
      ⟨71, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 5 hp) Q2.T71_51_2 Q2.hfix71_51_2 Q2.hinj71_51_2
      Q2.hcardT71_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_51_2 i) (Q2.hfix71_51_2 i) _)
      colCert_71_51_5.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_51_10 (hp : 10 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 10 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp)) T71_51
      hfix71_51 hinj71_51 hcardT71_51
      (fun i => conj_mem_of_fixedPoints _ _ (T71_51 i) (hfix71_51 i) _)
      ⟨71, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 10 hp) Q2.T71_51_2 Q2.hfix71_51_2 Q2.hinj71_51_2
      Q2.hcardT71_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_51_2 i) (Q2.hfix71_51_2 i) _)
      colCert_71_51_10.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_51_15 (hp : 15 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 15 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp)) T71_51
      hfix71_51 hinj71_51 hcardT71_51
      (fun i => conj_mem_of_fixedPoints _ _ (T71_51 i) (hfix71_51 i) _)
      ⟨71, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 15 hp) Q2.T71_51_2 Q2.hfix71_51_2 Q2.hinj71_51_2
      Q2.hcardT71_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_51_2 i) (Q2.hfix71_51_2 i) _)
      colCert_71_51_15.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_51_20 (hp : 20 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 20 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp)) T71_51
      hfix71_51 hinj71_51 hcardT71_51
      (fun i => conj_mem_of_fixedPoints _ _ (T71_51 i) (hfix71_51 i) _)
      ⟨71, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 20 hp) Q2.T71_51_2 Q2.hfix71_51_2 Q2.hinj71_51_2
      Q2.hcardT71_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_51_2 i) (Q2.hfix71_51_2 i) _)
      colCert_71_51_20.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_71_0 (hp : 0 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 0 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 0 (transLenTr ⟨71, by decide⟩ 0 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 0 (transLenTr ⟨71, by decide⟩ 0 hp)) T71_71
      hfix71_71 hinj71_71 hcardT71_71
      (fun i => conj_mem_of_fixedPoints _ _ (T71_71 i) (hfix71_71 i) _)
      ⟨71, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 0 hp) Q2.T71_71_2 Q2.hfix71_71_2 Q2.hinj71_71_2
      Q2.hcardT71_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_71_2 i) (Q2.hfix71_71_2 i) _)
      colCert_71_71_0.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_71_1 (hp : 1 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 1 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 1 (transLenTr ⟨71, by decide⟩ 1 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 1 (transLenTr ⟨71, by decide⟩ 1 hp)) T71_71
      hfix71_71 hinj71_71 hcardT71_71
      (fun i => conj_mem_of_fixedPoints _ _ (T71_71 i) (hfix71_71 i) _)
      ⟨71, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 1 hp) Q2.T71_71_2 Q2.hfix71_71_2 Q2.hinj71_71_2
      Q2.hcardT71_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_71_2 i) (Q2.hfix71_71_2 i) _)
      colCert_71_71_1.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_71_2 (hp : 2 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 2 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 2 (transLenTr ⟨71, by decide⟩ 2 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 2 (transLenTr ⟨71, by decide⟩ 2 hp)) T71_71
      hfix71_71 hinj71_71 hcardT71_71
      (fun i => conj_mem_of_fixedPoints _ _ (T71_71 i) (hfix71_71 i) _)
      ⟨71, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 2 hp) Q2.T71_71_2 Q2.hfix71_71_2 Q2.hinj71_71_2
      Q2.hcardT71_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_71_2 i) (Q2.hfix71_71_2 i) _)
      colCert_71_71_2.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_71_3 (hp : 3 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 3 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 3 (transLenTr ⟨71, by decide⟩ 3 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 3 (transLenTr ⟨71, by decide⟩ 3 hp)) T71_71
      hfix71_71 hinj71_71 hcardT71_71
      (fun i => conj_mem_of_fixedPoints _ _ (T71_71 i) (hfix71_71 i) _)
      ⟨71, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 3 hp) Q2.T71_71_2 Q2.hfix71_71_2 Q2.hinj71_71_2
      Q2.hcardT71_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_71_2 i) (Q2.hfix71_71_2 i) _)
      colCert_71_71_3.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_71_4 (hp : 4 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 4 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 4 (transLenTr ⟨71, by decide⟩ 4 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 4 (transLenTr ⟨71, by decide⟩ 4 hp)) T71_71
      hfix71_71 hinj71_71 hcardT71_71
      (fun i => conj_mem_of_fixedPoints _ _ (T71_71 i) (hfix71_71 i) _)
      ⟨71, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 4 hp) Q2.T71_71_2 Q2.hfix71_71_2 Q2.hinj71_71_2
      Q2.hcardT71_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_71_2 i) (Q2.hfix71_71_2 i) _)
      colCert_71_71_4.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_71_5 (hp : 5 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 5 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 5 (transLenTr ⟨71, by decide⟩ 5 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 5 (transLenTr ⟨71, by decide⟩ 5 hp)) T71_71
      hfix71_71 hinj71_71 hcardT71_71
      (fun i => conj_mem_of_fixedPoints _ _ (T71_71 i) (hfix71_71 i) _)
      ⟨71, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 5 hp) Q2.T71_71_2 Q2.hfix71_71_2 Q2.hinj71_71_2
      Q2.hcardT71_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_71_2 i) (Q2.hfix71_71_2 i) _)
      colCert_71_71_5.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_71_6 (hp : 6 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 6 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 6 (transLenTr ⟨71, by decide⟩ 6 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 6 (transLenTr ⟨71, by decide⟩ 6 hp)) T71_71
      hfix71_71 hinj71_71 hcardT71_71
      (fun i => conj_mem_of_fixedPoints _ _ (T71_71 i) (hfix71_71 i) _)
      ⟨71, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 6 hp) Q2.T71_71_2 Q2.hfix71_71_2 Q2.hinj71_71_2
      Q2.hcardT71_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_71_2 i) (Q2.hfix71_71_2 i) _)
      colCert_71_71_6.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_71_7 (hp : 7 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 7 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 7 (transLenTr ⟨71, by decide⟩ 7 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 7 (transLenTr ⟨71, by decide⟩ 7 hp)) T71_71
      hfix71_71 hinj71_71 hcardT71_71
      (fun i => conj_mem_of_fixedPoints _ _ (T71_71 i) (hfix71_71 i) _)
      ⟨71, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 7 hp) Q2.T71_71_2 Q2.hfix71_71_2 Q2.hinj71_71_2
      Q2.hcardT71_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_71_2 i) (Q2.hfix71_71_2 i) _)
      colCert_71_71_7.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_71_8 (hp : 8 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 8 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 8 (transLenTr ⟨71, by decide⟩ 8 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 8 (transLenTr ⟨71, by decide⟩ 8 hp)) T71_71
      hfix71_71 hinj71_71 hcardT71_71
      (fun i => conj_mem_of_fixedPoints _ _ (T71_71 i) (hfix71_71 i) _)
      ⟨71, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 8 hp) Q2.T71_71_2 Q2.hfix71_71_2 Q2.hinj71_71_2
      Q2.hcardT71_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_71_2 i) (Q2.hfix71_71_2 i) _)
      colCert_71_71_8.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_71_9 (hp : 9 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 9 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 9 (transLenTr ⟨71, by decide⟩ 9 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 9 (transLenTr ⟨71, by decide⟩ 9 hp)) T71_71
      hfix71_71 hinj71_71 hcardT71_71
      (fun i => conj_mem_of_fixedPoints _ _ (T71_71 i) (hfix71_71 i) _)
      ⟨71, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 9 hp) Q2.T71_71_2 Q2.hfix71_71_2 Q2.hinj71_71_2
      Q2.hcardT71_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_71_2 i) (Q2.hfix71_71_2 i) _)
      colCert_71_71_9.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_71_10 (hp : 10 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 10 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 10 (transLenTr ⟨71, by decide⟩ 10 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 10 (transLenTr ⟨71, by decide⟩ 10 hp)) T71_71
      hfix71_71 hinj71_71 hcardT71_71
      (fun i => conj_mem_of_fixedPoints _ _ (T71_71 i) (hfix71_71 i) _)
      ⟨71, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 10 hp) Q2.T71_71_2 Q2.hfix71_71_2 Q2.hinj71_71_2
      Q2.hcardT71_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_71_2 i) (Q2.hfix71_71_2 i) _)
      colCert_71_71_10.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_71_11 (hp : 11 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 11 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 11 (transLenTr ⟨71, by decide⟩ 11 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 11 (transLenTr ⟨71, by decide⟩ 11 hp)) T71_71
      hfix71_71 hinj71_71 hcardT71_71
      (fun i => conj_mem_of_fixedPoints _ _ (T71_71 i) (hfix71_71 i) _)
      ⟨71, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 11 hp) Q2.T71_71_2 Q2.hfix71_71_2 Q2.hinj71_71_2
      Q2.hcardT71_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_71_2 i) (Q2.hfix71_71_2 i) _)
      colCert_71_71_11.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_71_12 (hp : 12 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 12 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 12 (transLenTr ⟨71, by decide⟩ 12 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 12 (transLenTr ⟨71, by decide⟩ 12 hp)) T71_71
      hfix71_71 hinj71_71 hcardT71_71
      (fun i => conj_mem_of_fixedPoints _ _ (T71_71 i) (hfix71_71 i) _)
      ⟨71, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 12 hp) Q2.T71_71_2 Q2.hfix71_71_2 Q2.hinj71_71_2
      Q2.hcardT71_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_71_2 i) (Q2.hfix71_71_2 i) _)
      colCert_71_71_12.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_71_13 (hp : 13 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 13 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 13 (transLenTr ⟨71, by decide⟩ 13 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 13 (transLenTr ⟨71, by decide⟩ 13 hp)) T71_71
      hfix71_71 hinj71_71 hcardT71_71
      (fun i => conj_mem_of_fixedPoints _ _ (T71_71 i) (hfix71_71 i) _)
      ⟨71, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 13 hp) Q2.T71_71_2 Q2.hfix71_71_2 Q2.hinj71_71_2
      Q2.hcardT71_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_71_2 i) (Q2.hfix71_71_2 i) _)
      colCert_71_71_13.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_71_14 (hp : 14 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 14 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 14 (transLenTr ⟨71, by decide⟩ 14 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 14 (transLenTr ⟨71, by decide⟩ 14 hp)) T71_71
      hfix71_71 hinj71_71 hcardT71_71
      (fun i => conj_mem_of_fixedPoints _ _ (T71_71 i) (hfix71_71 i) _)
      ⟨71, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 14 hp) Q2.T71_71_2 Q2.hfix71_71_2 Q2.hinj71_71_2
      Q2.hcardT71_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_71_2 i) (Q2.hfix71_71_2 i) _)
      colCert_71_71_14.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_71_15 (hp : 15 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 15 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 15 (transLenTr ⟨71, by decide⟩ 15 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 15 (transLenTr ⟨71, by decide⟩ 15 hp)) T71_71
      hfix71_71 hinj71_71 hcardT71_71
      (fun i => conj_mem_of_fixedPoints _ _ (T71_71 i) (hfix71_71 i) _)
      ⟨71, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 15 hp) Q2.T71_71_2 Q2.hfix71_71_2 Q2.hinj71_71_2
      Q2.hcardT71_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_71_2 i) (Q2.hfix71_71_2 i) _)
      colCert_71_71_15.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_71_16 (hp : 16 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 16 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 16 (transLenTr ⟨71, by decide⟩ 16 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 16 (transLenTr ⟨71, by decide⟩ 16 hp)) T71_71
      hfix71_71 hinj71_71 hcardT71_71
      (fun i => conj_mem_of_fixedPoints _ _ (T71_71 i) (hfix71_71 i) _)
      ⟨71, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 16 hp) Q2.T71_71_2 Q2.hfix71_71_2 Q2.hinj71_71_2
      Q2.hcardT71_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_71_2 i) (Q2.hfix71_71_2 i) _)
      colCert_71_71_16.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_71_17 (hp : 17 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 17 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 17 (transLenTr ⟨71, by decide⟩ 17 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 17 (transLenTr ⟨71, by decide⟩ 17 hp)) T71_71
      hfix71_71 hinj71_71 hcardT71_71
      (fun i => conj_mem_of_fixedPoints _ _ (T71_71 i) (hfix71_71 i) _)
      ⟨71, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 17 hp) Q2.T71_71_2 Q2.hfix71_71_2 Q2.hinj71_71_2
      Q2.hcardT71_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_71_2 i) (Q2.hfix71_71_2 i) _)
      colCert_71_71_17.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_71_18 (hp : 18 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 18 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 18 (transLenTr ⟨71, by decide⟩ 18 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 18 (transLenTr ⟨71, by decide⟩ 18 hp)) T71_71
      hfix71_71 hinj71_71 hcardT71_71
      (fun i => conj_mem_of_fixedPoints _ _ (T71_71 i) (hfix71_71 i) _)
      ⟨71, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 18 hp) Q2.T71_71_2 Q2.hfix71_71_2 Q2.hinj71_71_2
      Q2.hcardT71_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_71_2 i) (Q2.hfix71_71_2 i) _)
      colCert_71_71_18.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_71_19 (hp : 19 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 19 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 19 (transLenTr ⟨71, by decide⟩ 19 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 19 (transLenTr ⟨71, by decide⟩ 19 hp)) T71_71
      hfix71_71 hinj71_71 hcardT71_71
      (fun i => conj_mem_of_fixedPoints _ _ (T71_71 i) (hfix71_71 i) _)
      ⟨71, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 19 hp) Q2.T71_71_2 Q2.hfix71_71_2 Q2.hinj71_71_2
      Q2.hcardT71_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_71_2 i) (Q2.hfix71_71_2 i) _)
      colCert_71_71_19.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_71_20 (hp : 20 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 20 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 20 (transLenTr ⟨71, by decide⟩ 20 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 20 (transLenTr ⟨71, by decide⟩ 20 hp)) T71_71
      hfix71_71 hinj71_71 hcardT71_71
      (fun i => conj_mem_of_fixedPoints _ _ (T71_71 i) (hfix71_71 i) _)
      ⟨71, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 20 hp) Q2.T71_71_2 Q2.hfix71_71_2 Q2.hinj71_71_2
      Q2.hcardT71_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_71_2 i) (Q2.hfix71_71_2 i) _)
      colCert_71_71_20.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_71_21 (hp : 21 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 21 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 21 (transLenTr ⟨71, by decide⟩ 21 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 21 (transLenTr ⟨71, by decide⟩ 21 hp)) T71_71
      hfix71_71 hinj71_71 hcardT71_71
      (fun i => conj_mem_of_fixedPoints _ _ (T71_71 i) (hfix71_71 i) _)
      ⟨71, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 21 hp) Q2.T71_71_2 Q2.hfix71_71_2 Q2.hinj71_71_2
      Q2.hcardT71_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_71_2 i) (Q2.hfix71_71_2 i) _)
      colCert_71_71_21.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_71_22 (hp : 22 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 22 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 22 (transLenTr ⟨71, by decide⟩ 22 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 22 (transLenTr ⟨71, by decide⟩ 22 hp)) T71_71
      hfix71_71 hinj71_71 hcardT71_71
      (fun i => conj_mem_of_fixedPoints _ _ (T71_71 i) (hfix71_71 i) _)
      ⟨71, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 22 hp) Q2.T71_71_2 Q2.hfix71_71_2 Q2.hinj71_71_2
      Q2.hcardT71_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_71_2 i) (Q2.hfix71_71_2 i) _)
      colCert_71_71_22.hD ?_).symm
  rw [alnId_71 j hj]


end LeanDring.P5Presentation
