/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C017
import LeanDring.P5.Data.ColCdd.C018
import LeanDring.P5.Data.ColRestCheap.C077
import LeanDring.P5.Data.ColRestCheap.C078
import LeanDring.P5.Data.ColRestCheap.C079
import LeanDring.P5.Data.ColRestCheap.C080
import LeanDring.P5.Data.EntryK.C036
import LeanDring.P5.Data.EntryK.C037
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C023
import LeanDring.P5.Data.SpeciesDiv.C024

/-! # Stage-5 leaves, chunk 39 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_135_103_5 (hp : 5 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 5 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 5 (transLenTr ⟨103, by decide⟩ 5 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 5 (transLenTr ⟨103, by decide⟩ 5 hp)) T135_103
      hfix135_103 hinj135_103 hcardT135_103
      (fun i => conj_mem_of_fixedPoints _ _ (T135_103 i) (hfix135_103 i) _)
      ⟨135, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 5 hp) Q2.T135_103_2 Q2.hfix135_103_2 Q2.hinj135_103_2
      Q2.hcardT135_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_103_2 i) (Q2.hfix135_103_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨103, by decide⟩ 5 (transLenTr ⟨103, by decide⟩ 5 hp) : ↥(reps ⟨103, by decide⟩)) : Coordinate 1)
        T135_103 = colFn colCertDiv_135_103_5.D1 (m := 5) from colCertDiv_135_103_5.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨103, by decide⟩ 5 hp : ↥(Q2.reps ⟨103, by decide⟩)) : Coordinate 2)
        Q2.T135_103_2 = colFn colCertDiv_135_103_5.D2 (m := 5) from colCertDiv_135_103_5.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_103_5_match


theorem leaf_135_103_10 (hp : 10 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 10 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 10 (transLenTr ⟨103, by decide⟩ 10 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 10 (transLenTr ⟨103, by decide⟩ 10 hp)) T135_103
      hfix135_103 hinj135_103 hcardT135_103
      (fun i => conj_mem_of_fixedPoints _ _ (T135_103 i) (hfix135_103 i) _)
      ⟨135, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 10 hp) Q2.T135_103_2 Q2.hfix135_103_2 Q2.hinj135_103_2
      Q2.hcardT135_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_103_2 i) (Q2.hfix135_103_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨103, by decide⟩ 10 (transLenTr ⟨103, by decide⟩ 10 hp) : ↥(reps ⟨103, by decide⟩)) : Coordinate 1)
        T135_103 = colFn colCertDiv_135_103_10.D1 (m := 5) from colCertDiv_135_103_10.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨103, by decide⟩ 10 hp : ↥(Q2.reps ⟨103, by decide⟩)) : Coordinate 2)
        Q2.T135_103_2 = colFn colCertDiv_135_103_10.D2 (m := 5) from colCertDiv_135_103_10.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_103_10_match


theorem leaf_135_103_15 (hp : 15 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 15 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 15 (transLenTr ⟨103, by decide⟩ 15 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 15 (transLenTr ⟨103, by decide⟩ 15 hp)) T135_103
      hfix135_103 hinj135_103 hcardT135_103
      (fun i => conj_mem_of_fixedPoints _ _ (T135_103 i) (hfix135_103 i) _)
      ⟨135, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 15 hp) Q2.T135_103_2 Q2.hfix135_103_2 Q2.hinj135_103_2
      Q2.hcardT135_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_103_2 i) (Q2.hfix135_103_2 i) _)
      colCert_135_103_15.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_103_20 (hp : 20 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 20 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 20 (transLenTr ⟨103, by decide⟩ 20 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 20 (transLenTr ⟨103, by decide⟩ 20 hp)) T135_103
      hfix135_103 hinj135_103 hcardT135_103
      (fun i => conj_mem_of_fixedPoints _ _ (T135_103 i) (hfix135_103 i) _)
      ⟨135, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 20 hp) Q2.T135_103_2 Q2.hfix135_103_2 Q2.hinj135_103_2
      Q2.hcardT135_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_103_2 i) (Q2.hfix135_103_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨103, by decide⟩ 20 (transLenTr ⟨103, by decide⟩ 20 hp) : ↥(reps ⟨103, by decide⟩)) : Coordinate 1)
        T135_103 = colFn colCertDiv_135_103_20.D1 (m := 5) from colCertDiv_135_103_20.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨103, by decide⟩ 20 hp : ↥(Q2.reps ⟨103, by decide⟩)) : Coordinate 2)
        Q2.T135_103_2 = colFn colCertDiv_135_103_20.D2 (m := 5) from colCertDiv_135_103_20.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_103_20_match


theorem leaf_135_107_0 (hp : 0 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 0 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 0 (transLenTr ⟨107, by decide⟩ 0 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 0 (transLenTr ⟨107, by decide⟩ 0 hp)) T135_107
      hfix135_107 hinj135_107 hcardT135_107
      (fun i => conj_mem_of_fixedPoints _ _ (T135_107 i) (hfix135_107 i) _)
      ⟨135, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 0 hp) Q2.T135_107_2 Q2.hfix135_107_2 Q2.hinj135_107_2
      Q2.hcardT135_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_107_2 i) (Q2.hfix135_107_2 i) _)
      colCert_135_107_0.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_107_1 (hp : 1 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 1 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 1 (transLenTr ⟨107, by decide⟩ 1 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 1 (transLenTr ⟨107, by decide⟩ 1 hp)) T135_107
      hfix135_107 hinj135_107 hcardT135_107
      (fun i => conj_mem_of_fixedPoints _ _ (T135_107 i) (hfix135_107 i) _)
      ⟨135, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 1 hp) Q2.T135_107_2 Q2.hfix135_107_2 Q2.hinj135_107_2
      Q2.hcardT135_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_107_2 i) (Q2.hfix135_107_2 i) _)
      colCert_135_107_1.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_107_2 (hp : 2 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 2 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 2 (transLenTr ⟨107, by decide⟩ 2 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 2 (transLenTr ⟨107, by decide⟩ 2 hp)) T135_107
      hfix135_107 hinj135_107 hcardT135_107
      (fun i => conj_mem_of_fixedPoints _ _ (T135_107 i) (hfix135_107 i) _)
      ⟨135, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 2 hp) Q2.T135_107_2 Q2.hfix135_107_2 Q2.hinj135_107_2
      Q2.hcardT135_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_107_2 i) (Q2.hfix135_107_2 i) _)
      colCert_135_107_2.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_107_3 (hp : 3 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 3 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 3 (transLenTr ⟨107, by decide⟩ 3 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 3 (transLenTr ⟨107, by decide⟩ 3 hp)) T135_107
      hfix135_107 hinj135_107 hcardT135_107
      (fun i => conj_mem_of_fixedPoints _ _ (T135_107 i) (hfix135_107 i) _)
      ⟨135, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 3 hp) Q2.T135_107_2 Q2.hfix135_107_2 Q2.hinj135_107_2
      Q2.hcardT135_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_107_2 i) (Q2.hfix135_107_2 i) _)
      colCert_135_107_3.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_107_4 (hp : 4 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 4 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 4 (transLenTr ⟨107, by decide⟩ 4 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 4 (transLenTr ⟨107, by decide⟩ 4 hp)) T135_107
      hfix135_107 hinj135_107 hcardT135_107
      (fun i => conj_mem_of_fixedPoints _ _ (T135_107 i) (hfix135_107 i) _)
      ⟨135, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 4 hp) Q2.T135_107_2 Q2.hfix135_107_2 Q2.hinj135_107_2
      Q2.hcardT135_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_107_2 i) (Q2.hfix135_107_2 i) _)
      colCert_135_107_4.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_107_5 (hp : 5 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 5 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 5 (transLenTr ⟨107, by decide⟩ 5 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 5 (transLenTr ⟨107, by decide⟩ 5 hp)) T135_107
      hfix135_107 hinj135_107 hcardT135_107
      (fun i => conj_mem_of_fixedPoints _ _ (T135_107 i) (hfix135_107 i) _)
      ⟨135, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 5 hp) Q2.T135_107_2 Q2.hfix135_107_2 Q2.hinj135_107_2
      Q2.hcardT135_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_107_2 i) (Q2.hfix135_107_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨107, by decide⟩ 5 (transLenTr ⟨107, by decide⟩ 5 hp) : ↥(reps ⟨107, by decide⟩)) : Coordinate 1)
        T135_107 = colFn colCertDiv_135_107_5.D1 (m := 5) from colCertDiv_135_107_5.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨107, by decide⟩ 5 hp : ↥(Q2.reps ⟨107, by decide⟩)) : Coordinate 2)
        Q2.T135_107_2 = colFn colCertDiv_135_107_5.D2 (m := 5) from colCertDiv_135_107_5.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_107_5_match


theorem leaf_135_107_10 (hp : 10 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 10 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 10 (transLenTr ⟨107, by decide⟩ 10 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 10 (transLenTr ⟨107, by decide⟩ 10 hp)) T135_107
      hfix135_107 hinj135_107 hcardT135_107
      (fun i => conj_mem_of_fixedPoints _ _ (T135_107 i) (hfix135_107 i) _)
      ⟨135, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 10 hp) Q2.T135_107_2 Q2.hfix135_107_2 Q2.hinj135_107_2
      Q2.hcardT135_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_107_2 i) (Q2.hfix135_107_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨107, by decide⟩ 10 (transLenTr ⟨107, by decide⟩ 10 hp) : ↥(reps ⟨107, by decide⟩)) : Coordinate 1)
        T135_107 = colFn colCertDiv_135_107_10.D1 (m := 5) from colCertDiv_135_107_10.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨107, by decide⟩ 10 hp : ↥(Q2.reps ⟨107, by decide⟩)) : Coordinate 2)
        Q2.T135_107_2 = colFn colCertDiv_135_107_10.D2 (m := 5) from colCertDiv_135_107_10.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_107_10_match


theorem leaf_135_107_15 (hp : 15 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 15 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 15 (transLenTr ⟨107, by decide⟩ 15 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 15 (transLenTr ⟨107, by decide⟩ 15 hp)) T135_107
      hfix135_107 hinj135_107 hcardT135_107
      (fun i => conj_mem_of_fixedPoints _ _ (T135_107 i) (hfix135_107 i) _)
      ⟨135, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 15 hp) Q2.T135_107_2 Q2.hfix135_107_2 Q2.hinj135_107_2
      Q2.hcardT135_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_107_2 i) (Q2.hfix135_107_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨107, by decide⟩ 15 (transLenTr ⟨107, by decide⟩ 15 hp) : ↥(reps ⟨107, by decide⟩)) : Coordinate 1)
        T135_107 = colFn colCertDiv_135_107_15.D1 (m := 5) from colCertDiv_135_107_15.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨107, by decide⟩ 15 hp : ↥(Q2.reps ⟨107, by decide⟩)) : Coordinate 2)
        Q2.T135_107_2 = colFn colCertDiv_135_107_15.D2 (m := 5) from colCertDiv_135_107_15.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_107_15_match


theorem leaf_135_107_20 (hp : 20 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 20 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 20 (transLenTr ⟨107, by decide⟩ 20 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 20 (transLenTr ⟨107, by decide⟩ 20 hp)) T135_107
      hfix135_107 hinj135_107 hcardT135_107
      (fun i => conj_mem_of_fixedPoints _ _ (T135_107 i) (hfix135_107 i) _)
      ⟨135, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 20 hp) Q2.T135_107_2 Q2.hfix135_107_2 Q2.hinj135_107_2
      Q2.hcardT135_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_107_2 i) (Q2.hfix135_107_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨107, by decide⟩ 20 (transLenTr ⟨107, by decide⟩ 20 hp) : ↥(reps ⟨107, by decide⟩)) : Coordinate 1)
        T135_107 = colFn colCertDiv_135_107_20.D1 (m := 5) from colCertDiv_135_107_20.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨107, by decide⟩ 20 hp : ↥(Q2.reps ⟨107, by decide⟩)) : Coordinate 2)
        Q2.T135_107_2 = colFn colCertDiv_135_107_20.D2 (m := 5) from colCertDiv_135_107_20.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_107_20_match


theorem leaf_135_114_0 (hp : 0 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 0 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 0 (transLenTr ⟨114, by decide⟩ 0 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 0 (transLenTr ⟨114, by decide⟩ 0 hp)) T135_114
      hfix135_114 hinj135_114 hcardT135_114
      (fun i => conj_mem_of_fixedPoints _ _ (T135_114 i) (hfix135_114 i) _)
      ⟨135, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 0 hp) Q2.T135_114_2 Q2.hfix135_114_2 Q2.hinj135_114_2
      Q2.hcardT135_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_114_2 i) (Q2.hfix135_114_2 i) _)
      colCert_135_114_0.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_114_1 (hp : 1 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 1 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 1 (transLenTr ⟨114, by decide⟩ 1 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 1 (transLenTr ⟨114, by decide⟩ 1 hp)) T135_114
      hfix135_114 hinj135_114 hcardT135_114
      (fun i => conj_mem_of_fixedPoints _ _ (T135_114 i) (hfix135_114 i) _)
      ⟨135, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 1 hp) Q2.T135_114_2 Q2.hfix135_114_2 Q2.hinj135_114_2
      Q2.hcardT135_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_114_2 i) (Q2.hfix135_114_2 i) _)
      colCert_135_114_1.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_114_2 (hp : 2 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 2 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 2 (transLenTr ⟨114, by decide⟩ 2 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 2 (transLenTr ⟨114, by decide⟩ 2 hp)) T135_114
      hfix135_114 hinj135_114 hcardT135_114
      (fun i => conj_mem_of_fixedPoints _ _ (T135_114 i) (hfix135_114 i) _)
      ⟨135, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 2 hp) Q2.T135_114_2 Q2.hfix135_114_2 Q2.hinj135_114_2
      Q2.hcardT135_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_114_2 i) (Q2.hfix135_114_2 i) _)
      colCert_135_114_2.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_114_3 (hp : 3 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 3 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 3 (transLenTr ⟨114, by decide⟩ 3 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 3 (transLenTr ⟨114, by decide⟩ 3 hp)) T135_114
      hfix135_114 hinj135_114 hcardT135_114
      (fun i => conj_mem_of_fixedPoints _ _ (T135_114 i) (hfix135_114 i) _)
      ⟨135, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 3 hp) Q2.T135_114_2 Q2.hfix135_114_2 Q2.hinj135_114_2
      Q2.hcardT135_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_114_2 i) (Q2.hfix135_114_2 i) _)
      colCert_135_114_3.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_114_4 (hp : 4 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 4 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 4 (transLenTr ⟨114, by decide⟩ 4 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 4 (transLenTr ⟨114, by decide⟩ 4 hp)) T135_114
      hfix135_114 hinj135_114 hcardT135_114
      (fun i => conj_mem_of_fixedPoints _ _ (T135_114 i) (hfix135_114 i) _)
      ⟨135, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 4 hp) Q2.T135_114_2 Q2.hfix135_114_2 Q2.hinj135_114_2
      Q2.hcardT135_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_114_2 i) (Q2.hfix135_114_2 i) _)
      colCert_135_114_4.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_114_5 (hp : 5 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 5 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 5 (transLenTr ⟨114, by decide⟩ 5 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 5 (transLenTr ⟨114, by decide⟩ 5 hp)) T135_114
      hfix135_114 hinj135_114 hcardT135_114
      (fun i => conj_mem_of_fixedPoints _ _ (T135_114 i) (hfix135_114 i) _)
      ⟨135, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 5 hp) Q2.T135_114_2 Q2.hfix135_114_2 Q2.hinj135_114_2
      Q2.hcardT135_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_114_2 i) (Q2.hfix135_114_2 i) _)
      colCert_135_114_5.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_114_10 (hp : 10 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 10 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 10 (transLenTr ⟨114, by decide⟩ 10 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 10 (transLenTr ⟨114, by decide⟩ 10 hp)) T135_114
      hfix135_114 hinj135_114 hcardT135_114
      (fun i => conj_mem_of_fixedPoints _ _ (T135_114 i) (hfix135_114 i) _)
      ⟨135, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 10 hp) Q2.T135_114_2 Q2.hfix135_114_2 Q2.hinj135_114_2
      Q2.hcardT135_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_114_2 i) (Q2.hfix135_114_2 i) _)
      colCert_135_114_10.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_114_15 (hp : 15 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 15 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 15 (transLenTr ⟨114, by decide⟩ 15 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 15 (transLenTr ⟨114, by decide⟩ 15 hp)) T135_114
      hfix135_114 hinj135_114 hcardT135_114
      (fun i => conj_mem_of_fixedPoints _ _ (T135_114 i) (hfix135_114 i) _)
      ⟨135, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 15 hp) Q2.T135_114_2 Q2.hfix135_114_2 Q2.hinj135_114_2
      Q2.hcardT135_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_114_2 i) (Q2.hfix135_114_2 i) _)
      colCert_135_114_15.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_114_20 (hp : 20 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 20 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 20 (transLenTr ⟨114, by decide⟩ 20 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 20 (transLenTr ⟨114, by decide⟩ 20 hp)) T135_114
      hfix135_114 hinj135_114 hcardT135_114
      (fun i => conj_mem_of_fixedPoints _ _ (T135_114 i) (hfix135_114 i) _)
      ⟨135, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 20 hp) Q2.T135_114_2 Q2.hfix135_114_2 Q2.hinj135_114_2
      Q2.hcardT135_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_114_2 i) (Q2.hfix135_114_2 i) _)
      colCert_135_114_20.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_135_0 (hp : 0 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 0 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 0 (transLenTr ⟨135, by decide⟩ 0 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 0 (transLenTr ⟨135, by decide⟩ 0 hp)) T135_135
      hfix135_135 hinj135_135 hcardT135_135
      (fun i => conj_mem_of_fixedPoints _ _ (T135_135 i) (hfix135_135 i) _)
      ⟨135, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 0 hp) Q2.T135_135_2 Q2.hfix135_135_2 Q2.hinj135_135_2
      Q2.hcardT135_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_135_2 i) (Q2.hfix135_135_2 i) _)
      colCert_135_135_0.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_135_1 (hp : 1 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 1 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 1 (transLenTr ⟨135, by decide⟩ 1 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 1 (transLenTr ⟨135, by decide⟩ 1 hp)) T135_135
      hfix135_135 hinj135_135 hcardT135_135
      (fun i => conj_mem_of_fixedPoints _ _ (T135_135 i) (hfix135_135 i) _)
      ⟨135, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 1 hp) Q2.T135_135_2 Q2.hfix135_135_2 Q2.hinj135_135_2
      Q2.hcardT135_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_135_2 i) (Q2.hfix135_135_2 i) _)
      colCert_135_135_1.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_135_2 (hp : 2 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 2 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 2 (transLenTr ⟨135, by decide⟩ 2 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 2 (transLenTr ⟨135, by decide⟩ 2 hp)) T135_135
      hfix135_135 hinj135_135 hcardT135_135
      (fun i => conj_mem_of_fixedPoints _ _ (T135_135 i) (hfix135_135 i) _)
      ⟨135, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 2 hp) Q2.T135_135_2 Q2.hfix135_135_2 Q2.hinj135_135_2
      Q2.hcardT135_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_135_2 i) (Q2.hfix135_135_2 i) _)
      colCert_135_135_2.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_135_3 (hp : 3 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 3 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 3 (transLenTr ⟨135, by decide⟩ 3 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 3 (transLenTr ⟨135, by decide⟩ 3 hp)) T135_135
      hfix135_135 hinj135_135 hcardT135_135
      (fun i => conj_mem_of_fixedPoints _ _ (T135_135 i) (hfix135_135 i) _)
      ⟨135, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 3 hp) Q2.T135_135_2 Q2.hfix135_135_2 Q2.hinj135_135_2
      Q2.hcardT135_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_135_2 i) (Q2.hfix135_135_2 i) _)
      colCert_135_135_3.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_135_4 (hp : 4 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 4 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 4 (transLenTr ⟨135, by decide⟩ 4 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 4 (transLenTr ⟨135, by decide⟩ 4 hp)) T135_135
      hfix135_135 hinj135_135 hcardT135_135
      (fun i => conj_mem_of_fixedPoints _ _ (T135_135 i) (hfix135_135 i) _)
      ⟨135, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 4 hp) Q2.T135_135_2 Q2.hfix135_135_2 Q2.hinj135_135_2
      Q2.hcardT135_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_135_2 i) (Q2.hfix135_135_2 i) _)
      colCert_135_135_4.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_135_5 (hp : 5 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 5 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 5 (transLenTr ⟨135, by decide⟩ 5 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 5 (transLenTr ⟨135, by decide⟩ 5 hp)) T135_135
      hfix135_135 hinj135_135 hcardT135_135
      (fun i => conj_mem_of_fixedPoints _ _ (T135_135 i) (hfix135_135 i) _)
      ⟨135, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 5 hp) Q2.T135_135_2 Q2.hfix135_135_2 Q2.hinj135_135_2
      Q2.hcardT135_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_135_2 i) (Q2.hfix135_135_2 i) _)
      colCert_135_135_5.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_135_6 (hp : 6 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 6 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 6 (transLenTr ⟨135, by decide⟩ 6 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 6 (transLenTr ⟨135, by decide⟩ 6 hp)) T135_135
      hfix135_135 hinj135_135 hcardT135_135
      (fun i => conj_mem_of_fixedPoints _ _ (T135_135 i) (hfix135_135 i) _)
      ⟨135, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 6 hp) Q2.T135_135_2 Q2.hfix135_135_2 Q2.hinj135_135_2
      Q2.hcardT135_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_135_2 i) (Q2.hfix135_135_2 i) _)
      colCert_135_135_6.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_135_7 (hp : 7 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 7 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 7 (transLenTr ⟨135, by decide⟩ 7 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 7 (transLenTr ⟨135, by decide⟩ 7 hp)) T135_135
      hfix135_135 hinj135_135 hcardT135_135
      (fun i => conj_mem_of_fixedPoints _ _ (T135_135 i) (hfix135_135 i) _)
      ⟨135, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 7 hp) Q2.T135_135_2 Q2.hfix135_135_2 Q2.hinj135_135_2
      Q2.hcardT135_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_135_2 i) (Q2.hfix135_135_2 i) _)
      colCert_135_135_7.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_135_8 (hp : 8 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 8 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 8 (transLenTr ⟨135, by decide⟩ 8 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 8 (transLenTr ⟨135, by decide⟩ 8 hp)) T135_135
      hfix135_135 hinj135_135 hcardT135_135
      (fun i => conj_mem_of_fixedPoints _ _ (T135_135 i) (hfix135_135 i) _)
      ⟨135, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 8 hp) Q2.T135_135_2 Q2.hfix135_135_2 Q2.hinj135_135_2
      Q2.hcardT135_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_135_2 i) (Q2.hfix135_135_2 i) _)
      colCert_135_135_8.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_135_9 (hp : 9 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 9 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 9 (transLenTr ⟨135, by decide⟩ 9 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 9 (transLenTr ⟨135, by decide⟩ 9 hp)) T135_135
      hfix135_135 hinj135_135 hcardT135_135
      (fun i => conj_mem_of_fixedPoints _ _ (T135_135 i) (hfix135_135 i) _)
      ⟨135, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 9 hp) Q2.T135_135_2 Q2.hfix135_135_2 Q2.hinj135_135_2
      Q2.hcardT135_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_135_2 i) (Q2.hfix135_135_2 i) _)
      colCert_135_135_9.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_135_10 (hp : 10 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 10 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 10 (transLenTr ⟨135, by decide⟩ 10 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 10 (transLenTr ⟨135, by decide⟩ 10 hp)) T135_135
      hfix135_135 hinj135_135 hcardT135_135
      (fun i => conj_mem_of_fixedPoints _ _ (T135_135 i) (hfix135_135 i) _)
      ⟨135, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 10 hp) Q2.T135_135_2 Q2.hfix135_135_2 Q2.hinj135_135_2
      Q2.hcardT135_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_135_2 i) (Q2.hfix135_135_2 i) _)
      colCert_135_135_10.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_135_11 (hp : 11 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 11 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 11 (transLenTr ⟨135, by decide⟩ 11 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 11 (transLenTr ⟨135, by decide⟩ 11 hp)) T135_135
      hfix135_135 hinj135_135 hcardT135_135
      (fun i => conj_mem_of_fixedPoints _ _ (T135_135 i) (hfix135_135 i) _)
      ⟨135, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 11 hp) Q2.T135_135_2 Q2.hfix135_135_2 Q2.hinj135_135_2
      Q2.hcardT135_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_135_2 i) (Q2.hfix135_135_2 i) _)
      colCert_135_135_11.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_135_12 (hp : 12 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 12 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 12 (transLenTr ⟨135, by decide⟩ 12 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 12 (transLenTr ⟨135, by decide⟩ 12 hp)) T135_135
      hfix135_135 hinj135_135 hcardT135_135
      (fun i => conj_mem_of_fixedPoints _ _ (T135_135 i) (hfix135_135 i) _)
      ⟨135, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 12 hp) Q2.T135_135_2 Q2.hfix135_135_2 Q2.hinj135_135_2
      Q2.hcardT135_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_135_2 i) (Q2.hfix135_135_2 i) _)
      colCert_135_135_12.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_135_13 (hp : 13 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 13 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 13 (transLenTr ⟨135, by decide⟩ 13 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 13 (transLenTr ⟨135, by decide⟩ 13 hp)) T135_135
      hfix135_135 hinj135_135 hcardT135_135
      (fun i => conj_mem_of_fixedPoints _ _ (T135_135 i) (hfix135_135 i) _)
      ⟨135, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 13 hp) Q2.T135_135_2 Q2.hfix135_135_2 Q2.hinj135_135_2
      Q2.hcardT135_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_135_2 i) (Q2.hfix135_135_2 i) _)
      colCert_135_135_13.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_135_14 (hp : 14 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 14 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 14 (transLenTr ⟨135, by decide⟩ 14 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 14 (transLenTr ⟨135, by decide⟩ 14 hp)) T135_135
      hfix135_135 hinj135_135 hcardT135_135
      (fun i => conj_mem_of_fixedPoints _ _ (T135_135 i) (hfix135_135 i) _)
      ⟨135, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 14 hp) Q2.T135_135_2 Q2.hfix135_135_2 Q2.hinj135_135_2
      Q2.hcardT135_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_135_2 i) (Q2.hfix135_135_2 i) _)
      colCert_135_135_14.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_135_15 (hp : 15 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 15 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 15 (transLenTr ⟨135, by decide⟩ 15 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 15 (transLenTr ⟨135, by decide⟩ 15 hp)) T135_135
      hfix135_135 hinj135_135 hcardT135_135
      (fun i => conj_mem_of_fixedPoints _ _ (T135_135 i) (hfix135_135 i) _)
      ⟨135, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 15 hp) Q2.T135_135_2 Q2.hfix135_135_2 Q2.hinj135_135_2
      Q2.hcardT135_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_135_2 i) (Q2.hfix135_135_2 i) _)
      colCert_135_135_15.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_135_16 (hp : 16 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 16 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 16 (transLenTr ⟨135, by decide⟩ 16 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 16 (transLenTr ⟨135, by decide⟩ 16 hp)) T135_135
      hfix135_135 hinj135_135 hcardT135_135
      (fun i => conj_mem_of_fixedPoints _ _ (T135_135 i) (hfix135_135 i) _)
      ⟨135, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 16 hp) Q2.T135_135_2 Q2.hfix135_135_2 Q2.hinj135_135_2
      Q2.hcardT135_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_135_2 i) (Q2.hfix135_135_2 i) _)
      colCert_135_135_16.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_135_17 (hp : 17 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 17 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 17 (transLenTr ⟨135, by decide⟩ 17 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 17 (transLenTr ⟨135, by decide⟩ 17 hp)) T135_135
      hfix135_135 hinj135_135 hcardT135_135
      (fun i => conj_mem_of_fixedPoints _ _ (T135_135 i) (hfix135_135 i) _)
      ⟨135, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 17 hp) Q2.T135_135_2 Q2.hfix135_135_2 Q2.hinj135_135_2
      Q2.hcardT135_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_135_2 i) (Q2.hfix135_135_2 i) _)
      colCert_135_135_17.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_135_18 (hp : 18 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 18 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 18 (transLenTr ⟨135, by decide⟩ 18 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 18 (transLenTr ⟨135, by decide⟩ 18 hp)) T135_135
      hfix135_135 hinj135_135 hcardT135_135
      (fun i => conj_mem_of_fixedPoints _ _ (T135_135 i) (hfix135_135 i) _)
      ⟨135, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 18 hp) Q2.T135_135_2 Q2.hfix135_135_2 Q2.hinj135_135_2
      Q2.hcardT135_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_135_2 i) (Q2.hfix135_135_2 i) _)
      colCert_135_135_18.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_135_19 (hp : 19 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 19 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 19 (transLenTr ⟨135, by decide⟩ 19 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 19 (transLenTr ⟨135, by decide⟩ 19 hp)) T135_135
      hfix135_135 hinj135_135 hcardT135_135
      (fun i => conj_mem_of_fixedPoints _ _ (T135_135 i) (hfix135_135 i) _)
      ⟨135, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 19 hp) Q2.T135_135_2 Q2.hfix135_135_2 Q2.hinj135_135_2
      Q2.hcardT135_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_135_2 i) (Q2.hfix135_135_2 i) _)
      colCert_135_135_19.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_135_20 (hp : 20 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 20 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 20 (transLenTr ⟨135, by decide⟩ 20 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 20 (transLenTr ⟨135, by decide⟩ 20 hp)) T135_135
      hfix135_135 hinj135_135 hcardT135_135
      (fun i => conj_mem_of_fixedPoints _ _ (T135_135 i) (hfix135_135 i) _)
      ⟨135, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 20 hp) Q2.T135_135_2 Q2.hfix135_135_2 Q2.hinj135_135_2
      Q2.hcardT135_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_135_2 i) (Q2.hfix135_135_2 i) _)
      colCert_135_135_20.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_135_21 (hp : 21 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 21 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 21 (transLenTr ⟨135, by decide⟩ 21 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 21 (transLenTr ⟨135, by decide⟩ 21 hp)) T135_135
      hfix135_135 hinj135_135 hcardT135_135
      (fun i => conj_mem_of_fixedPoints _ _ (T135_135 i) (hfix135_135 i) _)
      ⟨135, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 21 hp) Q2.T135_135_2 Q2.hfix135_135_2 Q2.hinj135_135_2
      Q2.hcardT135_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_135_2 i) (Q2.hfix135_135_2 i) _)
      colCert_135_135_21.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_135_22 (hp : 22 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 22 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 22 (transLenTr ⟨135, by decide⟩ 22 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 22 (transLenTr ⟨135, by decide⟩ 22 hp)) T135_135
      hfix135_135 hinj135_135 hcardT135_135
      (fun i => conj_mem_of_fixedPoints _ _ (T135_135 i) (hfix135_135 i) _)
      ⟨135, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 22 hp) Q2.T135_135_2 Q2.hfix135_135_2 Q2.hinj135_135_2
      Q2.hcardT135_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_135_2 i) (Q2.hfix135_135_2 i) _)
      colCert_135_135_22.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_135_23 (hp : 23 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 23 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 23 (transLenTr ⟨135, by decide⟩ 23 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 23 (transLenTr ⟨135, by decide⟩ 23 hp)) T135_135
      hfix135_135 hinj135_135 hcardT135_135
      (fun i => conj_mem_of_fixedPoints _ _ (T135_135 i) (hfix135_135 i) _)
      ⟨135, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 23 hp) Q2.T135_135_2 Q2.hfix135_135_2 Q2.hinj135_135_2
      Q2.hcardT135_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_135_2 i) (Q2.hfix135_135_2 i) _)
      colCert_135_135_23.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_135_24 (hp : 24 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 24 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 24 (transLenTr ⟨135, by decide⟩ 24 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 24 (transLenTr ⟨135, by decide⟩ 24 hp)) T135_135
      hfix135_135 hinj135_135 hcardT135_135
      (fun i => conj_mem_of_fixedPoints _ _ (T135_135 i) (hfix135_135 i) _)
      ⟨135, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 24 hp) Q2.T135_135_2 Q2.hfix135_135_2 Q2.hinj135_135_2
      Q2.hcardT135_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_135_2 i) (Q2.hfix135_135_2 i) _)
      colCert_135_135_24.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_136_5_0 (hp : 0 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 0 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp)) T136_5
      hfix136_5 hinj136_5 hcardT136_5
      (fun i => conj_mem_of_fixedPoints _ _ (T136_5 i) (hfix136_5 i) _)
      ⟨136, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 0 hp) Q2.T136_5_2 Q2.hfix136_5_2 Q2.hinj136_5_2
      Q2.hcardT136_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_5_2 i) (Q2.hfix136_5_2 i) _)
      colCert_136_5_0.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_5_1 (hp : 1 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 1 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp)) T136_5
      hfix136_5 hinj136_5 hcardT136_5
      (fun i => conj_mem_of_fixedPoints _ _ (T136_5 i) (hfix136_5 i) _)
      ⟨136, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 1 hp) Q2.T136_5_2 Q2.hfix136_5_2 Q2.hinj136_5_2
      Q2.hcardT136_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_5_2 i) (Q2.hfix136_5_2 i) _)
      colCert_136_5_1.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_5_2 (hp : 2 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 2 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp)) T136_5
      hfix136_5 hinj136_5 hcardT136_5
      (fun i => conj_mem_of_fixedPoints _ _ (T136_5 i) (hfix136_5 i) _)
      ⟨136, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 2 hp) Q2.T136_5_2 Q2.hfix136_5_2 Q2.hinj136_5_2
      Q2.hcardT136_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_5_2 i) (Q2.hfix136_5_2 i) _)
      colCert_136_5_2.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_5_3 (hp : 3 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 3 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp)) T136_5
      hfix136_5 hinj136_5 hcardT136_5
      (fun i => conj_mem_of_fixedPoints _ _ (T136_5 i) (hfix136_5 i) _)
      ⟨136, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 3 hp) Q2.T136_5_2 Q2.hfix136_5_2 Q2.hinj136_5_2
      Q2.hcardT136_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_5_2 i) (Q2.hfix136_5_2 i) _)
      colCert_136_5_3.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_5_4 (hp : 4 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 4 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp)) T136_5
      hfix136_5 hinj136_5 hcardT136_5
      (fun i => conj_mem_of_fixedPoints _ _ (T136_5 i) (hfix136_5 i) _)
      ⟨136, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 4 hp) Q2.T136_5_2 Q2.hfix136_5_2 Q2.hinj136_5_2
      Q2.hcardT136_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_5_2 i) (Q2.hfix136_5_2 i) _)
      colCert_136_5_4.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T136_10
      hfix136_10 hinj136_10 hcardT136_10
      (fun i => conj_mem_of_fixedPoints _ _ (T136_10 i) (hfix136_10 i) _)
      ⟨136, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T136_10_2 Q2.hfix136_10_2 Q2.hinj136_10_2
      Q2.hcardT136_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_10_2 i) (Q2.hfix136_10_2 i) _)
      colCert_136_10_0.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T136_10
      hfix136_10 hinj136_10 hcardT136_10
      (fun i => conj_mem_of_fixedPoints _ _ (T136_10 i) (hfix136_10 i) _)
      ⟨136, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T136_10_2 Q2.hfix136_10_2 Q2.hinj136_10_2
      Q2.hcardT136_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_10_2 i) (Q2.hfix136_10_2 i) _)
      colCert_136_10_1.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T136_10
      hfix136_10 hinj136_10 hcardT136_10
      (fun i => conj_mem_of_fixedPoints _ _ (T136_10 i) (hfix136_10 i) _)
      ⟨136, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T136_10_2 Q2.hfix136_10_2 Q2.hinj136_10_2
      Q2.hcardT136_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_10_2 i) (Q2.hfix136_10_2 i) _)
      colCert_136_10_2.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T136_10
      hfix136_10 hinj136_10 hcardT136_10
      (fun i => conj_mem_of_fixedPoints _ _ (T136_10 i) (hfix136_10 i) _)
      ⟨136, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T136_10_2 Q2.hfix136_10_2 Q2.hinj136_10_2
      Q2.hcardT136_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_10_2 i) (Q2.hfix136_10_2 i) _)
      colCert_136_10_3.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T136_10
      hfix136_10 hinj136_10 hcardT136_10
      (fun i => conj_mem_of_fixedPoints _ _ (T136_10 i) (hfix136_10 i) _)
      ⟨136, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T136_10_2 Q2.hfix136_10_2 Q2.hinj136_10_2
      Q2.hcardT136_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_10_2 i) (Q2.hfix136_10_2 i) _)
      colCert_136_10_4.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T136_12
      hfix136_12 hinj136_12 hcardT136_12
      (fun i => conj_mem_of_fixedPoints _ _ (T136_12 i) (hfix136_12 i) _)
      ⟨136, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T136_12_2 Q2.hfix136_12_2 Q2.hinj136_12_2
      Q2.hcardT136_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_12_2 i) (Q2.hfix136_12_2 i) _)
      colCert_136_12_0.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T136_12
      hfix136_12 hinj136_12 hcardT136_12
      (fun i => conj_mem_of_fixedPoints _ _ (T136_12 i) (hfix136_12 i) _)
      ⟨136, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T136_12_2 Q2.hfix136_12_2 Q2.hinj136_12_2
      Q2.hcardT136_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_12_2 i) (Q2.hfix136_12_2 i) _)
      colCert_136_12_1.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T136_12
      hfix136_12 hinj136_12 hcardT136_12
      (fun i => conj_mem_of_fixedPoints _ _ (T136_12 i) (hfix136_12 i) _)
      ⟨136, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T136_12_2 Q2.hfix136_12_2 Q2.hinj136_12_2
      Q2.hcardT136_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_12_2 i) (Q2.hfix136_12_2 i) _)
      colCert_136_12_2.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T136_12
      hfix136_12 hinj136_12 hcardT136_12
      (fun i => conj_mem_of_fixedPoints _ _ (T136_12 i) (hfix136_12 i) _)
      ⟨136, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T136_12_2 Q2.hfix136_12_2 Q2.hinj136_12_2
      Q2.hcardT136_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_12_2 i) (Q2.hfix136_12_2 i) _)
      colCert_136_12_3.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T136_12
      hfix136_12 hinj136_12 hcardT136_12
      (fun i => conj_mem_of_fixedPoints _ _ (T136_12 i) (hfix136_12 i) _)
      ⟨136, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T136_12_2 Q2.hfix136_12_2 Q2.hinj136_12_2
      Q2.hcardT136_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_12_2 i) (Q2.hfix136_12_2 i) _)
      colCert_136_12_4.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_23_0 (hp : 0 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 0 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 0 (transLenTr ⟨23, by decide⟩ 0 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 0 (transLenTr ⟨23, by decide⟩ 0 hp)) T136_23
      hfix136_23 hinj136_23 hcardT136_23
      (fun i => conj_mem_of_fixedPoints _ _ (T136_23 i) (hfix136_23 i) _)
      ⟨136, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 0 hp) Q2.T136_23_2 Q2.hfix136_23_2 Q2.hinj136_23_2
      Q2.hcardT136_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_23_2 i) (Q2.hfix136_23_2 i) _)
      colCert_136_23_0.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_23_1 (hp : 1 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 1 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 1 (transLenTr ⟨23, by decide⟩ 1 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 1 (transLenTr ⟨23, by decide⟩ 1 hp)) T136_23
      hfix136_23 hinj136_23 hcardT136_23
      (fun i => conj_mem_of_fixedPoints _ _ (T136_23 i) (hfix136_23 i) _)
      ⟨136, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 1 hp) Q2.T136_23_2 Q2.hfix136_23_2 Q2.hinj136_23_2
      Q2.hcardT136_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_23_2 i) (Q2.hfix136_23_2 i) _)
      colCert_136_23_1.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_23_2 (hp : 2 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 2 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 2 (transLenTr ⟨23, by decide⟩ 2 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 2 (transLenTr ⟨23, by decide⟩ 2 hp)) T136_23
      hfix136_23 hinj136_23 hcardT136_23
      (fun i => conj_mem_of_fixedPoints _ _ (T136_23 i) (hfix136_23 i) _)
      ⟨136, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 2 hp) Q2.T136_23_2 Q2.hfix136_23_2 Q2.hinj136_23_2
      Q2.hcardT136_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_23_2 i) (Q2.hfix136_23_2 i) _)
      colCert_136_23_2.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_23_3 (hp : 3 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 3 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 3 (transLenTr ⟨23, by decide⟩ 3 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 3 (transLenTr ⟨23, by decide⟩ 3 hp)) T136_23
      hfix136_23 hinj136_23 hcardT136_23
      (fun i => conj_mem_of_fixedPoints _ _ (T136_23 i) (hfix136_23 i) _)
      ⟨136, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 3 hp) Q2.T136_23_2 Q2.hfix136_23_2 Q2.hinj136_23_2
      Q2.hcardT136_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_23_2 i) (Q2.hfix136_23_2 i) _)
      colCert_136_23_3.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_23_4 (hp : 4 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 4 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 4 (transLenTr ⟨23, by decide⟩ 4 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 4 (transLenTr ⟨23, by decide⟩ 4 hp)) T136_23
      hfix136_23 hinj136_23 hcardT136_23
      (fun i => conj_mem_of_fixedPoints _ _ (T136_23 i) (hfix136_23 i) _)
      ⟨136, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 4 hp) Q2.T136_23_2 Q2.hfix136_23_2 Q2.hinj136_23_2
      Q2.hcardT136_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_23_2 i) (Q2.hfix136_23_2 i) _)
      colCert_136_23_4.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_23_5 (hp : 5 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 5 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp)) T136_23
      hfix136_23 hinj136_23 hcardT136_23
      (fun i => conj_mem_of_fixedPoints _ _ (T136_23 i) (hfix136_23 i) _)
      ⟨136, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 5 hp) Q2.T136_23_2 Q2.hfix136_23_2 Q2.hinj136_23_2
      Q2.hcardT136_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_23_2 i) (Q2.hfix136_23_2 i) _)
      colCert_136_23_5.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_23_10 (hp : 10 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 10 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp)) T136_23
      hfix136_23 hinj136_23 hcardT136_23
      (fun i => conj_mem_of_fixedPoints _ _ (T136_23 i) (hfix136_23 i) _)
      ⟨136, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 10 hp) Q2.T136_23_2 Q2.hfix136_23_2 Q2.hinj136_23_2
      Q2.hcardT136_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_23_2 i) (Q2.hfix136_23_2 i) _)
      colCert_136_23_10.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_23_15 (hp : 15 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 15 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp)) T136_23
      hfix136_23 hinj136_23 hcardT136_23
      (fun i => conj_mem_of_fixedPoints _ _ (T136_23 i) (hfix136_23 i) _)
      ⟨136, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 15 hp) Q2.T136_23_2 Q2.hfix136_23_2 Q2.hinj136_23_2
      Q2.hcardT136_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_23_2 i) (Q2.hfix136_23_2 i) _)
      colCert_136_23_15.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_23_20 (hp : 20 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 20 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp)) T136_23
      hfix136_23 hinj136_23 hcardT136_23
      (fun i => conj_mem_of_fixedPoints _ _ (T136_23 i) (hfix136_23 i) _)
      ⟨136, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 20 hp) Q2.T136_23_2 Q2.hfix136_23_2 Q2.hinj136_23_2
      Q2.hcardT136_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_23_2 i) (Q2.hfix136_23_2 i) _)
      colCert_136_23_20.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_29_0 (hp : 0 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 0 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp)) T136_29
      hfix136_29 hinj136_29 hcardT136_29
      (fun i => conj_mem_of_fixedPoints _ _ (T136_29 i) (hfix136_29 i) _)
      ⟨136, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 0 hp) Q2.T136_29_2 Q2.hfix136_29_2 Q2.hinj136_29_2
      Q2.hcardT136_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_29_2 i) (Q2.hfix136_29_2 i) _)
      colCert_136_29_0.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_29_1 (hp : 1 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 1 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp)) T136_29
      hfix136_29 hinj136_29 hcardT136_29
      (fun i => conj_mem_of_fixedPoints _ _ (T136_29 i) (hfix136_29 i) _)
      ⟨136, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 1 hp) Q2.T136_29_2 Q2.hfix136_29_2 Q2.hinj136_29_2
      Q2.hcardT136_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_29_2 i) (Q2.hfix136_29_2 i) _)
      colCert_136_29_1.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_29_2 (hp : 2 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 2 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp)) T136_29
      hfix136_29 hinj136_29 hcardT136_29
      (fun i => conj_mem_of_fixedPoints _ _ (T136_29 i) (hfix136_29 i) _)
      ⟨136, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 2 hp) Q2.T136_29_2 Q2.hfix136_29_2 Q2.hinj136_29_2
      Q2.hcardT136_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_29_2 i) (Q2.hfix136_29_2 i) _)
      colCert_136_29_2.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_29_3 (hp : 3 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 3 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp)) T136_29
      hfix136_29 hinj136_29 hcardT136_29
      (fun i => conj_mem_of_fixedPoints _ _ (T136_29 i) (hfix136_29 i) _)
      ⟨136, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 3 hp) Q2.T136_29_2 Q2.hfix136_29_2 Q2.hinj136_29_2
      Q2.hcardT136_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_29_2 i) (Q2.hfix136_29_2 i) _)
      colCert_136_29_3.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_29_4 (hp : 4 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 4 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp)) T136_29
      hfix136_29 hinj136_29 hcardT136_29
      (fun i => conj_mem_of_fixedPoints _ _ (T136_29 i) (hfix136_29 i) _)
      ⟨136, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 4 hp) Q2.T136_29_2 Q2.hfix136_29_2 Q2.hinj136_29_2
      Q2.hcardT136_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_29_2 i) (Q2.hfix136_29_2 i) _)
      colCert_136_29_4.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_29_5 (hp : 5 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 5 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp)) T136_29
      hfix136_29 hinj136_29 hcardT136_29
      (fun i => conj_mem_of_fixedPoints _ _ (T136_29 i) (hfix136_29 i) _)
      ⟨136, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 5 hp) Q2.T136_29_2 Q2.hfix136_29_2 Q2.hinj136_29_2
      Q2.hcardT136_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_29_2 i) (Q2.hfix136_29_2 i) _)
      colCert_136_29_5.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_29_10 (hp : 10 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 10 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨136, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp)) T136_29
      hfix136_29 hinj136_29 hcardT136_29
      (fun i => conj_mem_of_fixedPoints _ _ (T136_29 i) (hfix136_29 i) _)
      ⟨136, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 10 hp) Q2.T136_29_2 Q2.hfix136_29_2 Q2.hinj136_29_2
      Q2.hcardT136_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_29_2 i) (Q2.hfix136_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨136, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T136_29 = colFn colCertDiv_136_29_10.D1 (m := 5) from colCertDiv_136_29_10.bind1,
    show colData2 (⟨136, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 10 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T136_29_2 = colFn colCertDiv_136_29_10.D2 (m := 5) from colCertDiv_136_29_10.bind2]
  rw [alnId_136 j hj]
  exact fastcode_of_div ⟨136, by decide⟩ _ _ _
    ((alnId_136 j hj) ▸ Q2.listedAt (⟨136, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨136, by decide⟩ : Fin 148) hj hq).1) colCertDiv_136_29_10_match


theorem leaf_136_29_15 (hp : 15 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 15 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨136, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp)) T136_29
      hfix136_29 hinj136_29 hcardT136_29
      (fun i => conj_mem_of_fixedPoints _ _ (T136_29 i) (hfix136_29 i) _)
      ⟨136, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 15 hp) Q2.T136_29_2 Q2.hfix136_29_2 Q2.hinj136_29_2
      Q2.hcardT136_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_29_2 i) (Q2.hfix136_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨136, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T136_29 = colFn colCertDiv_136_29_15.D1 (m := 5) from colCertDiv_136_29_15.bind1,
    show colData2 (⟨136, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 15 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T136_29_2 = colFn colCertDiv_136_29_15.D2 (m := 5) from colCertDiv_136_29_15.bind2]
  rw [alnId_136 j hj]
  exact fastcode_of_div ⟨136, by decide⟩ _ _ _
    ((alnId_136 j hj) ▸ Q2.listedAt (⟨136, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨136, by decide⟩ : Fin 148) hj hq).1) colCertDiv_136_29_15_match


theorem leaf_136_29_20 (hp : 20 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 20 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨136, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp)) T136_29
      hfix136_29 hinj136_29 hcardT136_29
      (fun i => conj_mem_of_fixedPoints _ _ (T136_29 i) (hfix136_29 i) _)
      ⟨136, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 20 hp) Q2.T136_29_2 Q2.hfix136_29_2 Q2.hinj136_29_2
      Q2.hcardT136_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_29_2 i) (Q2.hfix136_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨136, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T136_29 = colFn colCertDiv_136_29_20.D1 (m := 5) from colCertDiv_136_29_20.bind1,
    show colData2 (⟨136, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 20 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T136_29_2 = colFn colCertDiv_136_29_20.D2 (m := 5) from colCertDiv_136_29_20.bind2]
  rw [alnId_136 j hj]
  exact fastcode_of_div ⟨136, by decide⟩ _ _ _
    ((alnId_136 j hj) ▸ Q2.listedAt (⟨136, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨136, by decide⟩ : Fin 148) hj hq).1) colCertDiv_136_29_20_match


theorem leaf_136_36_0 (hp : 0 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 0 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp)) T136_36
      hfix136_36 hinj136_36 hcardT136_36
      (fun i => conj_mem_of_fixedPoints _ _ (T136_36 i) (hfix136_36 i) _)
      ⟨136, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 0 hp) Q2.T136_36_2 Q2.hfix136_36_2 Q2.hinj136_36_2
      Q2.hcardT136_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_36_2 i) (Q2.hfix136_36_2 i) _)
      colCert_136_36_0.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_36_1 (hp : 1 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 1 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp)) T136_36
      hfix136_36 hinj136_36 hcardT136_36
      (fun i => conj_mem_of_fixedPoints _ _ (T136_36 i) (hfix136_36 i) _)
      ⟨136, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 1 hp) Q2.T136_36_2 Q2.hfix136_36_2 Q2.hinj136_36_2
      Q2.hcardT136_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_36_2 i) (Q2.hfix136_36_2 i) _)
      colCert_136_36_1.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_36_2 (hp : 2 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 2 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp)) T136_36
      hfix136_36 hinj136_36 hcardT136_36
      (fun i => conj_mem_of_fixedPoints _ _ (T136_36 i) (hfix136_36 i) _)
      ⟨136, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 2 hp) Q2.T136_36_2 Q2.hfix136_36_2 Q2.hinj136_36_2
      Q2.hcardT136_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_36_2 i) (Q2.hfix136_36_2 i) _)
      colCert_136_36_2.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_36_3 (hp : 3 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 3 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp)) T136_36
      hfix136_36 hinj136_36 hcardT136_36
      (fun i => conj_mem_of_fixedPoints _ _ (T136_36 i) (hfix136_36 i) _)
      ⟨136, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 3 hp) Q2.T136_36_2 Q2.hfix136_36_2 Q2.hinj136_36_2
      Q2.hcardT136_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_36_2 i) (Q2.hfix136_36_2 i) _)
      colCert_136_36_3.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_36_4 (hp : 4 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 4 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp)) T136_36
      hfix136_36 hinj136_36 hcardT136_36
      (fun i => conj_mem_of_fixedPoints _ _ (T136_36 i) (hfix136_36 i) _)
      ⟨136, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 4 hp) Q2.T136_36_2 Q2.hfix136_36_2 Q2.hinj136_36_2
      Q2.hcardT136_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_36_2 i) (Q2.hfix136_36_2 i) _)
      colCert_136_36_4.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_36_5 (hp : 5 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 5 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨136, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp)) T136_36
      hfix136_36 hinj136_36 hcardT136_36
      (fun i => conj_mem_of_fixedPoints _ _ (T136_36 i) (hfix136_36 i) _)
      ⟨136, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 5 hp) Q2.T136_36_2 Q2.hfix136_36_2 Q2.hinj136_36_2
      Q2.hcardT136_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_36_2 i) (Q2.hfix136_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨136, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T136_36 = colFn colCertDiv_136_36_5.D1 (m := 5) from colCertDiv_136_36_5.bind1,
    show colData2 (⟨136, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 5 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T136_36_2 = colFn colCertDiv_136_36_5.D2 (m := 5) from colCertDiv_136_36_5.bind2]
  rw [alnId_136 j hj]
  exact fastcode_of_div ⟨136, by decide⟩ _ _ _
    ((alnId_136 j hj) ▸ Q2.listedAt (⟨136, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨136, by decide⟩ : Fin 148) hj hq).1) colCertDiv_136_36_5_match


theorem leaf_136_36_10 (hp : 10 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 10 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨136, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp)) T136_36
      hfix136_36 hinj136_36 hcardT136_36
      (fun i => conj_mem_of_fixedPoints _ _ (T136_36 i) (hfix136_36 i) _)
      ⟨136, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 10 hp) Q2.T136_36_2 Q2.hfix136_36_2 Q2.hinj136_36_2
      Q2.hcardT136_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_36_2 i) (Q2.hfix136_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨136, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T136_36 = colFn colCertDiv_136_36_10.D1 (m := 5) from colCertDiv_136_36_10.bind1,
    show colData2 (⟨136, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 10 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T136_36_2 = colFn colCertDiv_136_36_10.D2 (m := 5) from colCertDiv_136_36_10.bind2]
  rw [alnId_136 j hj]
  exact fastcode_of_div ⟨136, by decide⟩ _ _ _
    ((alnId_136 j hj) ▸ Q2.listedAt (⟨136, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨136, by decide⟩ : Fin 148) hj hq).1) colCertDiv_136_36_10_match


theorem leaf_136_36_15 (hp : 15 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 15 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨136, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp)) T136_36
      hfix136_36 hinj136_36 hcardT136_36
      (fun i => conj_mem_of_fixedPoints _ _ (T136_36 i) (hfix136_36 i) _)
      ⟨136, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 15 hp) Q2.T136_36_2 Q2.hfix136_36_2 Q2.hinj136_36_2
      Q2.hcardT136_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_36_2 i) (Q2.hfix136_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨136, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T136_36 = colFn colCertDiv_136_36_15.D1 (m := 5) from colCertDiv_136_36_15.bind1,
    show colData2 (⟨136, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 15 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T136_36_2 = colFn colCertDiv_136_36_15.D2 (m := 5) from colCertDiv_136_36_15.bind2]
  rw [alnId_136 j hj]
  exact fastcode_of_div ⟨136, by decide⟩ _ _ _
    ((alnId_136 j hj) ▸ Q2.listedAt (⟨136, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨136, by decide⟩ : Fin 148) hj hq).1) colCertDiv_136_36_15_match


theorem leaf_136_36_20 (hp : 20 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 20 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨136, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp)) T136_36
      hfix136_36 hinj136_36 hcardT136_36
      (fun i => conj_mem_of_fixedPoints _ _ (T136_36 i) (hfix136_36 i) _)
      ⟨136, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 20 hp) Q2.T136_36_2 Q2.hfix136_36_2 Q2.hinj136_36_2
      Q2.hcardT136_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_36_2 i) (Q2.hfix136_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨136, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T136_36 = colFn colCertDiv_136_36_20.D1 (m := 5) from colCertDiv_136_36_20.bind1,
    show colData2 (⟨136, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 20 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T136_36_2 = colFn colCertDiv_136_36_20.D2 (m := 5) from colCertDiv_136_36_20.bind2]
  rw [alnId_136 j hj]
  exact fastcode_of_div ⟨136, by decide⟩ _ _ _
    ((alnId_136 j hj) ▸ Q2.listedAt (⟨136, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨136, by decide⟩ : Fin 148) hj hq).1) colCertDiv_136_36_20_match


theorem leaf_136_40_0 (hp : 0 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 0 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp)) T136_40
      hfix136_40 hinj136_40 hcardT136_40
      (fun i => conj_mem_of_fixedPoints _ _ (T136_40 i) (hfix136_40 i) _)
      ⟨136, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 0 hp) Q2.T136_40_2 Q2.hfix136_40_2 Q2.hinj136_40_2
      Q2.hcardT136_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_40_2 i) (Q2.hfix136_40_2 i) _)
      colCert_136_40_0.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_40_1 (hp : 1 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 1 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp)) T136_40
      hfix136_40 hinj136_40 hcardT136_40
      (fun i => conj_mem_of_fixedPoints _ _ (T136_40 i) (hfix136_40 i) _)
      ⟨136, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 1 hp) Q2.T136_40_2 Q2.hfix136_40_2 Q2.hinj136_40_2
      Q2.hcardT136_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_40_2 i) (Q2.hfix136_40_2 i) _)
      colCert_136_40_1.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_40_2 (hp : 2 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 2 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp)) T136_40
      hfix136_40 hinj136_40 hcardT136_40
      (fun i => conj_mem_of_fixedPoints _ _ (T136_40 i) (hfix136_40 i) _)
      ⟨136, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 2 hp) Q2.T136_40_2 Q2.hfix136_40_2 Q2.hinj136_40_2
      Q2.hcardT136_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_40_2 i) (Q2.hfix136_40_2 i) _)
      colCert_136_40_2.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_40_3 (hp : 3 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 3 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp)) T136_40
      hfix136_40 hinj136_40 hcardT136_40
      (fun i => conj_mem_of_fixedPoints _ _ (T136_40 i) (hfix136_40 i) _)
      ⟨136, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 3 hp) Q2.T136_40_2 Q2.hfix136_40_2 Q2.hinj136_40_2
      Q2.hcardT136_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_40_2 i) (Q2.hfix136_40_2 i) _)
      colCert_136_40_3.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_40_4 (hp : 4 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 4 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp)) T136_40
      hfix136_40 hinj136_40 hcardT136_40
      (fun i => conj_mem_of_fixedPoints _ _ (T136_40 i) (hfix136_40 i) _)
      ⟨136, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 4 hp) Q2.T136_40_2 Q2.hfix136_40_2 Q2.hinj136_40_2
      Q2.hcardT136_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_40_2 i) (Q2.hfix136_40_2 i) _)
      colCert_136_40_4.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_40_5 (hp : 5 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 5 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨136, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp)) T136_40
      hfix136_40 hinj136_40 hcardT136_40
      (fun i => conj_mem_of_fixedPoints _ _ (T136_40 i) (hfix136_40 i) _)
      ⟨136, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 5 hp) Q2.T136_40_2 Q2.hfix136_40_2 Q2.hinj136_40_2
      Q2.hcardT136_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_40_2 i) (Q2.hfix136_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨136, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T136_40 = colFn colCertDiv_136_40_5.D1 (m := 5) from colCertDiv_136_40_5.bind1,
    show colData2 (⟨136, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 5 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T136_40_2 = colFn colCertDiv_136_40_5.D2 (m := 5) from colCertDiv_136_40_5.bind2]
  rw [alnId_136 j hj]
  exact fastcode_of_div ⟨136, by decide⟩ _ _ _
    ((alnId_136 j hj) ▸ Q2.listedAt (⟨136, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨136, by decide⟩ : Fin 148) hj hq).1) colCertDiv_136_40_5_match


theorem leaf_136_40_10 (hp : 10 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 10 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨136, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp)) T136_40
      hfix136_40 hinj136_40 hcardT136_40
      (fun i => conj_mem_of_fixedPoints _ _ (T136_40 i) (hfix136_40 i) _)
      ⟨136, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 10 hp) Q2.T136_40_2 Q2.hfix136_40_2 Q2.hinj136_40_2
      Q2.hcardT136_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_40_2 i) (Q2.hfix136_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨136, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T136_40 = colFn colCertDiv_136_40_10.D1 (m := 5) from colCertDiv_136_40_10.bind1,
    show colData2 (⟨136, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 10 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T136_40_2 = colFn colCertDiv_136_40_10.D2 (m := 5) from colCertDiv_136_40_10.bind2]
  rw [alnId_136 j hj]
  exact fastcode_of_div ⟨136, by decide⟩ _ _ _
    ((alnId_136 j hj) ▸ Q2.listedAt (⟨136, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨136, by decide⟩ : Fin 148) hj hq).1) colCertDiv_136_40_10_match


theorem leaf_136_40_15 (hp : 15 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 15 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨136, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp)) T136_40
      hfix136_40 hinj136_40 hcardT136_40
      (fun i => conj_mem_of_fixedPoints _ _ (T136_40 i) (hfix136_40 i) _)
      ⟨136, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 15 hp) Q2.T136_40_2 Q2.hfix136_40_2 Q2.hinj136_40_2
      Q2.hcardT136_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_40_2 i) (Q2.hfix136_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨136, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T136_40 = colFn colCertDiv_136_40_15.D1 (m := 5) from colCertDiv_136_40_15.bind1,
    show colData2 (⟨136, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 15 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T136_40_2 = colFn colCertDiv_136_40_15.D2 (m := 5) from colCertDiv_136_40_15.bind2]
  rw [alnId_136 j hj]
  exact fastcode_of_div ⟨136, by decide⟩ _ _ _
    ((alnId_136 j hj) ▸ Q2.listedAt (⟨136, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨136, by decide⟩ : Fin 148) hj hq).1) colCertDiv_136_40_15_match


theorem leaf_136_40_20 (hp : 20 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 20 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨136, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp)) T136_40
      hfix136_40 hinj136_40 hcardT136_40
      (fun i => conj_mem_of_fixedPoints _ _ (T136_40 i) (hfix136_40 i) _)
      ⟨136, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 20 hp) Q2.T136_40_2 Q2.hfix136_40_2 Q2.hinj136_40_2
      Q2.hcardT136_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_40_2 i) (Q2.hfix136_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨136, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T136_40 = colFn colCertDiv_136_40_20.D1 (m := 5) from colCertDiv_136_40_20.bind1,
    show colData2 (⟨136, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 20 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T136_40_2 = colFn colCertDiv_136_40_20.D2 (m := 5) from colCertDiv_136_40_20.bind2]
  rw [alnId_136 j hj]
  exact fastcode_of_div ⟨136, by decide⟩ _ _ _
    ((alnId_136 j hj) ▸ Q2.listedAt (⟨136, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨136, by decide⟩ : Fin 148) hj hq).1) colCertDiv_136_40_20_match


theorem leaf_136_47_0 (hp : 0 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 0 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp)) T136_47
      hfix136_47 hinj136_47 hcardT136_47
      (fun i => conj_mem_of_fixedPoints _ _ (T136_47 i) (hfix136_47 i) _)
      ⟨136, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 0 hp) Q2.T136_47_2 Q2.hfix136_47_2 Q2.hinj136_47_2
      Q2.hcardT136_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_47_2 i) (Q2.hfix136_47_2 i) _)
      colCert_136_47_0.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_47_1 (hp : 1 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 1 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp)) T136_47
      hfix136_47 hinj136_47 hcardT136_47
      (fun i => conj_mem_of_fixedPoints _ _ (T136_47 i) (hfix136_47 i) _)
      ⟨136, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 1 hp) Q2.T136_47_2 Q2.hfix136_47_2 Q2.hinj136_47_2
      Q2.hcardT136_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_47_2 i) (Q2.hfix136_47_2 i) _)
      colCert_136_47_1.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_47_2 (hp : 2 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 2 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp)) T136_47
      hfix136_47 hinj136_47 hcardT136_47
      (fun i => conj_mem_of_fixedPoints _ _ (T136_47 i) (hfix136_47 i) _)
      ⟨136, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 2 hp) Q2.T136_47_2 Q2.hfix136_47_2 Q2.hinj136_47_2
      Q2.hcardT136_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_47_2 i) (Q2.hfix136_47_2 i) _)
      colCert_136_47_2.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_47_3 (hp : 3 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 3 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp)) T136_47
      hfix136_47 hinj136_47 hcardT136_47
      (fun i => conj_mem_of_fixedPoints _ _ (T136_47 i) (hfix136_47 i) _)
      ⟨136, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 3 hp) Q2.T136_47_2 Q2.hfix136_47_2 Q2.hinj136_47_2
      Q2.hcardT136_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_47_2 i) (Q2.hfix136_47_2 i) _)
      colCert_136_47_3.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_47_4 (hp : 4 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 4 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp)) T136_47
      hfix136_47 hinj136_47 hcardT136_47
      (fun i => conj_mem_of_fixedPoints _ _ (T136_47 i) (hfix136_47 i) _)
      ⟨136, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 4 hp) Q2.T136_47_2 Q2.hfix136_47_2 Q2.hinj136_47_2
      Q2.hcardT136_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_47_2 i) (Q2.hfix136_47_2 i) _)
      colCert_136_47_4.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_47_5 (hp : 5 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 5 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨136, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp)) T136_47
      hfix136_47 hinj136_47 hcardT136_47
      (fun i => conj_mem_of_fixedPoints _ _ (T136_47 i) (hfix136_47 i) _)
      ⟨136, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 5 hp) Q2.T136_47_2 Q2.hfix136_47_2 Q2.hinj136_47_2
      Q2.hcardT136_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_47_2 i) (Q2.hfix136_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨136, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T136_47 = colFn colCertDiv_136_47_5.D1 (m := 5) from colCertDiv_136_47_5.bind1,
    show colData2 (⟨136, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 5 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T136_47_2 = colFn colCertDiv_136_47_5.D2 (m := 5) from colCertDiv_136_47_5.bind2]
  rw [alnId_136 j hj]
  exact fastcode_of_div ⟨136, by decide⟩ _ _ _
    ((alnId_136 j hj) ▸ Q2.listedAt (⟨136, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨136, by decide⟩ : Fin 148) hj hq).1) colCertDiv_136_47_5_match


theorem leaf_136_47_10 (hp : 10 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 10 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨136, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp)) T136_47
      hfix136_47 hinj136_47 hcardT136_47
      (fun i => conj_mem_of_fixedPoints _ _ (T136_47 i) (hfix136_47 i) _)
      ⟨136, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 10 hp) Q2.T136_47_2 Q2.hfix136_47_2 Q2.hinj136_47_2
      Q2.hcardT136_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_47_2 i) (Q2.hfix136_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨136, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T136_47 = colFn colCertDiv_136_47_10.D1 (m := 5) from colCertDiv_136_47_10.bind1,
    show colData2 (⟨136, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 10 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T136_47_2 = colFn colCertDiv_136_47_10.D2 (m := 5) from colCertDiv_136_47_10.bind2]
  rw [alnId_136 j hj]
  exact fastcode_of_div ⟨136, by decide⟩ _ _ _
    ((alnId_136 j hj) ▸ Q2.listedAt (⟨136, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨136, by decide⟩ : Fin 148) hj hq).1) colCertDiv_136_47_10_match


theorem leaf_136_47_15 (hp : 15 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 15 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨136, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp)) T136_47
      hfix136_47 hinj136_47 hcardT136_47
      (fun i => conj_mem_of_fixedPoints _ _ (T136_47 i) (hfix136_47 i) _)
      ⟨136, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 15 hp) Q2.T136_47_2 Q2.hfix136_47_2 Q2.hinj136_47_2
      Q2.hcardT136_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_47_2 i) (Q2.hfix136_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨136, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T136_47 = colFn colCertDiv_136_47_15.D1 (m := 5) from colCertDiv_136_47_15.bind1,
    show colData2 (⟨136, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 15 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T136_47_2 = colFn colCertDiv_136_47_15.D2 (m := 5) from colCertDiv_136_47_15.bind2]
  rw [alnId_136 j hj]
  exact fastcode_of_div ⟨136, by decide⟩ _ _ _
    ((alnId_136 j hj) ▸ Q2.listedAt (⟨136, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨136, by decide⟩ : Fin 148) hj hq).1) colCertDiv_136_47_15_match


theorem leaf_136_47_20 (hp : 20 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 20 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨136, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp)) T136_47
      hfix136_47 hinj136_47 hcardT136_47
      (fun i => conj_mem_of_fixedPoints _ _ (T136_47 i) (hfix136_47 i) _)
      ⟨136, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 20 hp) Q2.T136_47_2 Q2.hfix136_47_2 Q2.hinj136_47_2
      Q2.hcardT136_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_47_2 i) (Q2.hfix136_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨136, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T136_47 = colFn colCertDiv_136_47_20.D1 (m := 5) from colCertDiv_136_47_20.bind1,
    show colData2 (⟨136, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 20 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T136_47_2 = colFn colCertDiv_136_47_20.D2 (m := 5) from colCertDiv_136_47_20.bind2]
  rw [alnId_136 j hj]
  exact fastcode_of_div ⟨136, by decide⟩ _ _ _
    ((alnId_136 j hj) ▸ Q2.listedAt (⟨136, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨136, by decide⟩ : Fin 148) hj hq).1) colCertDiv_136_47_20_match


theorem leaf_136_48_0 (hp : 0 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 0 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp)) T136_48
      hfix136_48 hinj136_48 hcardT136_48
      (fun i => conj_mem_of_fixedPoints _ _ (T136_48 i) (hfix136_48 i) _)
      ⟨136, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 0 hp) Q2.T136_48_2 Q2.hfix136_48_2 Q2.hinj136_48_2
      Q2.hcardT136_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_48_2 i) (Q2.hfix136_48_2 i) _)
      colCert_136_48_0.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_48_1 (hp : 1 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 1 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp)) T136_48
      hfix136_48 hinj136_48 hcardT136_48
      (fun i => conj_mem_of_fixedPoints _ _ (T136_48 i) (hfix136_48 i) _)
      ⟨136, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 1 hp) Q2.T136_48_2 Q2.hfix136_48_2 Q2.hinj136_48_2
      Q2.hcardT136_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_48_2 i) (Q2.hfix136_48_2 i) _)
      colCert_136_48_1.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_48_2 (hp : 2 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 2 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp)) T136_48
      hfix136_48 hinj136_48 hcardT136_48
      (fun i => conj_mem_of_fixedPoints _ _ (T136_48 i) (hfix136_48 i) _)
      ⟨136, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 2 hp) Q2.T136_48_2 Q2.hfix136_48_2 Q2.hinj136_48_2
      Q2.hcardT136_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_48_2 i) (Q2.hfix136_48_2 i) _)
      colCert_136_48_2.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_48_3 (hp : 3 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 3 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp)) T136_48
      hfix136_48 hinj136_48 hcardT136_48
      (fun i => conj_mem_of_fixedPoints _ _ (T136_48 i) (hfix136_48 i) _)
      ⟨136, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 3 hp) Q2.T136_48_2 Q2.hfix136_48_2 Q2.hinj136_48_2
      Q2.hcardT136_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_48_2 i) (Q2.hfix136_48_2 i) _)
      colCert_136_48_3.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_48_4 (hp : 4 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 4 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp)) T136_48
      hfix136_48 hinj136_48 hcardT136_48
      (fun i => conj_mem_of_fixedPoints _ _ (T136_48 i) (hfix136_48 i) _)
      ⟨136, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 4 hp) Q2.T136_48_2 Q2.hfix136_48_2 Q2.hinj136_48_2
      Q2.hcardT136_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_48_2 i) (Q2.hfix136_48_2 i) _)
      colCert_136_48_4.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_48_5 (hp : 5 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 5 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨136, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp)) T136_48
      hfix136_48 hinj136_48 hcardT136_48
      (fun i => conj_mem_of_fixedPoints _ _ (T136_48 i) (hfix136_48 i) _)
      ⟨136, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 5 hp) Q2.T136_48_2 Q2.hfix136_48_2 Q2.hinj136_48_2
      Q2.hcardT136_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_48_2 i) (Q2.hfix136_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨136, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T136_48 = colFn colCertDiv_136_48_5.D1 (m := 5) from colCertDiv_136_48_5.bind1,
    show colData2 (⟨136, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 5 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T136_48_2 = colFn colCertDiv_136_48_5.D2 (m := 5) from colCertDiv_136_48_5.bind2]
  rw [alnId_136 j hj]
  exact fastcode_of_div ⟨136, by decide⟩ _ _ _
    ((alnId_136 j hj) ▸ Q2.listedAt (⟨136, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨136, by decide⟩ : Fin 148) hj hq).1) colCertDiv_136_48_5_match


theorem leaf_136_48_10 (hp : 10 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 10 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨136, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp)) T136_48
      hfix136_48 hinj136_48 hcardT136_48
      (fun i => conj_mem_of_fixedPoints _ _ (T136_48 i) (hfix136_48 i) _)
      ⟨136, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 10 hp) Q2.T136_48_2 Q2.hfix136_48_2 Q2.hinj136_48_2
      Q2.hcardT136_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_48_2 i) (Q2.hfix136_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨136, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T136_48 = colFn colCertDiv_136_48_10.D1 (m := 5) from colCertDiv_136_48_10.bind1,
    show colData2 (⟨136, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 10 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T136_48_2 = colFn colCertDiv_136_48_10.D2 (m := 5) from colCertDiv_136_48_10.bind2]
  rw [alnId_136 j hj]
  exact fastcode_of_div ⟨136, by decide⟩ _ _ _
    ((alnId_136 j hj) ▸ Q2.listedAt (⟨136, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨136, by decide⟩ : Fin 148) hj hq).1) colCertDiv_136_48_10_match


theorem leaf_136_48_15 (hp : 15 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 15 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨136, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp)) T136_48
      hfix136_48 hinj136_48 hcardT136_48
      (fun i => conj_mem_of_fixedPoints _ _ (T136_48 i) (hfix136_48 i) _)
      ⟨136, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 15 hp) Q2.T136_48_2 Q2.hfix136_48_2 Q2.hinj136_48_2
      Q2.hcardT136_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_48_2 i) (Q2.hfix136_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨136, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T136_48 = colFn colCertDiv_136_48_15.D1 (m := 5) from colCertDiv_136_48_15.bind1,
    show colData2 (⟨136, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 15 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T136_48_2 = colFn colCertDiv_136_48_15.D2 (m := 5) from colCertDiv_136_48_15.bind2]
  rw [alnId_136 j hj]
  exact fastcode_of_div ⟨136, by decide⟩ _ _ _
    ((alnId_136 j hj) ▸ Q2.listedAt (⟨136, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨136, by decide⟩ : Fin 148) hj hq).1) colCertDiv_136_48_15_match


theorem leaf_136_48_20 (hp : 20 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 20 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨136, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp)) T136_48
      hfix136_48 hinj136_48 hcardT136_48
      (fun i => conj_mem_of_fixedPoints _ _ (T136_48 i) (hfix136_48 i) _)
      ⟨136, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 20 hp) Q2.T136_48_2 Q2.hfix136_48_2 Q2.hinj136_48_2
      Q2.hcardT136_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_48_2 i) (Q2.hfix136_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨136, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T136_48 = colFn colCertDiv_136_48_20.D1 (m := 5) from colCertDiv_136_48_20.bind1,
    show colData2 (⟨136, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 20 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T136_48_2 = colFn colCertDiv_136_48_20.D2 (m := 5) from colCertDiv_136_48_20.bind2]
  rw [alnId_136 j hj]
  exact fastcode_of_div ⟨136, by decide⟩ _ _ _
    ((alnId_136 j hj) ▸ Q2.listedAt (⟨136, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨136, by decide⟩ : Fin 148) hj hq).1) colCertDiv_136_48_20_match


theorem leaf_136_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T136_53
      hfix136_53 hinj136_53 hcardT136_53
      (fun i => conj_mem_of_fixedPoints _ _ (T136_53 i) (hfix136_53 i) _)
      ⟨136, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T136_53_2 Q2.hfix136_53_2 Q2.hinj136_53_2
      Q2.hcardT136_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_53_2 i) (Q2.hfix136_53_2 i) _)
      colCert_136_53_0.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T136_53
      hfix136_53 hinj136_53 hcardT136_53
      (fun i => conj_mem_of_fixedPoints _ _ (T136_53 i) (hfix136_53 i) _)
      ⟨136, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T136_53_2 Q2.hfix136_53_2 Q2.hinj136_53_2
      Q2.hcardT136_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_53_2 i) (Q2.hfix136_53_2 i) _)
      colCert_136_53_1.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T136_53
      hfix136_53 hinj136_53 hcardT136_53
      (fun i => conj_mem_of_fixedPoints _ _ (T136_53 i) (hfix136_53 i) _)
      ⟨136, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T136_53_2 Q2.hfix136_53_2 Q2.hinj136_53_2
      Q2.hcardT136_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_53_2 i) (Q2.hfix136_53_2 i) _)
      colCert_136_53_2.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T136_53
      hfix136_53 hinj136_53 hcardT136_53
      (fun i => conj_mem_of_fixedPoints _ _ (T136_53 i) (hfix136_53 i) _)
      ⟨136, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T136_53_2 Q2.hfix136_53_2 Q2.hinj136_53_2
      Q2.hcardT136_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_53_2 i) (Q2.hfix136_53_2 i) _)
      colCert_136_53_3.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T136_53
      hfix136_53 hinj136_53 hcardT136_53
      (fun i => conj_mem_of_fixedPoints _ _ (T136_53 i) (hfix136_53 i) _)
      ⟨136, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T136_53_2 Q2.hfix136_53_2 Q2.hinj136_53_2
      Q2.hcardT136_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_53_2 i) (Q2.hfix136_53_2 i) _)
      colCert_136_53_4.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T136_53
      hfix136_53 hinj136_53 hcardT136_53
      (fun i => conj_mem_of_fixedPoints _ _ (T136_53 i) (hfix136_53 i) _)
      ⟨136, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T136_53_2 Q2.hfix136_53_2 Q2.hinj136_53_2
      Q2.hcardT136_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_53_2 i) (Q2.hfix136_53_2 i) _)
      colCert_136_53_5.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T136_53
      hfix136_53 hinj136_53 hcardT136_53
      (fun i => conj_mem_of_fixedPoints _ _ (T136_53 i) (hfix136_53 i) _)
      ⟨136, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T136_53_2 Q2.hfix136_53_2 Q2.hinj136_53_2
      Q2.hcardT136_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_53_2 i) (Q2.hfix136_53_2 i) _)
      colCert_136_53_10.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T136_53
      hfix136_53 hinj136_53 hcardT136_53
      (fun i => conj_mem_of_fixedPoints _ _ (T136_53 i) (hfix136_53 i) _)
      ⟨136, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T136_53_2 Q2.hfix136_53_2 Q2.hinj136_53_2
      Q2.hcardT136_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_53_2 i) (Q2.hfix136_53_2 i) _)
      colCert_136_53_15.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T136_53
      hfix136_53 hinj136_53 hcardT136_53
      (fun i => conj_mem_of_fixedPoints _ _ (T136_53 i) (hfix136_53 i) _)
      ⟨136, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T136_53_2 Q2.hfix136_53_2 Q2.hinj136_53_2
      Q2.hcardT136_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_53_2 i) (Q2.hfix136_53_2 i) _)
      colCert_136_53_20.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_84_0 (hp : 0 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 0 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 0 (transLenTr ⟨84, by decide⟩ 0 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 0 (transLenTr ⟨84, by decide⟩ 0 hp)) T136_84
      hfix136_84 hinj136_84 hcardT136_84
      (fun i => conj_mem_of_fixedPoints _ _ (T136_84 i) (hfix136_84 i) _)
      ⟨136, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 0 hp) Q2.T136_84_2 Q2.hfix136_84_2 Q2.hinj136_84_2
      Q2.hcardT136_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_84_2 i) (Q2.hfix136_84_2 i) _)
      colCert_136_84_0.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_84_1 (hp : 1 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 1 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 1 (transLenTr ⟨84, by decide⟩ 1 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 1 (transLenTr ⟨84, by decide⟩ 1 hp)) T136_84
      hfix136_84 hinj136_84 hcardT136_84
      (fun i => conj_mem_of_fixedPoints _ _ (T136_84 i) (hfix136_84 i) _)
      ⟨136, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 1 hp) Q2.T136_84_2 Q2.hfix136_84_2 Q2.hinj136_84_2
      Q2.hcardT136_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_84_2 i) (Q2.hfix136_84_2 i) _)
      colCert_136_84_1.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_84_2 (hp : 2 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 2 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 2 (transLenTr ⟨84, by decide⟩ 2 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 2 (transLenTr ⟨84, by decide⟩ 2 hp)) T136_84
      hfix136_84 hinj136_84 hcardT136_84
      (fun i => conj_mem_of_fixedPoints _ _ (T136_84 i) (hfix136_84 i) _)
      ⟨136, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 2 hp) Q2.T136_84_2 Q2.hfix136_84_2 Q2.hinj136_84_2
      Q2.hcardT136_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_84_2 i) (Q2.hfix136_84_2 i) _)
      colCert_136_84_2.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_84_3 (hp : 3 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 3 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 3 (transLenTr ⟨84, by decide⟩ 3 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 3 (transLenTr ⟨84, by decide⟩ 3 hp)) T136_84
      hfix136_84 hinj136_84 hcardT136_84
      (fun i => conj_mem_of_fixedPoints _ _ (T136_84 i) (hfix136_84 i) _)
      ⟨136, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 3 hp) Q2.T136_84_2 Q2.hfix136_84_2 Q2.hinj136_84_2
      Q2.hcardT136_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_84_2 i) (Q2.hfix136_84_2 i) _)
      colCert_136_84_3.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_84_4 (hp : 4 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 4 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 4 (transLenTr ⟨84, by decide⟩ 4 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 4 (transLenTr ⟨84, by decide⟩ 4 hp)) T136_84
      hfix136_84 hinj136_84 hcardT136_84
      (fun i => conj_mem_of_fixedPoints _ _ (T136_84 i) (hfix136_84 i) _)
      ⟨136, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 4 hp) Q2.T136_84_2 Q2.hfix136_84_2 Q2.hinj136_84_2
      Q2.hcardT136_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_84_2 i) (Q2.hfix136_84_2 i) _)
      colCert_136_84_4.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_84_5 (hp : 5 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 5 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 5 (transLenTr ⟨84, by decide⟩ 5 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 5 (transLenTr ⟨84, by decide⟩ 5 hp)) T136_84
      hfix136_84 hinj136_84 hcardT136_84
      (fun i => conj_mem_of_fixedPoints _ _ (T136_84 i) (hfix136_84 i) _)
      ⟨136, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 5 hp) Q2.T136_84_2 Q2.hfix136_84_2 Q2.hinj136_84_2
      Q2.hcardT136_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_84_2 i) (Q2.hfix136_84_2 i) _)
      colCert_136_84_5.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_84_10 (hp : 10 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 10 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 10 (transLenTr ⟨84, by decide⟩ 10 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 10 (transLenTr ⟨84, by decide⟩ 10 hp)) T136_84
      hfix136_84 hinj136_84 hcardT136_84
      (fun i => conj_mem_of_fixedPoints _ _ (T136_84 i) (hfix136_84 i) _)
      ⟨136, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 10 hp) Q2.T136_84_2 Q2.hfix136_84_2 Q2.hinj136_84_2
      Q2.hcardT136_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_84_2 i) (Q2.hfix136_84_2 i) _)
      colCert_136_84_10.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_84_15 (hp : 15 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 15 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 15 (transLenTr ⟨84, by decide⟩ 15 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 15 (transLenTr ⟨84, by decide⟩ 15 hp)) T136_84
      hfix136_84 hinj136_84 hcardT136_84
      (fun i => conj_mem_of_fixedPoints _ _ (T136_84 i) (hfix136_84 i) _)
      ⟨136, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 15 hp) Q2.T136_84_2 Q2.hfix136_84_2 Q2.hinj136_84_2
      Q2.hcardT136_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_84_2 i) (Q2.hfix136_84_2 i) _)
      colCert_136_84_15.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_84_20 (hp : 20 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 20 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 20 (transLenTr ⟨84, by decide⟩ 20 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 20 (transLenTr ⟨84, by decide⟩ 20 hp)) T136_84
      hfix136_84 hinj136_84 hcardT136_84
      (fun i => conj_mem_of_fixedPoints _ _ (T136_84 i) (hfix136_84 i) _)
      ⟨136, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 20 hp) Q2.T136_84_2 Q2.hfix136_84_2 Q2.hinj136_84_2
      Q2.hcardT136_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_84_2 i) (Q2.hfix136_84_2 i) _)
      colCert_136_84_20.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_91_0 (hp : 0 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 0 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 0 (transLenTr ⟨91, by decide⟩ 0 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 0 (transLenTr ⟨91, by decide⟩ 0 hp)) T136_91
      hfix136_91 hinj136_91 hcardT136_91
      (fun i => conj_mem_of_fixedPoints _ _ (T136_91 i) (hfix136_91 i) _)
      ⟨136, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 0 hp) Q2.T136_91_2 Q2.hfix136_91_2 Q2.hinj136_91_2
      Q2.hcardT136_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_91_2 i) (Q2.hfix136_91_2 i) _)
      colCert_136_91_0.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_91_1 (hp : 1 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 1 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 1 (transLenTr ⟨91, by decide⟩ 1 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 1 (transLenTr ⟨91, by decide⟩ 1 hp)) T136_91
      hfix136_91 hinj136_91 hcardT136_91
      (fun i => conj_mem_of_fixedPoints _ _ (T136_91 i) (hfix136_91 i) _)
      ⟨136, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 1 hp) Q2.T136_91_2 Q2.hfix136_91_2 Q2.hinj136_91_2
      Q2.hcardT136_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_91_2 i) (Q2.hfix136_91_2 i) _)
      colCert_136_91_1.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_91_2 (hp : 2 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 2 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 2 (transLenTr ⟨91, by decide⟩ 2 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 2 (transLenTr ⟨91, by decide⟩ 2 hp)) T136_91
      hfix136_91 hinj136_91 hcardT136_91
      (fun i => conj_mem_of_fixedPoints _ _ (T136_91 i) (hfix136_91 i) _)
      ⟨136, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 2 hp) Q2.T136_91_2 Q2.hfix136_91_2 Q2.hinj136_91_2
      Q2.hcardT136_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_91_2 i) (Q2.hfix136_91_2 i) _)
      colCert_136_91_2.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_91_3 (hp : 3 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 3 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 3 (transLenTr ⟨91, by decide⟩ 3 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 3 (transLenTr ⟨91, by decide⟩ 3 hp)) T136_91
      hfix136_91 hinj136_91 hcardT136_91
      (fun i => conj_mem_of_fixedPoints _ _ (T136_91 i) (hfix136_91 i) _)
      ⟨136, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 3 hp) Q2.T136_91_2 Q2.hfix136_91_2 Q2.hinj136_91_2
      Q2.hcardT136_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_91_2 i) (Q2.hfix136_91_2 i) _)
      colCert_136_91_3.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_91_4 (hp : 4 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 4 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 4 (transLenTr ⟨91, by decide⟩ 4 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 4 (transLenTr ⟨91, by decide⟩ 4 hp)) T136_91
      hfix136_91 hinj136_91 hcardT136_91
      (fun i => conj_mem_of_fixedPoints _ _ (T136_91 i) (hfix136_91 i) _)
      ⟨136, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 4 hp) Q2.T136_91_2 Q2.hfix136_91_2 Q2.hinj136_91_2
      Q2.hcardT136_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_91_2 i) (Q2.hfix136_91_2 i) _)
      colCert_136_91_4.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_91_5 (hp : 5 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 5 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 5 (transLenTr ⟨91, by decide⟩ 5 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 5 (transLenTr ⟨91, by decide⟩ 5 hp)) T136_91
      hfix136_91 hinj136_91 hcardT136_91
      (fun i => conj_mem_of_fixedPoints _ _ (T136_91 i) (hfix136_91 i) _)
      ⟨136, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 5 hp) Q2.T136_91_2 Q2.hfix136_91_2 Q2.hinj136_91_2
      Q2.hcardT136_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_91_2 i) (Q2.hfix136_91_2 i) _)
      colCert_136_91_5.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_91_10 (hp : 10 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 10 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 10 (transLenTr ⟨91, by decide⟩ 10 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨136, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 10 (transLenTr ⟨91, by decide⟩ 10 hp)) T136_91
      hfix136_91 hinj136_91 hcardT136_91
      (fun i => conj_mem_of_fixedPoints _ _ (T136_91 i) (hfix136_91 i) _)
      ⟨136, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 10 hp) Q2.T136_91_2 Q2.hfix136_91_2 Q2.hinj136_91_2
      Q2.hcardT136_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_91_2 i) (Q2.hfix136_91_2 i) _)
      ?_).symm
  rw [show colData1 (⟨136, by decide⟩ : Fin 148)
        ((colE1 ⟨91, by decide⟩ 10 (transLenTr ⟨91, by decide⟩ 10 hp) : ↥(reps ⟨91, by decide⟩)) : Coordinate 1)
        T136_91 = colFn colCertDiv_136_91_10.D1 (m := 5) from colCertDiv_136_91_10.bind1,
    show colData2 (⟨136, by decide⟩ : Fin 148)
        ((colE2 ⟨91, by decide⟩ 10 hp : ↥(Q2.reps ⟨91, by decide⟩)) : Coordinate 2)
        Q2.T136_91_2 = colFn colCertDiv_136_91_10.D2 (m := 5) from colCertDiv_136_91_10.bind2]
  rw [alnId_136 j hj]
  exact fastcode_of_div ⟨136, by decide⟩ _ _ _
    ((alnId_136 j hj) ▸ Q2.listedAt (⟨136, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨136, by decide⟩ : Fin 148) hj hq).1) colCertDiv_136_91_10_match


theorem leaf_136_91_15 (hp : 15 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 15 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 15 (transLenTr ⟨91, by decide⟩ 15 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨136, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 15 (transLenTr ⟨91, by decide⟩ 15 hp)) T136_91
      hfix136_91 hinj136_91 hcardT136_91
      (fun i => conj_mem_of_fixedPoints _ _ (T136_91 i) (hfix136_91 i) _)
      ⟨136, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 15 hp) Q2.T136_91_2 Q2.hfix136_91_2 Q2.hinj136_91_2
      Q2.hcardT136_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_91_2 i) (Q2.hfix136_91_2 i) _)
      ?_).symm
  rw [show colData1 (⟨136, by decide⟩ : Fin 148)
        ((colE1 ⟨91, by decide⟩ 15 (transLenTr ⟨91, by decide⟩ 15 hp) : ↥(reps ⟨91, by decide⟩)) : Coordinate 1)
        T136_91 = colFn colCertDiv_136_91_15.D1 (m := 5) from colCertDiv_136_91_15.bind1,
    show colData2 (⟨136, by decide⟩ : Fin 148)
        ((colE2 ⟨91, by decide⟩ 15 hp : ↥(Q2.reps ⟨91, by decide⟩)) : Coordinate 2)
        Q2.T136_91_2 = colFn colCertDiv_136_91_15.D2 (m := 5) from colCertDiv_136_91_15.bind2]
  rw [alnId_136 j hj]
  exact fastcode_of_div ⟨136, by decide⟩ _ _ _
    ((alnId_136 j hj) ▸ Q2.listedAt (⟨136, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨136, by decide⟩ : Fin 148) hj hq).1) colCertDiv_136_91_15_match


theorem leaf_136_91_20 (hp : 20 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 20 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 20 (transLenTr ⟨91, by decide⟩ 20 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨136, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 20 (transLenTr ⟨91, by decide⟩ 20 hp)) T136_91
      hfix136_91 hinj136_91 hcardT136_91
      (fun i => conj_mem_of_fixedPoints _ _ (T136_91 i) (hfix136_91 i) _)
      ⟨136, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 20 hp) Q2.T136_91_2 Q2.hfix136_91_2 Q2.hinj136_91_2
      Q2.hcardT136_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_91_2 i) (Q2.hfix136_91_2 i) _)
      ?_).symm
  rw [show colData1 (⟨136, by decide⟩ : Fin 148)
        ((colE1 ⟨91, by decide⟩ 20 (transLenTr ⟨91, by decide⟩ 20 hp) : ↥(reps ⟨91, by decide⟩)) : Coordinate 1)
        T136_91 = colFn colCertDiv_136_91_20.D1 (m := 5) from colCertDiv_136_91_20.bind1,
    show colData2 (⟨136, by decide⟩ : Fin 148)
        ((colE2 ⟨91, by decide⟩ 20 hp : ↥(Q2.reps ⟨91, by decide⟩)) : Coordinate 2)
        Q2.T136_91_2 = colFn colCertDiv_136_91_20.D2 (m := 5) from colCertDiv_136_91_20.bind2]
  rw [alnId_136 j hj]
  exact fastcode_of_div ⟨136, by decide⟩ _ _ _
    ((alnId_136 j hj) ▸ Q2.listedAt (⟨136, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨136, by decide⟩ : Fin 148) hj hq).1) colCertDiv_136_91_20_match


theorem leaf_136_98_0 (hp : 0 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 0 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 0 (transLenTr ⟨98, by decide⟩ 0 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 0 (transLenTr ⟨98, by decide⟩ 0 hp)) T136_98
      hfix136_98 hinj136_98 hcardT136_98
      (fun i => conj_mem_of_fixedPoints _ _ (T136_98 i) (hfix136_98 i) _)
      ⟨136, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 0 hp) Q2.T136_98_2 Q2.hfix136_98_2 Q2.hinj136_98_2
      Q2.hcardT136_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_98_2 i) (Q2.hfix136_98_2 i) _)
      colCert_136_98_0.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_98_1 (hp : 1 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 1 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 1 (transLenTr ⟨98, by decide⟩ 1 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 1 (transLenTr ⟨98, by decide⟩ 1 hp)) T136_98
      hfix136_98 hinj136_98 hcardT136_98
      (fun i => conj_mem_of_fixedPoints _ _ (T136_98 i) (hfix136_98 i) _)
      ⟨136, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 1 hp) Q2.T136_98_2 Q2.hfix136_98_2 Q2.hinj136_98_2
      Q2.hcardT136_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_98_2 i) (Q2.hfix136_98_2 i) _)
      colCert_136_98_1.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_98_2 (hp : 2 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 2 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 2 (transLenTr ⟨98, by decide⟩ 2 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 2 (transLenTr ⟨98, by decide⟩ 2 hp)) T136_98
      hfix136_98 hinj136_98 hcardT136_98
      (fun i => conj_mem_of_fixedPoints _ _ (T136_98 i) (hfix136_98 i) _)
      ⟨136, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 2 hp) Q2.T136_98_2 Q2.hfix136_98_2 Q2.hinj136_98_2
      Q2.hcardT136_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_98_2 i) (Q2.hfix136_98_2 i) _)
      colCert_136_98_2.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_98_3 (hp : 3 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 3 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 3 (transLenTr ⟨98, by decide⟩ 3 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 3 (transLenTr ⟨98, by decide⟩ 3 hp)) T136_98
      hfix136_98 hinj136_98 hcardT136_98
      (fun i => conj_mem_of_fixedPoints _ _ (T136_98 i) (hfix136_98 i) _)
      ⟨136, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 3 hp) Q2.T136_98_2 Q2.hfix136_98_2 Q2.hinj136_98_2
      Q2.hcardT136_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_98_2 i) (Q2.hfix136_98_2 i) _)
      colCert_136_98_3.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_98_4 (hp : 4 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 4 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 4 (transLenTr ⟨98, by decide⟩ 4 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 4 (transLenTr ⟨98, by decide⟩ 4 hp)) T136_98
      hfix136_98 hinj136_98 hcardT136_98
      (fun i => conj_mem_of_fixedPoints _ _ (T136_98 i) (hfix136_98 i) _)
      ⟨136, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 4 hp) Q2.T136_98_2 Q2.hfix136_98_2 Q2.hinj136_98_2
      Q2.hcardT136_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_98_2 i) (Q2.hfix136_98_2 i) _)
      colCert_136_98_4.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_98_5 (hp : 5 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 5 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 5 (transLenTr ⟨98, by decide⟩ 5 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 5 (transLenTr ⟨98, by decide⟩ 5 hp)) T136_98
      hfix136_98 hinj136_98 hcardT136_98
      (fun i => conj_mem_of_fixedPoints _ _ (T136_98 i) (hfix136_98 i) _)
      ⟨136, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 5 hp) Q2.T136_98_2 Q2.hfix136_98_2 Q2.hinj136_98_2
      Q2.hcardT136_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_98_2 i) (Q2.hfix136_98_2 i) _)
      colCert_136_98_5.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_98_10 (hp : 10 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 10 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 10 (transLenTr ⟨98, by decide⟩ 10 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨136, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 10 (transLenTr ⟨98, by decide⟩ 10 hp)) T136_98
      hfix136_98 hinj136_98 hcardT136_98
      (fun i => conj_mem_of_fixedPoints _ _ (T136_98 i) (hfix136_98 i) _)
      ⟨136, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 10 hp) Q2.T136_98_2 Q2.hfix136_98_2 Q2.hinj136_98_2
      Q2.hcardT136_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_98_2 i) (Q2.hfix136_98_2 i) _)
      ?_).symm
  rw [show colData1 (⟨136, by decide⟩ : Fin 148)
        ((colE1 ⟨98, by decide⟩ 10 (transLenTr ⟨98, by decide⟩ 10 hp) : ↥(reps ⟨98, by decide⟩)) : Coordinate 1)
        T136_98 = colFn colCertDiv_136_98_10.D1 (m := 5) from colCertDiv_136_98_10.bind1,
    show colData2 (⟨136, by decide⟩ : Fin 148)
        ((colE2 ⟨98, by decide⟩ 10 hp : ↥(Q2.reps ⟨98, by decide⟩)) : Coordinate 2)
        Q2.T136_98_2 = colFn colCertDiv_136_98_10.D2 (m := 5) from colCertDiv_136_98_10.bind2]
  rw [alnId_136 j hj]
  exact fastcode_of_div ⟨136, by decide⟩ _ _ _
    ((alnId_136 j hj) ▸ Q2.listedAt (⟨136, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨136, by decide⟩ : Fin 148) hj hq).1) colCertDiv_136_98_10_match


theorem leaf_136_98_15 (hp : 15 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 15 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 15 (transLenTr ⟨98, by decide⟩ 15 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨136, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 15 (transLenTr ⟨98, by decide⟩ 15 hp)) T136_98
      hfix136_98 hinj136_98 hcardT136_98
      (fun i => conj_mem_of_fixedPoints _ _ (T136_98 i) (hfix136_98 i) _)
      ⟨136, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 15 hp) Q2.T136_98_2 Q2.hfix136_98_2 Q2.hinj136_98_2
      Q2.hcardT136_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_98_2 i) (Q2.hfix136_98_2 i) _)
      ?_).symm
  rw [show colData1 (⟨136, by decide⟩ : Fin 148)
        ((colE1 ⟨98, by decide⟩ 15 (transLenTr ⟨98, by decide⟩ 15 hp) : ↥(reps ⟨98, by decide⟩)) : Coordinate 1)
        T136_98 = colFn colCertDiv_136_98_15.D1 (m := 5) from colCertDiv_136_98_15.bind1,
    show colData2 (⟨136, by decide⟩ : Fin 148)
        ((colE2 ⟨98, by decide⟩ 15 hp : ↥(Q2.reps ⟨98, by decide⟩)) : Coordinate 2)
        Q2.T136_98_2 = colFn colCertDiv_136_98_15.D2 (m := 5) from colCertDiv_136_98_15.bind2]
  rw [alnId_136 j hj]
  exact fastcode_of_div ⟨136, by decide⟩ _ _ _
    ((alnId_136 j hj) ▸ Q2.listedAt (⟨136, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨136, by decide⟩ : Fin 148) hj hq).1) colCertDiv_136_98_15_match


theorem leaf_136_98_20 (hp : 20 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 20 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 20 (transLenTr ⟨98, by decide⟩ 20 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨136, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 20 (transLenTr ⟨98, by decide⟩ 20 hp)) T136_98
      hfix136_98 hinj136_98 hcardT136_98
      (fun i => conj_mem_of_fixedPoints _ _ (T136_98 i) (hfix136_98 i) _)
      ⟨136, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 20 hp) Q2.T136_98_2 Q2.hfix136_98_2 Q2.hinj136_98_2
      Q2.hcardT136_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_98_2 i) (Q2.hfix136_98_2 i) _)
      ?_).symm
  rw [show colData1 (⟨136, by decide⟩ : Fin 148)
        ((colE1 ⟨98, by decide⟩ 20 (transLenTr ⟨98, by decide⟩ 20 hp) : ↥(reps ⟨98, by decide⟩)) : Coordinate 1)
        T136_98 = colFn colCertDiv_136_98_20.D1 (m := 5) from colCertDiv_136_98_20.bind1,
    show colData2 (⟨136, by decide⟩ : Fin 148)
        ((colE2 ⟨98, by decide⟩ 20 hp : ↥(Q2.reps ⟨98, by decide⟩)) : Coordinate 2)
        Q2.T136_98_2 = colFn colCertDiv_136_98_20.D2 (m := 5) from colCertDiv_136_98_20.bind2]
  rw [alnId_136 j hj]
  exact fastcode_of_div ⟨136, by decide⟩ _ _ _
    ((alnId_136 j hj) ▸ Q2.listedAt (⟨136, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨136, by decide⟩ : Fin 148) hj hq).1) colCertDiv_136_98_20_match


theorem leaf_136_102_0 (hp : 0 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 0 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 0 (transLenTr ⟨102, by decide⟩ 0 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 0 (transLenTr ⟨102, by decide⟩ 0 hp)) T136_102
      hfix136_102 hinj136_102 hcardT136_102
      (fun i => conj_mem_of_fixedPoints _ _ (T136_102 i) (hfix136_102 i) _)
      ⟨136, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 0 hp) Q2.T136_102_2 Q2.hfix136_102_2 Q2.hinj136_102_2
      Q2.hcardT136_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_102_2 i) (Q2.hfix136_102_2 i) _)
      colCert_136_102_0.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_102_1 (hp : 1 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 1 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 1 (transLenTr ⟨102, by decide⟩ 1 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 1 (transLenTr ⟨102, by decide⟩ 1 hp)) T136_102
      hfix136_102 hinj136_102 hcardT136_102
      (fun i => conj_mem_of_fixedPoints _ _ (T136_102 i) (hfix136_102 i) _)
      ⟨136, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 1 hp) Q2.T136_102_2 Q2.hfix136_102_2 Q2.hinj136_102_2
      Q2.hcardT136_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_102_2 i) (Q2.hfix136_102_2 i) _)
      colCert_136_102_1.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_102_2 (hp : 2 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 2 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 2 (transLenTr ⟨102, by decide⟩ 2 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 2 (transLenTr ⟨102, by decide⟩ 2 hp)) T136_102
      hfix136_102 hinj136_102 hcardT136_102
      (fun i => conj_mem_of_fixedPoints _ _ (T136_102 i) (hfix136_102 i) _)
      ⟨136, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 2 hp) Q2.T136_102_2 Q2.hfix136_102_2 Q2.hinj136_102_2
      Q2.hcardT136_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_102_2 i) (Q2.hfix136_102_2 i) _)
      colCert_136_102_2.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_102_3 (hp : 3 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 3 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 3 (transLenTr ⟨102, by decide⟩ 3 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 3 (transLenTr ⟨102, by decide⟩ 3 hp)) T136_102
      hfix136_102 hinj136_102 hcardT136_102
      (fun i => conj_mem_of_fixedPoints _ _ (T136_102 i) (hfix136_102 i) _)
      ⟨136, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 3 hp) Q2.T136_102_2 Q2.hfix136_102_2 Q2.hinj136_102_2
      Q2.hcardT136_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_102_2 i) (Q2.hfix136_102_2 i) _)
      colCert_136_102_3.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_102_4 (hp : 4 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 4 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 4 (transLenTr ⟨102, by decide⟩ 4 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 4 (transLenTr ⟨102, by decide⟩ 4 hp)) T136_102
      hfix136_102 hinj136_102 hcardT136_102
      (fun i => conj_mem_of_fixedPoints _ _ (T136_102 i) (hfix136_102 i) _)
      ⟨136, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 4 hp) Q2.T136_102_2 Q2.hfix136_102_2 Q2.hinj136_102_2
      Q2.hcardT136_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_102_2 i) (Q2.hfix136_102_2 i) _)
      colCert_136_102_4.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_102_5 (hp : 5 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 5 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 5 (transLenTr ⟨102, by decide⟩ 5 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 5 (transLenTr ⟨102, by decide⟩ 5 hp)) T136_102
      hfix136_102 hinj136_102 hcardT136_102
      (fun i => conj_mem_of_fixedPoints _ _ (T136_102 i) (hfix136_102 i) _)
      ⟨136, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 5 hp) Q2.T136_102_2 Q2.hfix136_102_2 Q2.hinj136_102_2
      Q2.hcardT136_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_102_2 i) (Q2.hfix136_102_2 i) _)
      colCert_136_102_5.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_102_10 (hp : 10 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 10 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 10 (transLenTr ⟨102, by decide⟩ 10 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 10 (transLenTr ⟨102, by decide⟩ 10 hp)) T136_102
      hfix136_102 hinj136_102 hcardT136_102
      (fun i => conj_mem_of_fixedPoints _ _ (T136_102 i) (hfix136_102 i) _)
      ⟨136, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 10 hp) Q2.T136_102_2 Q2.hfix136_102_2 Q2.hinj136_102_2
      Q2.hcardT136_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_102_2 i) (Q2.hfix136_102_2 i) _)
      colCert_136_102_10.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_102_15 (hp : 15 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 15 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 15 (transLenTr ⟨102, by decide⟩ 15 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨136, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 15 (transLenTr ⟨102, by decide⟩ 15 hp)) T136_102
      hfix136_102 hinj136_102 hcardT136_102
      (fun i => conj_mem_of_fixedPoints _ _ (T136_102 i) (hfix136_102 i) _)
      ⟨136, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 15 hp) Q2.T136_102_2 Q2.hfix136_102_2 Q2.hinj136_102_2
      Q2.hcardT136_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_102_2 i) (Q2.hfix136_102_2 i) _)
      ?_).symm
  rw [show colData1 (⟨136, by decide⟩ : Fin 148)
        ((colE1 ⟨102, by decide⟩ 15 (transLenTr ⟨102, by decide⟩ 15 hp) : ↥(reps ⟨102, by decide⟩)) : Coordinate 1)
        T136_102 = colFn colCertDiv_136_102_15.D1 (m := 5) from colCertDiv_136_102_15.bind1,
    show colData2 (⟨136, by decide⟩ : Fin 148)
        ((colE2 ⟨102, by decide⟩ 15 hp : ↥(Q2.reps ⟨102, by decide⟩)) : Coordinate 2)
        Q2.T136_102_2 = colFn colCertDiv_136_102_15.D2 (m := 5) from colCertDiv_136_102_15.bind2]
  rw [alnId_136 j hj]
  exact fastcode_of_div ⟨136, by decide⟩ _ _ _
    ((alnId_136 j hj) ▸ Q2.listedAt (⟨136, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨136, by decide⟩ : Fin 148) hj hq).1) colCertDiv_136_102_15_match


theorem leaf_136_102_20 (hp : 20 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 20 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 20 (transLenTr ⟨102, by decide⟩ 20 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨136, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 20 (transLenTr ⟨102, by decide⟩ 20 hp)) T136_102
      hfix136_102 hinj136_102 hcardT136_102
      (fun i => conj_mem_of_fixedPoints _ _ (T136_102 i) (hfix136_102 i) _)
      ⟨136, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 20 hp) Q2.T136_102_2 Q2.hfix136_102_2 Q2.hinj136_102_2
      Q2.hcardT136_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_102_2 i) (Q2.hfix136_102_2 i) _)
      ?_).symm
  rw [show colData1 (⟨136, by decide⟩ : Fin 148)
        ((colE1 ⟨102, by decide⟩ 20 (transLenTr ⟨102, by decide⟩ 20 hp) : ↥(reps ⟨102, by decide⟩)) : Coordinate 1)
        T136_102 = colFn colCertDiv_136_102_20.D1 (m := 5) from colCertDiv_136_102_20.bind1,
    show colData2 (⟨136, by decide⟩ : Fin 148)
        ((colE2 ⟨102, by decide⟩ 20 hp : ↥(Q2.reps ⟨102, by decide⟩)) : Coordinate 2)
        Q2.T136_102_2 = colFn colCertDiv_136_102_20.D2 (m := 5) from colCertDiv_136_102_20.bind2]
  rw [alnId_136 j hj]
  exact fastcode_of_div ⟨136, by decide⟩ _ _ _
    ((alnId_136 j hj) ▸ Q2.listedAt (⟨136, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨136, by decide⟩ : Fin 148) hj hq).1) colCertDiv_136_102_20_match


theorem leaf_136_109_0 (hp : 0 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 0 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 0 (transLenTr ⟨109, by decide⟩ 0 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 0 (transLenTr ⟨109, by decide⟩ 0 hp)) T136_109
      hfix136_109 hinj136_109 hcardT136_109
      (fun i => conj_mem_of_fixedPoints _ _ (T136_109 i) (hfix136_109 i) _)
      ⟨136, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 0 hp) Q2.T136_109_2 Q2.hfix136_109_2 Q2.hinj136_109_2
      Q2.hcardT136_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_109_2 i) (Q2.hfix136_109_2 i) _)
      colCert_136_109_0.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_109_1 (hp : 1 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 1 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 1 (transLenTr ⟨109, by decide⟩ 1 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 1 (transLenTr ⟨109, by decide⟩ 1 hp)) T136_109
      hfix136_109 hinj136_109 hcardT136_109
      (fun i => conj_mem_of_fixedPoints _ _ (T136_109 i) (hfix136_109 i) _)
      ⟨136, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 1 hp) Q2.T136_109_2 Q2.hfix136_109_2 Q2.hinj136_109_2
      Q2.hcardT136_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_109_2 i) (Q2.hfix136_109_2 i) _)
      colCert_136_109_1.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_109_2 (hp : 2 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 2 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 2 (transLenTr ⟨109, by decide⟩ 2 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 2 (transLenTr ⟨109, by decide⟩ 2 hp)) T136_109
      hfix136_109 hinj136_109 hcardT136_109
      (fun i => conj_mem_of_fixedPoints _ _ (T136_109 i) (hfix136_109 i) _)
      ⟨136, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 2 hp) Q2.T136_109_2 Q2.hfix136_109_2 Q2.hinj136_109_2
      Q2.hcardT136_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_109_2 i) (Q2.hfix136_109_2 i) _)
      colCert_136_109_2.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_109_3 (hp : 3 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 3 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 3 (transLenTr ⟨109, by decide⟩ 3 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 3 (transLenTr ⟨109, by decide⟩ 3 hp)) T136_109
      hfix136_109 hinj136_109 hcardT136_109
      (fun i => conj_mem_of_fixedPoints _ _ (T136_109 i) (hfix136_109 i) _)
      ⟨136, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 3 hp) Q2.T136_109_2 Q2.hfix136_109_2 Q2.hinj136_109_2
      Q2.hcardT136_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_109_2 i) (Q2.hfix136_109_2 i) _)
      colCert_136_109_3.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_109_4 (hp : 4 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 4 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 4 (transLenTr ⟨109, by decide⟩ 4 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 4 (transLenTr ⟨109, by decide⟩ 4 hp)) T136_109
      hfix136_109 hinj136_109 hcardT136_109
      (fun i => conj_mem_of_fixedPoints _ _ (T136_109 i) (hfix136_109 i) _)
      ⟨136, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 4 hp) Q2.T136_109_2 Q2.hfix136_109_2 Q2.hinj136_109_2
      Q2.hcardT136_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_109_2 i) (Q2.hfix136_109_2 i) _)
      colCert_136_109_4.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_109_5 (hp : 5 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 5 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 5 (transLenTr ⟨109, by decide⟩ 5 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 5 (transLenTr ⟨109, by decide⟩ 5 hp)) T136_109
      hfix136_109 hinj136_109 hcardT136_109
      (fun i => conj_mem_of_fixedPoints _ _ (T136_109 i) (hfix136_109 i) _)
      ⟨136, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 5 hp) Q2.T136_109_2 Q2.hfix136_109_2 Q2.hinj136_109_2
      Q2.hcardT136_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_109_2 i) (Q2.hfix136_109_2 i) _)
      colCert_136_109_5.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_109_10 (hp : 10 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 10 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 10 (transLenTr ⟨109, by decide⟩ 10 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 10 (transLenTr ⟨109, by decide⟩ 10 hp)) T136_109
      hfix136_109 hinj136_109 hcardT136_109
      (fun i => conj_mem_of_fixedPoints _ _ (T136_109 i) (hfix136_109 i) _)
      ⟨136, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 10 hp) Q2.T136_109_2 Q2.hfix136_109_2 Q2.hinj136_109_2
      Q2.hcardT136_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_109_2 i) (Q2.hfix136_109_2 i) _)
      colCert_136_109_10.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_109_15 (hp : 15 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 15 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 15 (transLenTr ⟨109, by decide⟩ 15 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 15 (transLenTr ⟨109, by decide⟩ 15 hp)) T136_109
      hfix136_109 hinj136_109 hcardT136_109
      (fun i => conj_mem_of_fixedPoints _ _ (T136_109 i) (hfix136_109 i) _)
      ⟨136, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 15 hp) Q2.T136_109_2 Q2.hfix136_109_2 Q2.hinj136_109_2
      Q2.hcardT136_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_109_2 i) (Q2.hfix136_109_2 i) _)
      colCert_136_109_15.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_109_20 (hp : 20 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 20 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 20 (transLenTr ⟨109, by decide⟩ 20 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 20 (transLenTr ⟨109, by decide⟩ 20 hp)) T136_109
      hfix136_109 hinj136_109 hcardT136_109
      (fun i => conj_mem_of_fixedPoints _ _ (T136_109 i) (hfix136_109 i) _)
      ⟨136, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 20 hp) Q2.T136_109_2 Q2.hfix136_109_2 Q2.hinj136_109_2
      Q2.hcardT136_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_109_2 i) (Q2.hfix136_109_2 i) _)
      colCert_136_109_20.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_110_0 (hp : 0 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 0 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 0 (transLenTr ⟨110, by decide⟩ 0 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 0 (transLenTr ⟨110, by decide⟩ 0 hp)) T136_110
      hfix136_110 hinj136_110 hcardT136_110
      (fun i => conj_mem_of_fixedPoints _ _ (T136_110 i) (hfix136_110 i) _)
      ⟨136, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 0 hp) Q2.T136_110_2 Q2.hfix136_110_2 Q2.hinj136_110_2
      Q2.hcardT136_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_110_2 i) (Q2.hfix136_110_2 i) _)
      colCert_136_110_0.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_110_1 (hp : 1 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 1 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 1 (transLenTr ⟨110, by decide⟩ 1 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 1 (transLenTr ⟨110, by decide⟩ 1 hp)) T136_110
      hfix136_110 hinj136_110 hcardT136_110
      (fun i => conj_mem_of_fixedPoints _ _ (T136_110 i) (hfix136_110 i) _)
      ⟨136, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 1 hp) Q2.T136_110_2 Q2.hfix136_110_2 Q2.hinj136_110_2
      Q2.hcardT136_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_110_2 i) (Q2.hfix136_110_2 i) _)
      colCert_136_110_1.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_110_2 (hp : 2 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 2 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 2 (transLenTr ⟨110, by decide⟩ 2 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 2 (transLenTr ⟨110, by decide⟩ 2 hp)) T136_110
      hfix136_110 hinj136_110 hcardT136_110
      (fun i => conj_mem_of_fixedPoints _ _ (T136_110 i) (hfix136_110 i) _)
      ⟨136, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 2 hp) Q2.T136_110_2 Q2.hfix136_110_2 Q2.hinj136_110_2
      Q2.hcardT136_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_110_2 i) (Q2.hfix136_110_2 i) _)
      colCert_136_110_2.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_110_3 (hp : 3 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 3 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 3 (transLenTr ⟨110, by decide⟩ 3 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 3 (transLenTr ⟨110, by decide⟩ 3 hp)) T136_110
      hfix136_110 hinj136_110 hcardT136_110
      (fun i => conj_mem_of_fixedPoints _ _ (T136_110 i) (hfix136_110 i) _)
      ⟨136, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 3 hp) Q2.T136_110_2 Q2.hfix136_110_2 Q2.hinj136_110_2
      Q2.hcardT136_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_110_2 i) (Q2.hfix136_110_2 i) _)
      colCert_136_110_3.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_110_4 (hp : 4 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 4 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 4 (transLenTr ⟨110, by decide⟩ 4 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 4 (transLenTr ⟨110, by decide⟩ 4 hp)) T136_110
      hfix136_110 hinj136_110 hcardT136_110
      (fun i => conj_mem_of_fixedPoints _ _ (T136_110 i) (hfix136_110 i) _)
      ⟨136, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 4 hp) Q2.T136_110_2 Q2.hfix136_110_2 Q2.hinj136_110_2
      Q2.hcardT136_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_110_2 i) (Q2.hfix136_110_2 i) _)
      colCert_136_110_4.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_110_5 (hp : 5 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 5 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 5 (transLenTr ⟨110, by decide⟩ 5 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 5 (transLenTr ⟨110, by decide⟩ 5 hp)) T136_110
      hfix136_110 hinj136_110 hcardT136_110
      (fun i => conj_mem_of_fixedPoints _ _ (T136_110 i) (hfix136_110 i) _)
      ⟨136, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 5 hp) Q2.T136_110_2 Q2.hfix136_110_2 Q2.hinj136_110_2
      Q2.hcardT136_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_110_2 i) (Q2.hfix136_110_2 i) _)
      colCert_136_110_5.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_110_10 (hp : 10 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 10 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 10 (transLenTr ⟨110, by decide⟩ 10 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 10 (transLenTr ⟨110, by decide⟩ 10 hp)) T136_110
      hfix136_110 hinj136_110 hcardT136_110
      (fun i => conj_mem_of_fixedPoints _ _ (T136_110 i) (hfix136_110 i) _)
      ⟨136, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 10 hp) Q2.T136_110_2 Q2.hfix136_110_2 Q2.hinj136_110_2
      Q2.hcardT136_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_110_2 i) (Q2.hfix136_110_2 i) _)
      colCert_136_110_10.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_110_15 (hp : 15 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 15 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 15 (transLenTr ⟨110, by decide⟩ 15 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 15 (transLenTr ⟨110, by decide⟩ 15 hp)) T136_110
      hfix136_110 hinj136_110 hcardT136_110
      (fun i => conj_mem_of_fixedPoints _ _ (T136_110 i) (hfix136_110 i) _)
      ⟨136, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 15 hp) Q2.T136_110_2 Q2.hfix136_110_2 Q2.hinj136_110_2
      Q2.hcardT136_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_110_2 i) (Q2.hfix136_110_2 i) _)
      colCert_136_110_15.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_110_20 (hp : 20 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 20 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 20 (transLenTr ⟨110, by decide⟩ 20 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 20 (transLenTr ⟨110, by decide⟩ 20 hp)) T136_110
      hfix136_110 hinj136_110 hcardT136_110
      (fun i => conj_mem_of_fixedPoints _ _ (T136_110 i) (hfix136_110 i) _)
      ⟨136, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 20 hp) Q2.T136_110_2 Q2.hfix136_110_2 Q2.hinj136_110_2
      Q2.hcardT136_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_110_2 i) (Q2.hfix136_110_2 i) _)
      colCert_136_110_20.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_110_25 (hp : 25 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 25 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 25 (transLenTr ⟨110, by decide⟩ 25 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 25 (transLenTr ⟨110, by decide⟩ 25 hp)) T136_110
      hfix136_110 hinj136_110 hcardT136_110
      (fun i => conj_mem_of_fixedPoints _ _ (T136_110 i) (hfix136_110 i) _)
      ⟨136, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 25 hp) Q2.T136_110_2 Q2.hfix136_110_2 Q2.hinj136_110_2
      Q2.hcardT136_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_110_2 i) (Q2.hfix136_110_2 i) _)
      colCert_136_110_25.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_110_50 (hp : 50 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 50 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 50 (transLenTr ⟨110, by decide⟩ 50 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 50 (transLenTr ⟨110, by decide⟩ 50 hp)) T136_110
      hfix136_110 hinj136_110 hcardT136_110
      (fun i => conj_mem_of_fixedPoints _ _ (T136_110 i) (hfix136_110 i) _)
      ⟨136, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 50 hp) Q2.T136_110_2 Q2.hfix136_110_2 Q2.hinj136_110_2
      Q2.hcardT136_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_110_2 i) (Q2.hfix136_110_2 i) _)
      colCert_136_110_50.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_110_75 (hp : 75 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 75 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 75 (transLenTr ⟨110, by decide⟩ 75 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 75 (transLenTr ⟨110, by decide⟩ 75 hp)) T136_110
      hfix136_110 hinj136_110 hcardT136_110
      (fun i => conj_mem_of_fixedPoints _ _ (T136_110 i) (hfix136_110 i) _)
      ⟨136, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 75 hp) Q2.T136_110_2 Q2.hfix136_110_2 Q2.hinj136_110_2
      Q2.hcardT136_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_110_2 i) (Q2.hfix136_110_2 i) _)
      colCert_136_110_75.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_110_100 (hp : 100 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 100 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 100 (transLenTr ⟨110, by decide⟩ 100 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 100 (transLenTr ⟨110, by decide⟩ 100 hp)) T136_110
      hfix136_110 hinj136_110 hcardT136_110
      (fun i => conj_mem_of_fixedPoints _ _ (T136_110 i) (hfix136_110 i) _)
      ⟨136, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 100 hp) Q2.T136_110_2 Q2.hfix136_110_2 Q2.hinj136_110_2
      Q2.hcardT136_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_110_2 i) (Q2.hfix136_110_2 i) _)
      colCert_136_110_100.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_136_0 (hp : 0 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 0 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 0 (transLenTr ⟨136, by decide⟩ 0 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 0 (transLenTr ⟨136, by decide⟩ 0 hp)) T136_136
      hfix136_136 hinj136_136 hcardT136_136
      (fun i => conj_mem_of_fixedPoints _ _ (T136_136 i) (hfix136_136 i) _)
      ⟨136, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 0 hp) Q2.T136_136_2 Q2.hfix136_136_2 Q2.hinj136_136_2
      Q2.hcardT136_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_136_2 i) (Q2.hfix136_136_2 i) _)
      colCert_136_136_0.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_136_1 (hp : 1 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 1 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 1 (transLenTr ⟨136, by decide⟩ 1 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 1 (transLenTr ⟨136, by decide⟩ 1 hp)) T136_136
      hfix136_136 hinj136_136 hcardT136_136
      (fun i => conj_mem_of_fixedPoints _ _ (T136_136 i) (hfix136_136 i) _)
      ⟨136, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 1 hp) Q2.T136_136_2 Q2.hfix136_136_2 Q2.hinj136_136_2
      Q2.hcardT136_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_136_2 i) (Q2.hfix136_136_2 i) _)
      colCert_136_136_1.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_136_2 (hp : 2 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 2 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 2 (transLenTr ⟨136, by decide⟩ 2 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 2 (transLenTr ⟨136, by decide⟩ 2 hp)) T136_136
      hfix136_136 hinj136_136 hcardT136_136
      (fun i => conj_mem_of_fixedPoints _ _ (T136_136 i) (hfix136_136 i) _)
      ⟨136, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 2 hp) Q2.T136_136_2 Q2.hfix136_136_2 Q2.hinj136_136_2
      Q2.hcardT136_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_136_2 i) (Q2.hfix136_136_2 i) _)
      colCert_136_136_2.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_136_3 (hp : 3 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 3 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 3 (transLenTr ⟨136, by decide⟩ 3 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 3 (transLenTr ⟨136, by decide⟩ 3 hp)) T136_136
      hfix136_136 hinj136_136 hcardT136_136
      (fun i => conj_mem_of_fixedPoints _ _ (T136_136 i) (hfix136_136 i) _)
      ⟨136, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 3 hp) Q2.T136_136_2 Q2.hfix136_136_2 Q2.hinj136_136_2
      Q2.hcardT136_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_136_2 i) (Q2.hfix136_136_2 i) _)
      colCert_136_136_3.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_136_4 (hp : 4 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 4 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 4 (transLenTr ⟨136, by decide⟩ 4 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 4 (transLenTr ⟨136, by decide⟩ 4 hp)) T136_136
      hfix136_136 hinj136_136 hcardT136_136
      (fun i => conj_mem_of_fixedPoints _ _ (T136_136 i) (hfix136_136 i) _)
      ⟨136, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 4 hp) Q2.T136_136_2 Q2.hfix136_136_2 Q2.hinj136_136_2
      Q2.hcardT136_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_136_2 i) (Q2.hfix136_136_2 i) _)
      colCert_136_136_4.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_136_5 (hp : 5 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 5 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 5 (transLenTr ⟨136, by decide⟩ 5 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 5 (transLenTr ⟨136, by decide⟩ 5 hp)) T136_136
      hfix136_136 hinj136_136 hcardT136_136
      (fun i => conj_mem_of_fixedPoints _ _ (T136_136 i) (hfix136_136 i) _)
      ⟨136, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 5 hp) Q2.T136_136_2 Q2.hfix136_136_2 Q2.hinj136_136_2
      Q2.hcardT136_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_136_2 i) (Q2.hfix136_136_2 i) _)
      colCert_136_136_5.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_136_6 (hp : 6 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 6 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 6 (transLenTr ⟨136, by decide⟩ 6 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 6 (transLenTr ⟨136, by decide⟩ 6 hp)) T136_136
      hfix136_136 hinj136_136 hcardT136_136
      (fun i => conj_mem_of_fixedPoints _ _ (T136_136 i) (hfix136_136 i) _)
      ⟨136, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 6 hp) Q2.T136_136_2 Q2.hfix136_136_2 Q2.hinj136_136_2
      Q2.hcardT136_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_136_2 i) (Q2.hfix136_136_2 i) _)
      colCert_136_136_6.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_136_7 (hp : 7 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 7 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 7 (transLenTr ⟨136, by decide⟩ 7 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 7 (transLenTr ⟨136, by decide⟩ 7 hp)) T136_136
      hfix136_136 hinj136_136 hcardT136_136
      (fun i => conj_mem_of_fixedPoints _ _ (T136_136 i) (hfix136_136 i) _)
      ⟨136, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 7 hp) Q2.T136_136_2 Q2.hfix136_136_2 Q2.hinj136_136_2
      Q2.hcardT136_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_136_2 i) (Q2.hfix136_136_2 i) _)
      colCert_136_136_7.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_136_8 (hp : 8 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 8 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 8 (transLenTr ⟨136, by decide⟩ 8 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 8 (transLenTr ⟨136, by decide⟩ 8 hp)) T136_136
      hfix136_136 hinj136_136 hcardT136_136
      (fun i => conj_mem_of_fixedPoints _ _ (T136_136 i) (hfix136_136 i) _)
      ⟨136, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 8 hp) Q2.T136_136_2 Q2.hfix136_136_2 Q2.hinj136_136_2
      Q2.hcardT136_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_136_2 i) (Q2.hfix136_136_2 i) _)
      colCert_136_136_8.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_136_9 (hp : 9 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 9 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 9 (transLenTr ⟨136, by decide⟩ 9 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 9 (transLenTr ⟨136, by decide⟩ 9 hp)) T136_136
      hfix136_136 hinj136_136 hcardT136_136
      (fun i => conj_mem_of_fixedPoints _ _ (T136_136 i) (hfix136_136 i) _)
      ⟨136, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 9 hp) Q2.T136_136_2 Q2.hfix136_136_2 Q2.hinj136_136_2
      Q2.hcardT136_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_136_2 i) (Q2.hfix136_136_2 i) _)
      colCert_136_136_9.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_136_10 (hp : 10 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 10 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 10 (transLenTr ⟨136, by decide⟩ 10 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 10 (transLenTr ⟨136, by decide⟩ 10 hp)) T136_136
      hfix136_136 hinj136_136 hcardT136_136
      (fun i => conj_mem_of_fixedPoints _ _ (T136_136 i) (hfix136_136 i) _)
      ⟨136, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 10 hp) Q2.T136_136_2 Q2.hfix136_136_2 Q2.hinj136_136_2
      Q2.hcardT136_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_136_2 i) (Q2.hfix136_136_2 i) _)
      colCert_136_136_10.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_136_11 (hp : 11 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 11 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 11 (transLenTr ⟨136, by decide⟩ 11 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 11 (transLenTr ⟨136, by decide⟩ 11 hp)) T136_136
      hfix136_136 hinj136_136 hcardT136_136
      (fun i => conj_mem_of_fixedPoints _ _ (T136_136 i) (hfix136_136 i) _)
      ⟨136, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 11 hp) Q2.T136_136_2 Q2.hfix136_136_2 Q2.hinj136_136_2
      Q2.hcardT136_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_136_2 i) (Q2.hfix136_136_2 i) _)
      colCert_136_136_11.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_136_12 (hp : 12 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 12 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 12 (transLenTr ⟨136, by decide⟩ 12 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 12 (transLenTr ⟨136, by decide⟩ 12 hp)) T136_136
      hfix136_136 hinj136_136 hcardT136_136
      (fun i => conj_mem_of_fixedPoints _ _ (T136_136 i) (hfix136_136 i) _)
      ⟨136, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 12 hp) Q2.T136_136_2 Q2.hfix136_136_2 Q2.hinj136_136_2
      Q2.hcardT136_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_136_2 i) (Q2.hfix136_136_2 i) _)
      colCert_136_136_12.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_136_13 (hp : 13 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 13 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 13 (transLenTr ⟨136, by decide⟩ 13 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 13 (transLenTr ⟨136, by decide⟩ 13 hp)) T136_136
      hfix136_136 hinj136_136 hcardT136_136
      (fun i => conj_mem_of_fixedPoints _ _ (T136_136 i) (hfix136_136 i) _)
      ⟨136, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 13 hp) Q2.T136_136_2 Q2.hfix136_136_2 Q2.hinj136_136_2
      Q2.hcardT136_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_136_2 i) (Q2.hfix136_136_2 i) _)
      colCert_136_136_13.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_136_14 (hp : 14 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 14 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 14 (transLenTr ⟨136, by decide⟩ 14 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 14 (transLenTr ⟨136, by decide⟩ 14 hp)) T136_136
      hfix136_136 hinj136_136 hcardT136_136
      (fun i => conj_mem_of_fixedPoints _ _ (T136_136 i) (hfix136_136 i) _)
      ⟨136, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 14 hp) Q2.T136_136_2 Q2.hfix136_136_2 Q2.hinj136_136_2
      Q2.hcardT136_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_136_2 i) (Q2.hfix136_136_2 i) _)
      colCert_136_136_14.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_136_15 (hp : 15 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 15 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 15 (transLenTr ⟨136, by decide⟩ 15 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 15 (transLenTr ⟨136, by decide⟩ 15 hp)) T136_136
      hfix136_136 hinj136_136 hcardT136_136
      (fun i => conj_mem_of_fixedPoints _ _ (T136_136 i) (hfix136_136 i) _)
      ⟨136, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 15 hp) Q2.T136_136_2 Q2.hfix136_136_2 Q2.hinj136_136_2
      Q2.hcardT136_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_136_2 i) (Q2.hfix136_136_2 i) _)
      colCert_136_136_15.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_136_16 (hp : 16 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 16 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 16 (transLenTr ⟨136, by decide⟩ 16 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 16 (transLenTr ⟨136, by decide⟩ 16 hp)) T136_136
      hfix136_136 hinj136_136 hcardT136_136
      (fun i => conj_mem_of_fixedPoints _ _ (T136_136 i) (hfix136_136 i) _)
      ⟨136, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 16 hp) Q2.T136_136_2 Q2.hfix136_136_2 Q2.hinj136_136_2
      Q2.hcardT136_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_136_2 i) (Q2.hfix136_136_2 i) _)
      colCert_136_136_16.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_136_17 (hp : 17 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 17 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 17 (transLenTr ⟨136, by decide⟩ 17 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 17 (transLenTr ⟨136, by decide⟩ 17 hp)) T136_136
      hfix136_136 hinj136_136 hcardT136_136
      (fun i => conj_mem_of_fixedPoints _ _ (T136_136 i) (hfix136_136 i) _)
      ⟨136, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 17 hp) Q2.T136_136_2 Q2.hfix136_136_2 Q2.hinj136_136_2
      Q2.hcardT136_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_136_2 i) (Q2.hfix136_136_2 i) _)
      colCert_136_136_17.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_136_18 (hp : 18 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 18 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 18 (transLenTr ⟨136, by decide⟩ 18 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 18 (transLenTr ⟨136, by decide⟩ 18 hp)) T136_136
      hfix136_136 hinj136_136 hcardT136_136
      (fun i => conj_mem_of_fixedPoints _ _ (T136_136 i) (hfix136_136 i) _)
      ⟨136, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 18 hp) Q2.T136_136_2 Q2.hfix136_136_2 Q2.hinj136_136_2
      Q2.hcardT136_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_136_2 i) (Q2.hfix136_136_2 i) _)
      colCert_136_136_18.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_136_19 (hp : 19 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 19 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 19 (transLenTr ⟨136, by decide⟩ 19 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 19 (transLenTr ⟨136, by decide⟩ 19 hp)) T136_136
      hfix136_136 hinj136_136 hcardT136_136
      (fun i => conj_mem_of_fixedPoints _ _ (T136_136 i) (hfix136_136 i) _)
      ⟨136, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 19 hp) Q2.T136_136_2 Q2.hfix136_136_2 Q2.hinj136_136_2
      Q2.hcardT136_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_136_2 i) (Q2.hfix136_136_2 i) _)
      colCert_136_136_19.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_136_20 (hp : 20 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 20 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 20 (transLenTr ⟨136, by decide⟩ 20 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 20 (transLenTr ⟨136, by decide⟩ 20 hp)) T136_136
      hfix136_136 hinj136_136 hcardT136_136
      (fun i => conj_mem_of_fixedPoints _ _ (T136_136 i) (hfix136_136 i) _)
      ⟨136, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 20 hp) Q2.T136_136_2 Q2.hfix136_136_2 Q2.hinj136_136_2
      Q2.hcardT136_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_136_2 i) (Q2.hfix136_136_2 i) _)
      colCert_136_136_20.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_136_21 (hp : 21 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 21 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 21 (transLenTr ⟨136, by decide⟩ 21 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 21 (transLenTr ⟨136, by decide⟩ 21 hp)) T136_136
      hfix136_136 hinj136_136 hcardT136_136
      (fun i => conj_mem_of_fixedPoints _ _ (T136_136 i) (hfix136_136 i) _)
      ⟨136, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 21 hp) Q2.T136_136_2 Q2.hfix136_136_2 Q2.hinj136_136_2
      Q2.hcardT136_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_136_2 i) (Q2.hfix136_136_2 i) _)
      colCert_136_136_21.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_136_22 (hp : 22 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 22 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 22 (transLenTr ⟨136, by decide⟩ 22 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 22 (transLenTr ⟨136, by decide⟩ 22 hp)) T136_136
      hfix136_136 hinj136_136 hcardT136_136
      (fun i => conj_mem_of_fixedPoints _ _ (T136_136 i) (hfix136_136 i) _)
      ⟨136, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 22 hp) Q2.T136_136_2 Q2.hfix136_136_2 Q2.hinj136_136_2
      Q2.hcardT136_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_136_2 i) (Q2.hfix136_136_2 i) _)
      colCert_136_136_22.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_136_23 (hp : 23 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 23 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 23 (transLenTr ⟨136, by decide⟩ 23 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 23 (transLenTr ⟨136, by decide⟩ 23 hp)) T136_136
      hfix136_136 hinj136_136 hcardT136_136
      (fun i => conj_mem_of_fixedPoints _ _ (T136_136 i) (hfix136_136 i) _)
      ⟨136, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 23 hp) Q2.T136_136_2 Q2.hfix136_136_2 Q2.hinj136_136_2
      Q2.hcardT136_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_136_2 i) (Q2.hfix136_136_2 i) _)
      colCert_136_136_23.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_136_136_24 (hp : 24 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 136 []).length)
    (hq : (normIsRep.getD 136 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 24 hp)
        (rowE2 (⟨136, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 24 (transLenTr ⟨136, by decide⟩ 24 hp))
        (rowE1 (⟨136, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨136, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨136, by decide⟩ (listedAt ⟨136, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 24 (transLenTr ⟨136, by decide⟩ 24 hp)) T136_136
      hfix136_136 hinj136_136 hcardT136_136
      (fun i => conj_mem_of_fixedPoints _ _ (T136_136 i) (hfix136_136 i) _)
      ⟨136, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨136, by decide⟩ (Q2.listedAt ⟨136, by decide⟩
        (alnCheck_rep ⟨136, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 24 hp) Q2.T136_136_2 Q2.hfix136_136_2 Q2.hinj136_136_2
      Q2.hcardT136_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T136_136_2 i) (Q2.hfix136_136_2 i) _)
      colCert_136_136_24.hD ?_).symm
  rw [alnId_136 j hj]


theorem leaf_137_5_0 (hp : 0 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 0 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp)) T137_5
      hfix137_5 hinj137_5 hcardT137_5
      (fun i => conj_mem_of_fixedPoints _ _ (T137_5 i) (hfix137_5 i) _)
      ⟨137, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 0 hp) Q2.T137_5_2 Q2.hfix137_5_2 Q2.hinj137_5_2
      Q2.hcardT137_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_5_2 i) (Q2.hfix137_5_2 i) _)
      colCert_137_5_0.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_5_1 (hp : 1 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 1 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp)) T137_5
      hfix137_5 hinj137_5 hcardT137_5
      (fun i => conj_mem_of_fixedPoints _ _ (T137_5 i) (hfix137_5 i) _)
      ⟨137, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 1 hp) Q2.T137_5_2 Q2.hfix137_5_2 Q2.hinj137_5_2
      Q2.hcardT137_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_5_2 i) (Q2.hfix137_5_2 i) _)
      colCert_137_5_1.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_5_2 (hp : 2 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 2 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp)) T137_5
      hfix137_5 hinj137_5 hcardT137_5
      (fun i => conj_mem_of_fixedPoints _ _ (T137_5 i) (hfix137_5 i) _)
      ⟨137, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 2 hp) Q2.T137_5_2 Q2.hfix137_5_2 Q2.hinj137_5_2
      Q2.hcardT137_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_5_2 i) (Q2.hfix137_5_2 i) _)
      colCert_137_5_2.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_5_3 (hp : 3 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 3 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp)) T137_5
      hfix137_5 hinj137_5 hcardT137_5
      (fun i => conj_mem_of_fixedPoints _ _ (T137_5 i) (hfix137_5 i) _)
      ⟨137, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 3 hp) Q2.T137_5_2 Q2.hfix137_5_2 Q2.hinj137_5_2
      Q2.hcardT137_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_5_2 i) (Q2.hfix137_5_2 i) _)
      colCert_137_5_3.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_5_4 (hp : 4 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 4 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp)) T137_5
      hfix137_5 hinj137_5 hcardT137_5
      (fun i => conj_mem_of_fixedPoints _ _ (T137_5 i) (hfix137_5 i) _)
      ⟨137, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 4 hp) Q2.T137_5_2 Q2.hfix137_5_2 Q2.hinj137_5_2
      Q2.hcardT137_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_5_2 i) (Q2.hfix137_5_2 i) _)
      colCert_137_5_4.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T137_10
      hfix137_10 hinj137_10 hcardT137_10
      (fun i => conj_mem_of_fixedPoints _ _ (T137_10 i) (hfix137_10 i) _)
      ⟨137, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T137_10_2 Q2.hfix137_10_2 Q2.hinj137_10_2
      Q2.hcardT137_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_10_2 i) (Q2.hfix137_10_2 i) _)
      colCert_137_10_0.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T137_10
      hfix137_10 hinj137_10 hcardT137_10
      (fun i => conj_mem_of_fixedPoints _ _ (T137_10 i) (hfix137_10 i) _)
      ⟨137, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T137_10_2 Q2.hfix137_10_2 Q2.hinj137_10_2
      Q2.hcardT137_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_10_2 i) (Q2.hfix137_10_2 i) _)
      colCert_137_10_1.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T137_10
      hfix137_10 hinj137_10 hcardT137_10
      (fun i => conj_mem_of_fixedPoints _ _ (T137_10 i) (hfix137_10 i) _)
      ⟨137, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T137_10_2 Q2.hfix137_10_2 Q2.hinj137_10_2
      Q2.hcardT137_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_10_2 i) (Q2.hfix137_10_2 i) _)
      colCert_137_10_2.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T137_10
      hfix137_10 hinj137_10 hcardT137_10
      (fun i => conj_mem_of_fixedPoints _ _ (T137_10 i) (hfix137_10 i) _)
      ⟨137, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T137_10_2 Q2.hfix137_10_2 Q2.hinj137_10_2
      Q2.hcardT137_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_10_2 i) (Q2.hfix137_10_2 i) _)
      colCert_137_10_3.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T137_10
      hfix137_10 hinj137_10 hcardT137_10
      (fun i => conj_mem_of_fixedPoints _ _ (T137_10 i) (hfix137_10 i) _)
      ⟨137, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T137_10_2 Q2.hfix137_10_2 Q2.hinj137_10_2
      Q2.hcardT137_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_10_2 i) (Q2.hfix137_10_2 i) _)
      colCert_137_10_4.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T137_12
      hfix137_12 hinj137_12 hcardT137_12
      (fun i => conj_mem_of_fixedPoints _ _ (T137_12 i) (hfix137_12 i) _)
      ⟨137, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T137_12_2 Q2.hfix137_12_2 Q2.hinj137_12_2
      Q2.hcardT137_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_12_2 i) (Q2.hfix137_12_2 i) _)
      colCert_137_12_0.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T137_12
      hfix137_12 hinj137_12 hcardT137_12
      (fun i => conj_mem_of_fixedPoints _ _ (T137_12 i) (hfix137_12 i) _)
      ⟨137, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T137_12_2 Q2.hfix137_12_2 Q2.hinj137_12_2
      Q2.hcardT137_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_12_2 i) (Q2.hfix137_12_2 i) _)
      colCert_137_12_1.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T137_12
      hfix137_12 hinj137_12 hcardT137_12
      (fun i => conj_mem_of_fixedPoints _ _ (T137_12 i) (hfix137_12 i) _)
      ⟨137, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T137_12_2 Q2.hfix137_12_2 Q2.hinj137_12_2
      Q2.hcardT137_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_12_2 i) (Q2.hfix137_12_2 i) _)
      colCert_137_12_2.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T137_12
      hfix137_12 hinj137_12 hcardT137_12
      (fun i => conj_mem_of_fixedPoints _ _ (T137_12 i) (hfix137_12 i) _)
      ⟨137, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T137_12_2 Q2.hfix137_12_2 Q2.hinj137_12_2
      Q2.hcardT137_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_12_2 i) (Q2.hfix137_12_2 i) _)
      colCert_137_12_3.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T137_12
      hfix137_12 hinj137_12 hcardT137_12
      (fun i => conj_mem_of_fixedPoints _ _ (T137_12 i) (hfix137_12 i) _)
      ⟨137, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T137_12_2 Q2.hfix137_12_2 Q2.hinj137_12_2
      Q2.hcardT137_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_12_2 i) (Q2.hfix137_12_2 i) _)
      colCert_137_12_4.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_23_0 (hp : 0 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 0 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 0 (transLenTr ⟨23, by decide⟩ 0 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 0 (transLenTr ⟨23, by decide⟩ 0 hp)) T137_23
      hfix137_23 hinj137_23 hcardT137_23
      (fun i => conj_mem_of_fixedPoints _ _ (T137_23 i) (hfix137_23 i) _)
      ⟨137, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 0 hp) Q2.T137_23_2 Q2.hfix137_23_2 Q2.hinj137_23_2
      Q2.hcardT137_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_23_2 i) (Q2.hfix137_23_2 i) _)
      colCert_137_23_0.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_23_1 (hp : 1 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 1 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 1 (transLenTr ⟨23, by decide⟩ 1 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 1 (transLenTr ⟨23, by decide⟩ 1 hp)) T137_23
      hfix137_23 hinj137_23 hcardT137_23
      (fun i => conj_mem_of_fixedPoints _ _ (T137_23 i) (hfix137_23 i) _)
      ⟨137, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 1 hp) Q2.T137_23_2 Q2.hfix137_23_2 Q2.hinj137_23_2
      Q2.hcardT137_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_23_2 i) (Q2.hfix137_23_2 i) _)
      colCert_137_23_1.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_23_2 (hp : 2 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 2 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 2 (transLenTr ⟨23, by decide⟩ 2 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 2 (transLenTr ⟨23, by decide⟩ 2 hp)) T137_23
      hfix137_23 hinj137_23 hcardT137_23
      (fun i => conj_mem_of_fixedPoints _ _ (T137_23 i) (hfix137_23 i) _)
      ⟨137, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 2 hp) Q2.T137_23_2 Q2.hfix137_23_2 Q2.hinj137_23_2
      Q2.hcardT137_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_23_2 i) (Q2.hfix137_23_2 i) _)
      colCert_137_23_2.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_23_3 (hp : 3 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 3 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 3 (transLenTr ⟨23, by decide⟩ 3 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 3 (transLenTr ⟨23, by decide⟩ 3 hp)) T137_23
      hfix137_23 hinj137_23 hcardT137_23
      (fun i => conj_mem_of_fixedPoints _ _ (T137_23 i) (hfix137_23 i) _)
      ⟨137, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 3 hp) Q2.T137_23_2 Q2.hfix137_23_2 Q2.hinj137_23_2
      Q2.hcardT137_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_23_2 i) (Q2.hfix137_23_2 i) _)
      colCert_137_23_3.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_23_4 (hp : 4 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 4 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 4 (transLenTr ⟨23, by decide⟩ 4 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 4 (transLenTr ⟨23, by decide⟩ 4 hp)) T137_23
      hfix137_23 hinj137_23 hcardT137_23
      (fun i => conj_mem_of_fixedPoints _ _ (T137_23 i) (hfix137_23 i) _)
      ⟨137, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 4 hp) Q2.T137_23_2 Q2.hfix137_23_2 Q2.hinj137_23_2
      Q2.hcardT137_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_23_2 i) (Q2.hfix137_23_2 i) _)
      colCert_137_23_4.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_23_5 (hp : 5 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 5 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp)) T137_23
      hfix137_23 hinj137_23 hcardT137_23
      (fun i => conj_mem_of_fixedPoints _ _ (T137_23 i) (hfix137_23 i) _)
      ⟨137, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 5 hp) Q2.T137_23_2 Q2.hfix137_23_2 Q2.hinj137_23_2
      Q2.hcardT137_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_23_2 i) (Q2.hfix137_23_2 i) _)
      colCert_137_23_5.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_23_10 (hp : 10 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 10 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp)) T137_23
      hfix137_23 hinj137_23 hcardT137_23
      (fun i => conj_mem_of_fixedPoints _ _ (T137_23 i) (hfix137_23 i) _)
      ⟨137, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 10 hp) Q2.T137_23_2 Q2.hfix137_23_2 Q2.hinj137_23_2
      Q2.hcardT137_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_23_2 i) (Q2.hfix137_23_2 i) _)
      colCert_137_23_10.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_23_15 (hp : 15 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 15 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp)) T137_23
      hfix137_23 hinj137_23 hcardT137_23
      (fun i => conj_mem_of_fixedPoints _ _ (T137_23 i) (hfix137_23 i) _)
      ⟨137, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 15 hp) Q2.T137_23_2 Q2.hfix137_23_2 Q2.hinj137_23_2
      Q2.hcardT137_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_23_2 i) (Q2.hfix137_23_2 i) _)
      colCert_137_23_15.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_23_20 (hp : 20 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 20 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp)) T137_23
      hfix137_23 hinj137_23 hcardT137_23
      (fun i => conj_mem_of_fixedPoints _ _ (T137_23 i) (hfix137_23 i) _)
      ⟨137, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 20 hp) Q2.T137_23_2 Q2.hfix137_23_2 Q2.hinj137_23_2
      Q2.hcardT137_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_23_2 i) (Q2.hfix137_23_2 i) _)
      colCert_137_23_20.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_30_0 (hp : 0 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 0 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp)) T137_30
      hfix137_30 hinj137_30 hcardT137_30
      (fun i => conj_mem_of_fixedPoints _ _ (T137_30 i) (hfix137_30 i) _)
      ⟨137, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 0 hp) Q2.T137_30_2 Q2.hfix137_30_2 Q2.hinj137_30_2
      Q2.hcardT137_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_30_2 i) (Q2.hfix137_30_2 i) _)
      colCert_137_30_0.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_30_1 (hp : 1 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 1 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp)) T137_30
      hfix137_30 hinj137_30 hcardT137_30
      (fun i => conj_mem_of_fixedPoints _ _ (T137_30 i) (hfix137_30 i) _)
      ⟨137, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 1 hp) Q2.T137_30_2 Q2.hfix137_30_2 Q2.hinj137_30_2
      Q2.hcardT137_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_30_2 i) (Q2.hfix137_30_2 i) _)
      colCert_137_30_1.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_30_2 (hp : 2 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 2 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp)) T137_30
      hfix137_30 hinj137_30 hcardT137_30
      (fun i => conj_mem_of_fixedPoints _ _ (T137_30 i) (hfix137_30 i) _)
      ⟨137, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 2 hp) Q2.T137_30_2 Q2.hfix137_30_2 Q2.hinj137_30_2
      Q2.hcardT137_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_30_2 i) (Q2.hfix137_30_2 i) _)
      colCert_137_30_2.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_30_3 (hp : 3 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 3 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp)) T137_30
      hfix137_30 hinj137_30 hcardT137_30
      (fun i => conj_mem_of_fixedPoints _ _ (T137_30 i) (hfix137_30 i) _)
      ⟨137, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 3 hp) Q2.T137_30_2 Q2.hfix137_30_2 Q2.hinj137_30_2
      Q2.hcardT137_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_30_2 i) (Q2.hfix137_30_2 i) _)
      colCert_137_30_3.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_30_4 (hp : 4 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 4 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp)) T137_30
      hfix137_30 hinj137_30 hcardT137_30
      (fun i => conj_mem_of_fixedPoints _ _ (T137_30 i) (hfix137_30 i) _)
      ⟨137, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 4 hp) Q2.T137_30_2 Q2.hfix137_30_2 Q2.hinj137_30_2
      Q2.hcardT137_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_30_2 i) (Q2.hfix137_30_2 i) _)
      colCert_137_30_4.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_30_5 (hp : 5 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 5 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨137, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp)) T137_30
      hfix137_30 hinj137_30 hcardT137_30
      (fun i => conj_mem_of_fixedPoints _ _ (T137_30 i) (hfix137_30 i) _)
      ⟨137, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 5 hp) Q2.T137_30_2 Q2.hfix137_30_2 Q2.hinj137_30_2
      Q2.hcardT137_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_30_2 i) (Q2.hfix137_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨137, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T137_30 = colFn colCertDiv_137_30_5.D1 (m := 5) from colCertDiv_137_30_5.bind1,
    show colData2 (⟨137, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 5 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T137_30_2 = colFn colCertDiv_137_30_5.D2 (m := 5) from colCertDiv_137_30_5.bind2]
  rw [alnId_137 j hj]
  exact fastcode_of_div ⟨137, by decide⟩ _ _ _
    ((alnId_137 j hj) ▸ Q2.listedAt (⟨137, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨137, by decide⟩ : Fin 148) hj hq).1) colCertDiv_137_30_5_match


theorem leaf_137_30_10 (hp : 10 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 10 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨137, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp)) T137_30
      hfix137_30 hinj137_30 hcardT137_30
      (fun i => conj_mem_of_fixedPoints _ _ (T137_30 i) (hfix137_30 i) _)
      ⟨137, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 10 hp) Q2.T137_30_2 Q2.hfix137_30_2 Q2.hinj137_30_2
      Q2.hcardT137_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_30_2 i) (Q2.hfix137_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨137, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T137_30 = colFn colCertDiv_137_30_10.D1 (m := 5) from colCertDiv_137_30_10.bind1,
    show colData2 (⟨137, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 10 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T137_30_2 = colFn colCertDiv_137_30_10.D2 (m := 5) from colCertDiv_137_30_10.bind2]
  rw [alnId_137 j hj]
  exact fastcode_of_div ⟨137, by decide⟩ _ _ _
    ((alnId_137 j hj) ▸ Q2.listedAt (⟨137, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨137, by decide⟩ : Fin 148) hj hq).1) colCertDiv_137_30_10_match


theorem leaf_137_30_15 (hp : 15 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 15 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨137, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp)) T137_30
      hfix137_30 hinj137_30 hcardT137_30
      (fun i => conj_mem_of_fixedPoints _ _ (T137_30 i) (hfix137_30 i) _)
      ⟨137, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 15 hp) Q2.T137_30_2 Q2.hfix137_30_2 Q2.hinj137_30_2
      Q2.hcardT137_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_30_2 i) (Q2.hfix137_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨137, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T137_30 = colFn colCertDiv_137_30_15.D1 (m := 5) from colCertDiv_137_30_15.bind1,
    show colData2 (⟨137, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 15 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T137_30_2 = colFn colCertDiv_137_30_15.D2 (m := 5) from colCertDiv_137_30_15.bind2]
  rw [alnId_137 j hj]
  exact fastcode_of_div ⟨137, by decide⟩ _ _ _
    ((alnId_137 j hj) ▸ Q2.listedAt (⟨137, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨137, by decide⟩ : Fin 148) hj hq).1) colCertDiv_137_30_15_match


theorem leaf_137_30_20 (hp : 20 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 20 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨137, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp)) T137_30
      hfix137_30 hinj137_30 hcardT137_30
      (fun i => conj_mem_of_fixedPoints _ _ (T137_30 i) (hfix137_30 i) _)
      ⟨137, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 20 hp) Q2.T137_30_2 Q2.hfix137_30_2 Q2.hinj137_30_2
      Q2.hcardT137_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_30_2 i) (Q2.hfix137_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨137, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T137_30 = colFn colCertDiv_137_30_20.D1 (m := 5) from colCertDiv_137_30_20.bind1,
    show colData2 (⟨137, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 20 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T137_30_2 = colFn colCertDiv_137_30_20.D2 (m := 5) from colCertDiv_137_30_20.bind2]
  rw [alnId_137 j hj]
  exact fastcode_of_div ⟨137, by decide⟩ _ _ _
    ((alnId_137 j hj) ▸ Q2.listedAt (⟨137, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨137, by decide⟩ : Fin 148) hj hq).1) colCertDiv_137_30_20_match


theorem leaf_137_37_0 (hp : 0 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 0 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp)) T137_37
      hfix137_37 hinj137_37 hcardT137_37
      (fun i => conj_mem_of_fixedPoints _ _ (T137_37 i) (hfix137_37 i) _)
      ⟨137, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 0 hp) Q2.T137_37_2 Q2.hfix137_37_2 Q2.hinj137_37_2
      Q2.hcardT137_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_37_2 i) (Q2.hfix137_37_2 i) _)
      colCert_137_37_0.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_37_1 (hp : 1 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 1 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp)) T137_37
      hfix137_37 hinj137_37 hcardT137_37
      (fun i => conj_mem_of_fixedPoints _ _ (T137_37 i) (hfix137_37 i) _)
      ⟨137, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 1 hp) Q2.T137_37_2 Q2.hfix137_37_2 Q2.hinj137_37_2
      Q2.hcardT137_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_37_2 i) (Q2.hfix137_37_2 i) _)
      colCert_137_37_1.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_37_2 (hp : 2 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 2 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp)) T137_37
      hfix137_37 hinj137_37 hcardT137_37
      (fun i => conj_mem_of_fixedPoints _ _ (T137_37 i) (hfix137_37 i) _)
      ⟨137, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 2 hp) Q2.T137_37_2 Q2.hfix137_37_2 Q2.hinj137_37_2
      Q2.hcardT137_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_37_2 i) (Q2.hfix137_37_2 i) _)
      colCert_137_37_2.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_37_3 (hp : 3 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 3 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp)) T137_37
      hfix137_37 hinj137_37 hcardT137_37
      (fun i => conj_mem_of_fixedPoints _ _ (T137_37 i) (hfix137_37 i) _)
      ⟨137, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 3 hp) Q2.T137_37_2 Q2.hfix137_37_2 Q2.hinj137_37_2
      Q2.hcardT137_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_37_2 i) (Q2.hfix137_37_2 i) _)
      colCert_137_37_3.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_37_4 (hp : 4 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 4 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp)) T137_37
      hfix137_37 hinj137_37 hcardT137_37
      (fun i => conj_mem_of_fixedPoints _ _ (T137_37 i) (hfix137_37 i) _)
      ⟨137, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 4 hp) Q2.T137_37_2 Q2.hfix137_37_2 Q2.hinj137_37_2
      Q2.hcardT137_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_37_2 i) (Q2.hfix137_37_2 i) _)
      colCert_137_37_4.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_37_5 (hp : 5 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 5 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨137, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp)) T137_37
      hfix137_37 hinj137_37 hcardT137_37
      (fun i => conj_mem_of_fixedPoints _ _ (T137_37 i) (hfix137_37 i) _)
      ⟨137, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 5 hp) Q2.T137_37_2 Q2.hfix137_37_2 Q2.hinj137_37_2
      Q2.hcardT137_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_37_2 i) (Q2.hfix137_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨137, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T137_37 = colFn colCertDiv_137_37_5.D1 (m := 5) from colCertDiv_137_37_5.bind1,
    show colData2 (⟨137, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 5 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T137_37_2 = colFn colCertDiv_137_37_5.D2 (m := 5) from colCertDiv_137_37_5.bind2]
  rw [alnId_137 j hj]
  exact fastcode_of_div ⟨137, by decide⟩ _ _ _
    ((alnId_137 j hj) ▸ Q2.listedAt (⟨137, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨137, by decide⟩ : Fin 148) hj hq).1) colCertDiv_137_37_5_match


theorem leaf_137_37_10 (hp : 10 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 10 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨137, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp)) T137_37
      hfix137_37 hinj137_37 hcardT137_37
      (fun i => conj_mem_of_fixedPoints _ _ (T137_37 i) (hfix137_37 i) _)
      ⟨137, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 10 hp) Q2.T137_37_2 Q2.hfix137_37_2 Q2.hinj137_37_2
      Q2.hcardT137_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_37_2 i) (Q2.hfix137_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨137, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T137_37 = colFn colCertDiv_137_37_10.D1 (m := 5) from colCertDiv_137_37_10.bind1,
    show colData2 (⟨137, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 10 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T137_37_2 = colFn colCertDiv_137_37_10.D2 (m := 5) from colCertDiv_137_37_10.bind2]
  rw [alnId_137 j hj]
  exact fastcode_of_div ⟨137, by decide⟩ _ _ _
    ((alnId_137 j hj) ▸ Q2.listedAt (⟨137, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨137, by decide⟩ : Fin 148) hj hq).1) colCertDiv_137_37_10_match


theorem leaf_137_37_15 (hp : 15 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 15 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨137, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp)) T137_37
      hfix137_37 hinj137_37 hcardT137_37
      (fun i => conj_mem_of_fixedPoints _ _ (T137_37 i) (hfix137_37 i) _)
      ⟨137, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 15 hp) Q2.T137_37_2 Q2.hfix137_37_2 Q2.hinj137_37_2
      Q2.hcardT137_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_37_2 i) (Q2.hfix137_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨137, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T137_37 = colFn colCertDiv_137_37_15.D1 (m := 5) from colCertDiv_137_37_15.bind1,
    show colData2 (⟨137, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 15 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T137_37_2 = colFn colCertDiv_137_37_15.D2 (m := 5) from colCertDiv_137_37_15.bind2]
  rw [alnId_137 j hj]
  exact fastcode_of_div ⟨137, by decide⟩ _ _ _
    ((alnId_137 j hj) ▸ Q2.listedAt (⟨137, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨137, by decide⟩ : Fin 148) hj hq).1) colCertDiv_137_37_15_match


theorem leaf_137_37_20 (hp : 20 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 20 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨137, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp)) T137_37
      hfix137_37 hinj137_37 hcardT137_37
      (fun i => conj_mem_of_fixedPoints _ _ (T137_37 i) (hfix137_37 i) _)
      ⟨137, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 20 hp) Q2.T137_37_2 Q2.hfix137_37_2 Q2.hinj137_37_2
      Q2.hcardT137_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_37_2 i) (Q2.hfix137_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨137, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T137_37 = colFn colCertDiv_137_37_20.D1 (m := 5) from colCertDiv_137_37_20.bind1,
    show colData2 (⟨137, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 20 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T137_37_2 = colFn colCertDiv_137_37_20.D2 (m := 5) from colCertDiv_137_37_20.bind2]
  rw [alnId_137 j hj]
  exact fastcode_of_div ⟨137, by decide⟩ _ _ _
    ((alnId_137 j hj) ▸ Q2.listedAt (⟨137, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨137, by decide⟩ : Fin 148) hj hq).1) colCertDiv_137_37_20_match


end LeanDring.P5Presentation
