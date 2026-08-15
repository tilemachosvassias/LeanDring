/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C040
import LeanDring.P5.Data.ColRestCheap.C166
import LeanDring.P5.Data.ColRestCheap.C167
import LeanDring.P5.Data.ColRestCheap.C168
import LeanDring.P5.Data.ColRestCheap.C169
import LeanDring.P5.Data.ColRestCheap.C170
import LeanDring.P5.Data.ColRestCheap.C171
import LeanDring.P5.Data.EntryK.C017
import LeanDring.P5.Data.EntryK.C018
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesAlign.C020
import LeanDring.P5.Data.SpeciesAlign.C021
import LeanDring.P5.Data.SpeciesAlign.C022
import LeanDring.P5.Data.SpeciesDiv.C049

/-! # Stage-5 leaves, chunk 11 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_74_46_4 (hp : 4 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 4 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp)) T74_46
      hfix74_46 hinj74_46 hcardT74_46
      (fun i => conj_mem_of_fixedPoints _ _ (T74_46 i) (hfix74_46 i) _)
      ⟨74, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 4 hp) Q2.T74_46_2 Q2.hfix74_46_2 Q2.hinj74_46_2
      Q2.hcardT74_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_46_2 i) (Q2.hfix74_46_2 i) _)
      colCert_74_46_4.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_46_5 (hp : 5 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 5 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨74, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp)) T74_46
      hfix74_46 hinj74_46 hcardT74_46
      (fun i => conj_mem_of_fixedPoints _ _ (T74_46 i) (hfix74_46 i) _)
      ⟨74, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 5 hp) Q2.T74_46_2 Q2.hfix74_46_2 Q2.hinj74_46_2
      Q2.hcardT74_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_46_2 i) (Q2.hfix74_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨74, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T74_46 = colFn colCertDiv_74_46_5.D1 (m := 5) from colCertDiv_74_46_5.bind1,
    show colData2 (⟨74, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 5 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T74_46_2 = colFn colCertDiv_74_46_5.D2 (m := 5) from colCertDiv_74_46_5.bind2]
  rw [alnId_74 j hj]
  exact fastcode_of_div ⟨74, by decide⟩ _ _ _
    ((alnId_74 j hj) ▸ Q2.listedAt (⟨74, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨74, by decide⟩ : Fin 148) hj hq).1) colCertDiv_74_46_5_match


theorem leaf_74_46_10 (hp : 10 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 10 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨74, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp)) T74_46
      hfix74_46 hinj74_46 hcardT74_46
      (fun i => conj_mem_of_fixedPoints _ _ (T74_46 i) (hfix74_46 i) _)
      ⟨74, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 10 hp) Q2.T74_46_2 Q2.hfix74_46_2 Q2.hinj74_46_2
      Q2.hcardT74_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_46_2 i) (Q2.hfix74_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨74, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T74_46 = colFn colCertDiv_74_46_10.D1 (m := 5) from colCertDiv_74_46_10.bind1,
    show colData2 (⟨74, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 10 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T74_46_2 = colFn colCertDiv_74_46_10.D2 (m := 5) from colCertDiv_74_46_10.bind2]
  rw [alnId_74 j hj]
  exact fastcode_of_div ⟨74, by decide⟩ _ _ _
    ((alnId_74 j hj) ▸ Q2.listedAt (⟨74, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨74, by decide⟩ : Fin 148) hj hq).1) colCertDiv_74_46_10_match


theorem leaf_74_46_15 (hp : 15 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 15 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨74, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp)) T74_46
      hfix74_46 hinj74_46 hcardT74_46
      (fun i => conj_mem_of_fixedPoints _ _ (T74_46 i) (hfix74_46 i) _)
      ⟨74, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 15 hp) Q2.T74_46_2 Q2.hfix74_46_2 Q2.hinj74_46_2
      Q2.hcardT74_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_46_2 i) (Q2.hfix74_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨74, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T74_46 = colFn colCertDiv_74_46_15.D1 (m := 5) from colCertDiv_74_46_15.bind1,
    show colData2 (⟨74, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 15 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T74_46_2 = colFn colCertDiv_74_46_15.D2 (m := 5) from colCertDiv_74_46_15.bind2]
  rw [alnId_74 j hj]
  exact fastcode_of_div ⟨74, by decide⟩ _ _ _
    ((alnId_74 j hj) ▸ Q2.listedAt (⟨74, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨74, by decide⟩ : Fin 148) hj hq).1) colCertDiv_74_46_15_match


theorem leaf_74_46_20 (hp : 20 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 20 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨74, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp)) T74_46
      hfix74_46 hinj74_46 hcardT74_46
      (fun i => conj_mem_of_fixedPoints _ _ (T74_46 i) (hfix74_46 i) _)
      ⟨74, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 20 hp) Q2.T74_46_2 Q2.hfix74_46_2 Q2.hinj74_46_2
      Q2.hcardT74_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_46_2 i) (Q2.hfix74_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨74, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T74_46 = colFn colCertDiv_74_46_20.D1 (m := 5) from colCertDiv_74_46_20.bind1,
    show colData2 (⟨74, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 20 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T74_46_2 = colFn colCertDiv_74_46_20.D2 (m := 5) from colCertDiv_74_46_20.bind2]
  rw [alnId_74 j hj]
  exact fastcode_of_div ⟨74, by decide⟩ _ _ _
    ((alnId_74 j hj) ▸ Q2.listedAt (⟨74, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨74, by decide⟩ : Fin 148) hj hq).1) colCertDiv_74_46_20_match


theorem leaf_74_51_0 (hp : 0 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 0 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp)) T74_51
      hfix74_51 hinj74_51 hcardT74_51
      (fun i => conj_mem_of_fixedPoints _ _ (T74_51 i) (hfix74_51 i) _)
      ⟨74, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 0 hp) Q2.T74_51_2 Q2.hfix74_51_2 Q2.hinj74_51_2
      Q2.hcardT74_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_51_2 i) (Q2.hfix74_51_2 i) _)
      colCert_74_51_0.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_51_1 (hp : 1 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 1 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp)) T74_51
      hfix74_51 hinj74_51 hcardT74_51
      (fun i => conj_mem_of_fixedPoints _ _ (T74_51 i) (hfix74_51 i) _)
      ⟨74, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 1 hp) Q2.T74_51_2 Q2.hfix74_51_2 Q2.hinj74_51_2
      Q2.hcardT74_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_51_2 i) (Q2.hfix74_51_2 i) _)
      colCert_74_51_1.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_51_2 (hp : 2 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 2 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp)) T74_51
      hfix74_51 hinj74_51 hcardT74_51
      (fun i => conj_mem_of_fixedPoints _ _ (T74_51 i) (hfix74_51 i) _)
      ⟨74, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 2 hp) Q2.T74_51_2 Q2.hfix74_51_2 Q2.hinj74_51_2
      Q2.hcardT74_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_51_2 i) (Q2.hfix74_51_2 i) _)
      colCert_74_51_2.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_51_3 (hp : 3 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 3 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp)) T74_51
      hfix74_51 hinj74_51 hcardT74_51
      (fun i => conj_mem_of_fixedPoints _ _ (T74_51 i) (hfix74_51 i) _)
      ⟨74, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 3 hp) Q2.T74_51_2 Q2.hfix74_51_2 Q2.hinj74_51_2
      Q2.hcardT74_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_51_2 i) (Q2.hfix74_51_2 i) _)
      colCert_74_51_3.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_51_4 (hp : 4 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 4 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp)) T74_51
      hfix74_51 hinj74_51 hcardT74_51
      (fun i => conj_mem_of_fixedPoints _ _ (T74_51 i) (hfix74_51 i) _)
      ⟨74, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 4 hp) Q2.T74_51_2 Q2.hfix74_51_2 Q2.hinj74_51_2
      Q2.hcardT74_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_51_2 i) (Q2.hfix74_51_2 i) _)
      colCert_74_51_4.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_51_5 (hp : 5 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 5 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨74, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp)) T74_51
      hfix74_51 hinj74_51 hcardT74_51
      (fun i => conj_mem_of_fixedPoints _ _ (T74_51 i) (hfix74_51 i) _)
      ⟨74, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 5 hp) Q2.T74_51_2 Q2.hfix74_51_2 Q2.hinj74_51_2
      Q2.hcardT74_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_51_2 i) (Q2.hfix74_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨74, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T74_51 = colFn colCertDiv_74_51_5.D1 (m := 5) from colCertDiv_74_51_5.bind1,
    show colData2 (⟨74, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 5 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T74_51_2 = colFn colCertDiv_74_51_5.D2 (m := 5) from colCertDiv_74_51_5.bind2]
  rw [alnId_74 j hj]
  exact fastcode_of_div ⟨74, by decide⟩ _ _ _
    ((alnId_74 j hj) ▸ Q2.listedAt (⟨74, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨74, by decide⟩ : Fin 148) hj hq).1) colCertDiv_74_51_5_match


theorem leaf_74_51_10 (hp : 10 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 10 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨74, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp)) T74_51
      hfix74_51 hinj74_51 hcardT74_51
      (fun i => conj_mem_of_fixedPoints _ _ (T74_51 i) (hfix74_51 i) _)
      ⟨74, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 10 hp) Q2.T74_51_2 Q2.hfix74_51_2 Q2.hinj74_51_2
      Q2.hcardT74_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_51_2 i) (Q2.hfix74_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨74, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T74_51 = colFn colCertDiv_74_51_10.D1 (m := 5) from colCertDiv_74_51_10.bind1,
    show colData2 (⟨74, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 10 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T74_51_2 = colFn colCertDiv_74_51_10.D2 (m := 5) from colCertDiv_74_51_10.bind2]
  rw [alnId_74 j hj]
  exact fastcode_of_div ⟨74, by decide⟩ _ _ _
    ((alnId_74 j hj) ▸ Q2.listedAt (⟨74, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨74, by decide⟩ : Fin 148) hj hq).1) colCertDiv_74_51_10_match


theorem leaf_74_51_15 (hp : 15 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 15 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨74, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp)) T74_51
      hfix74_51 hinj74_51 hcardT74_51
      (fun i => conj_mem_of_fixedPoints _ _ (T74_51 i) (hfix74_51 i) _)
      ⟨74, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 15 hp) Q2.T74_51_2 Q2.hfix74_51_2 Q2.hinj74_51_2
      Q2.hcardT74_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_51_2 i) (Q2.hfix74_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨74, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T74_51 = colFn colCertDiv_74_51_15.D1 (m := 5) from colCertDiv_74_51_15.bind1,
    show colData2 (⟨74, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 15 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T74_51_2 = colFn colCertDiv_74_51_15.D2 (m := 5) from colCertDiv_74_51_15.bind2]
  rw [alnId_74 j hj]
  exact fastcode_of_div ⟨74, by decide⟩ _ _ _
    ((alnId_74 j hj) ▸ Q2.listedAt (⟨74, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨74, by decide⟩ : Fin 148) hj hq).1) colCertDiv_74_51_15_match


theorem leaf_74_51_20 (hp : 20 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 20 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨74, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp)) T74_51
      hfix74_51 hinj74_51 hcardT74_51
      (fun i => conj_mem_of_fixedPoints _ _ (T74_51 i) (hfix74_51 i) _)
      ⟨74, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 20 hp) Q2.T74_51_2 Q2.hfix74_51_2 Q2.hinj74_51_2
      Q2.hcardT74_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_51_2 i) (Q2.hfix74_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨74, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T74_51 = colFn colCertDiv_74_51_20.D1 (m := 5) from colCertDiv_74_51_20.bind1,
    show colData2 (⟨74, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 20 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T74_51_2 = colFn colCertDiv_74_51_20.D2 (m := 5) from colCertDiv_74_51_20.bind2]
  rw [alnId_74 j hj]
  exact fastcode_of_div ⟨74, by decide⟩ _ _ _
    ((alnId_74 j hj) ▸ Q2.listedAt (⟨74, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨74, by decide⟩ : Fin 148) hj hq).1) colCertDiv_74_51_20_match


theorem leaf_74_74_0 (hp : 0 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 0 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 0 (transLenTr ⟨74, by decide⟩ 0 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 0 (transLenTr ⟨74, by decide⟩ 0 hp)) T74_74
      hfix74_74 hinj74_74 hcardT74_74
      (fun i => conj_mem_of_fixedPoints _ _ (T74_74 i) (hfix74_74 i) _)
      ⟨74, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 0 hp) Q2.T74_74_2 Q2.hfix74_74_2 Q2.hinj74_74_2
      Q2.hcardT74_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_74_2 i) (Q2.hfix74_74_2 i) _)
      colCert_74_74_0.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_74_1 (hp : 1 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 1 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 1 (transLenTr ⟨74, by decide⟩ 1 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 1 (transLenTr ⟨74, by decide⟩ 1 hp)) T74_74
      hfix74_74 hinj74_74 hcardT74_74
      (fun i => conj_mem_of_fixedPoints _ _ (T74_74 i) (hfix74_74 i) _)
      ⟨74, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 1 hp) Q2.T74_74_2 Q2.hfix74_74_2 Q2.hinj74_74_2
      Q2.hcardT74_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_74_2 i) (Q2.hfix74_74_2 i) _)
      colCert_74_74_1.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_74_2 (hp : 2 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 2 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 2 (transLenTr ⟨74, by decide⟩ 2 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 2 (transLenTr ⟨74, by decide⟩ 2 hp)) T74_74
      hfix74_74 hinj74_74 hcardT74_74
      (fun i => conj_mem_of_fixedPoints _ _ (T74_74 i) (hfix74_74 i) _)
      ⟨74, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 2 hp) Q2.T74_74_2 Q2.hfix74_74_2 Q2.hinj74_74_2
      Q2.hcardT74_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_74_2 i) (Q2.hfix74_74_2 i) _)
      colCert_74_74_2.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_74_3 (hp : 3 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 3 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 3 (transLenTr ⟨74, by decide⟩ 3 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 3 (transLenTr ⟨74, by decide⟩ 3 hp)) T74_74
      hfix74_74 hinj74_74 hcardT74_74
      (fun i => conj_mem_of_fixedPoints _ _ (T74_74 i) (hfix74_74 i) _)
      ⟨74, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 3 hp) Q2.T74_74_2 Q2.hfix74_74_2 Q2.hinj74_74_2
      Q2.hcardT74_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_74_2 i) (Q2.hfix74_74_2 i) _)
      colCert_74_74_3.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_74_4 (hp : 4 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 4 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 4 (transLenTr ⟨74, by decide⟩ 4 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 4 (transLenTr ⟨74, by decide⟩ 4 hp)) T74_74
      hfix74_74 hinj74_74 hcardT74_74
      (fun i => conj_mem_of_fixedPoints _ _ (T74_74 i) (hfix74_74 i) _)
      ⟨74, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 4 hp) Q2.T74_74_2 Q2.hfix74_74_2 Q2.hinj74_74_2
      Q2.hcardT74_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_74_2 i) (Q2.hfix74_74_2 i) _)
      colCert_74_74_4.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_74_5 (hp : 5 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 5 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 5 (transLenTr ⟨74, by decide⟩ 5 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 5 (transLenTr ⟨74, by decide⟩ 5 hp)) T74_74
      hfix74_74 hinj74_74 hcardT74_74
      (fun i => conj_mem_of_fixedPoints _ _ (T74_74 i) (hfix74_74 i) _)
      ⟨74, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 5 hp) Q2.T74_74_2 Q2.hfix74_74_2 Q2.hinj74_74_2
      Q2.hcardT74_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_74_2 i) (Q2.hfix74_74_2 i) _)
      colCert_74_74_5.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_74_6 (hp : 6 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 6 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 6 (transLenTr ⟨74, by decide⟩ 6 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 6 (transLenTr ⟨74, by decide⟩ 6 hp)) T74_74
      hfix74_74 hinj74_74 hcardT74_74
      (fun i => conj_mem_of_fixedPoints _ _ (T74_74 i) (hfix74_74 i) _)
      ⟨74, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 6 hp) Q2.T74_74_2 Q2.hfix74_74_2 Q2.hinj74_74_2
      Q2.hcardT74_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_74_2 i) (Q2.hfix74_74_2 i) _)
      colCert_74_74_6.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_74_7 (hp : 7 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 7 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 7 (transLenTr ⟨74, by decide⟩ 7 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 7 (transLenTr ⟨74, by decide⟩ 7 hp)) T74_74
      hfix74_74 hinj74_74 hcardT74_74
      (fun i => conj_mem_of_fixedPoints _ _ (T74_74 i) (hfix74_74 i) _)
      ⟨74, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 7 hp) Q2.T74_74_2 Q2.hfix74_74_2 Q2.hinj74_74_2
      Q2.hcardT74_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_74_2 i) (Q2.hfix74_74_2 i) _)
      colCert_74_74_7.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_74_8 (hp : 8 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 8 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 8 (transLenTr ⟨74, by decide⟩ 8 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 8 (transLenTr ⟨74, by decide⟩ 8 hp)) T74_74
      hfix74_74 hinj74_74 hcardT74_74
      (fun i => conj_mem_of_fixedPoints _ _ (T74_74 i) (hfix74_74 i) _)
      ⟨74, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 8 hp) Q2.T74_74_2 Q2.hfix74_74_2 Q2.hinj74_74_2
      Q2.hcardT74_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_74_2 i) (Q2.hfix74_74_2 i) _)
      colCert_74_74_8.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_74_9 (hp : 9 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 9 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 9 (transLenTr ⟨74, by decide⟩ 9 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 9 (transLenTr ⟨74, by decide⟩ 9 hp)) T74_74
      hfix74_74 hinj74_74 hcardT74_74
      (fun i => conj_mem_of_fixedPoints _ _ (T74_74 i) (hfix74_74 i) _)
      ⟨74, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 9 hp) Q2.T74_74_2 Q2.hfix74_74_2 Q2.hinj74_74_2
      Q2.hcardT74_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_74_2 i) (Q2.hfix74_74_2 i) _)
      colCert_74_74_9.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_74_10 (hp : 10 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 10 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 10 (transLenTr ⟨74, by decide⟩ 10 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 10 (transLenTr ⟨74, by decide⟩ 10 hp)) T74_74
      hfix74_74 hinj74_74 hcardT74_74
      (fun i => conj_mem_of_fixedPoints _ _ (T74_74 i) (hfix74_74 i) _)
      ⟨74, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 10 hp) Q2.T74_74_2 Q2.hfix74_74_2 Q2.hinj74_74_2
      Q2.hcardT74_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_74_2 i) (Q2.hfix74_74_2 i) _)
      colCert_74_74_10.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_74_11 (hp : 11 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 11 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 11 (transLenTr ⟨74, by decide⟩ 11 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 11 (transLenTr ⟨74, by decide⟩ 11 hp)) T74_74
      hfix74_74 hinj74_74 hcardT74_74
      (fun i => conj_mem_of_fixedPoints _ _ (T74_74 i) (hfix74_74 i) _)
      ⟨74, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 11 hp) Q2.T74_74_2 Q2.hfix74_74_2 Q2.hinj74_74_2
      Q2.hcardT74_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_74_2 i) (Q2.hfix74_74_2 i) _)
      colCert_74_74_11.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_74_12 (hp : 12 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 12 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 12 (transLenTr ⟨74, by decide⟩ 12 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 12 (transLenTr ⟨74, by decide⟩ 12 hp)) T74_74
      hfix74_74 hinj74_74 hcardT74_74
      (fun i => conj_mem_of_fixedPoints _ _ (T74_74 i) (hfix74_74 i) _)
      ⟨74, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 12 hp) Q2.T74_74_2 Q2.hfix74_74_2 Q2.hinj74_74_2
      Q2.hcardT74_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_74_2 i) (Q2.hfix74_74_2 i) _)
      colCert_74_74_12.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_74_13 (hp : 13 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 13 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 13 (transLenTr ⟨74, by decide⟩ 13 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 13 (transLenTr ⟨74, by decide⟩ 13 hp)) T74_74
      hfix74_74 hinj74_74 hcardT74_74
      (fun i => conj_mem_of_fixedPoints _ _ (T74_74 i) (hfix74_74 i) _)
      ⟨74, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 13 hp) Q2.T74_74_2 Q2.hfix74_74_2 Q2.hinj74_74_2
      Q2.hcardT74_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_74_2 i) (Q2.hfix74_74_2 i) _)
      colCert_74_74_13.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_74_14 (hp : 14 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 14 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 14 (transLenTr ⟨74, by decide⟩ 14 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 14 (transLenTr ⟨74, by decide⟩ 14 hp)) T74_74
      hfix74_74 hinj74_74 hcardT74_74
      (fun i => conj_mem_of_fixedPoints _ _ (T74_74 i) (hfix74_74 i) _)
      ⟨74, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 14 hp) Q2.T74_74_2 Q2.hfix74_74_2 Q2.hinj74_74_2
      Q2.hcardT74_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_74_2 i) (Q2.hfix74_74_2 i) _)
      colCert_74_74_14.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_74_15 (hp : 15 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 15 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 15 (transLenTr ⟨74, by decide⟩ 15 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 15 (transLenTr ⟨74, by decide⟩ 15 hp)) T74_74
      hfix74_74 hinj74_74 hcardT74_74
      (fun i => conj_mem_of_fixedPoints _ _ (T74_74 i) (hfix74_74 i) _)
      ⟨74, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 15 hp) Q2.T74_74_2 Q2.hfix74_74_2 Q2.hinj74_74_2
      Q2.hcardT74_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_74_2 i) (Q2.hfix74_74_2 i) _)
      colCert_74_74_15.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_74_16 (hp : 16 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 16 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 16 (transLenTr ⟨74, by decide⟩ 16 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 16 (transLenTr ⟨74, by decide⟩ 16 hp)) T74_74
      hfix74_74 hinj74_74 hcardT74_74
      (fun i => conj_mem_of_fixedPoints _ _ (T74_74 i) (hfix74_74 i) _)
      ⟨74, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 16 hp) Q2.T74_74_2 Q2.hfix74_74_2 Q2.hinj74_74_2
      Q2.hcardT74_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_74_2 i) (Q2.hfix74_74_2 i) _)
      colCert_74_74_16.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_74_17 (hp : 17 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 17 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 17 (transLenTr ⟨74, by decide⟩ 17 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 17 (transLenTr ⟨74, by decide⟩ 17 hp)) T74_74
      hfix74_74 hinj74_74 hcardT74_74
      (fun i => conj_mem_of_fixedPoints _ _ (T74_74 i) (hfix74_74 i) _)
      ⟨74, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 17 hp) Q2.T74_74_2 Q2.hfix74_74_2 Q2.hinj74_74_2
      Q2.hcardT74_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_74_2 i) (Q2.hfix74_74_2 i) _)
      colCert_74_74_17.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_74_18 (hp : 18 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 18 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 18 (transLenTr ⟨74, by decide⟩ 18 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 18 (transLenTr ⟨74, by decide⟩ 18 hp)) T74_74
      hfix74_74 hinj74_74 hcardT74_74
      (fun i => conj_mem_of_fixedPoints _ _ (T74_74 i) (hfix74_74 i) _)
      ⟨74, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 18 hp) Q2.T74_74_2 Q2.hfix74_74_2 Q2.hinj74_74_2
      Q2.hcardT74_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_74_2 i) (Q2.hfix74_74_2 i) _)
      colCert_74_74_18.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_74_19 (hp : 19 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 19 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 19 (transLenTr ⟨74, by decide⟩ 19 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 19 (transLenTr ⟨74, by decide⟩ 19 hp)) T74_74
      hfix74_74 hinj74_74 hcardT74_74
      (fun i => conj_mem_of_fixedPoints _ _ (T74_74 i) (hfix74_74 i) _)
      ⟨74, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 19 hp) Q2.T74_74_2 Q2.hfix74_74_2 Q2.hinj74_74_2
      Q2.hcardT74_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_74_2 i) (Q2.hfix74_74_2 i) _)
      colCert_74_74_19.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_74_20 (hp : 20 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 20 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 20 (transLenTr ⟨74, by decide⟩ 20 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 20 (transLenTr ⟨74, by decide⟩ 20 hp)) T74_74
      hfix74_74 hinj74_74 hcardT74_74
      (fun i => conj_mem_of_fixedPoints _ _ (T74_74 i) (hfix74_74 i) _)
      ⟨74, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 20 hp) Q2.T74_74_2 Q2.hfix74_74_2 Q2.hinj74_74_2
      Q2.hcardT74_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_74_2 i) (Q2.hfix74_74_2 i) _)
      colCert_74_74_20.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_74_21 (hp : 21 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 21 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 21 (transLenTr ⟨74, by decide⟩ 21 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 21 (transLenTr ⟨74, by decide⟩ 21 hp)) T74_74
      hfix74_74 hinj74_74 hcardT74_74
      (fun i => conj_mem_of_fixedPoints _ _ (T74_74 i) (hfix74_74 i) _)
      ⟨74, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 21 hp) Q2.T74_74_2 Q2.hfix74_74_2 Q2.hinj74_74_2
      Q2.hcardT74_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_74_2 i) (Q2.hfix74_74_2 i) _)
      colCert_74_74_21.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_74_22 (hp : 22 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 22 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 22 (transLenTr ⟨74, by decide⟩ 22 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 22 (transLenTr ⟨74, by decide⟩ 22 hp)) T74_74
      hfix74_74 hinj74_74 hcardT74_74
      (fun i => conj_mem_of_fixedPoints _ _ (T74_74 i) (hfix74_74 i) _)
      ⟨74, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 22 hp) Q2.T74_74_2 Q2.hfix74_74_2 Q2.hinj74_74_2
      Q2.hcardT74_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_74_2 i) (Q2.hfix74_74_2 i) _)
      colCert_74_74_22.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_74_23 (hp : 23 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 23 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 23 (transLenTr ⟨74, by decide⟩ 23 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 23 (transLenTr ⟨74, by decide⟩ 23 hp)) T74_74
      hfix74_74 hinj74_74 hcardT74_74
      (fun i => conj_mem_of_fixedPoints _ _ (T74_74 i) (hfix74_74 i) _)
      ⟨74, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 23 hp) Q2.T74_74_2 Q2.hfix74_74_2 Q2.hinj74_74_2
      Q2.hcardT74_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_74_2 i) (Q2.hfix74_74_2 i) _)
      colCert_74_74_23.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_74_24 (hp : 24 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 24 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 24 (transLenTr ⟨74, by decide⟩ 24 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 24 (transLenTr ⟨74, by decide⟩ 24 hp)) T74_74
      hfix74_74 hinj74_74 hcardT74_74
      (fun i => conj_mem_of_fixedPoints _ _ (T74_74 i) (hfix74_74 i) _)
      ⟨74, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 24 hp) Q2.T74_74_2 Q2.hfix74_74_2 Q2.hinj74_74_2
      Q2.hcardT74_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_74_2 i) (Q2.hfix74_74_2 i) _)
      colCert_74_74_24.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_75_9_0 (hp : 0 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 0 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp)) T75_9
      hfix75_9 hinj75_9 hcardT75_9
      (fun i => conj_mem_of_fixedPoints _ _ (T75_9 i) (hfix75_9 i) _)
      ⟨75, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 0 hp) Q2.T75_9_2 Q2.hfix75_9_2 Q2.hinj75_9_2
      Q2.hcardT75_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_9_2 i) (Q2.hfix75_9_2 i) _)
      colCert_75_9_0.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_9_1 (hp : 1 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 1 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp)) T75_9
      hfix75_9 hinj75_9 hcardT75_9
      (fun i => conj_mem_of_fixedPoints _ _ (T75_9 i) (hfix75_9 i) _)
      ⟨75, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 1 hp) Q2.T75_9_2 Q2.hfix75_9_2 Q2.hinj75_9_2
      Q2.hcardT75_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_9_2 i) (Q2.hfix75_9_2 i) _)
      colCert_75_9_1.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_9_2 (hp : 2 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 2 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp)) T75_9
      hfix75_9 hinj75_9 hcardT75_9
      (fun i => conj_mem_of_fixedPoints _ _ (T75_9 i) (hfix75_9 i) _)
      ⟨75, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 2 hp) Q2.T75_9_2 Q2.hfix75_9_2 Q2.hinj75_9_2
      Q2.hcardT75_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_9_2 i) (Q2.hfix75_9_2 i) _)
      colCert_75_9_2.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_9_3 (hp : 3 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 3 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp)) T75_9
      hfix75_9 hinj75_9 hcardT75_9
      (fun i => conj_mem_of_fixedPoints _ _ (T75_9 i) (hfix75_9 i) _)
      ⟨75, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 3 hp) Q2.T75_9_2 Q2.hfix75_9_2 Q2.hinj75_9_2
      Q2.hcardT75_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_9_2 i) (Q2.hfix75_9_2 i) _)
      colCert_75_9_3.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_9_4 (hp : 4 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 4 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp)) T75_9
      hfix75_9 hinj75_9 hcardT75_9
      (fun i => conj_mem_of_fixedPoints _ _ (T75_9 i) (hfix75_9 i) _)
      ⟨75, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 4 hp) Q2.T75_9_2 Q2.hfix75_9_2 Q2.hinj75_9_2
      Q2.hcardT75_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_9_2 i) (Q2.hfix75_9_2 i) _)
      colCert_75_9_4.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T75_12
      hfix75_12 hinj75_12 hcardT75_12
      (fun i => conj_mem_of_fixedPoints _ _ (T75_12 i) (hfix75_12 i) _)
      ⟨75, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T75_12_2 Q2.hfix75_12_2 Q2.hinj75_12_2
      Q2.hcardT75_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_12_2 i) (Q2.hfix75_12_2 i) _)
      colCert_75_12_0.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T75_12
      hfix75_12 hinj75_12 hcardT75_12
      (fun i => conj_mem_of_fixedPoints _ _ (T75_12 i) (hfix75_12 i) _)
      ⟨75, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T75_12_2 Q2.hfix75_12_2 Q2.hinj75_12_2
      Q2.hcardT75_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_12_2 i) (Q2.hfix75_12_2 i) _)
      colCert_75_12_1.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T75_12
      hfix75_12 hinj75_12 hcardT75_12
      (fun i => conj_mem_of_fixedPoints _ _ (T75_12 i) (hfix75_12 i) _)
      ⟨75, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T75_12_2 Q2.hfix75_12_2 Q2.hinj75_12_2
      Q2.hcardT75_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_12_2 i) (Q2.hfix75_12_2 i) _)
      colCert_75_12_2.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T75_12
      hfix75_12 hinj75_12 hcardT75_12
      (fun i => conj_mem_of_fixedPoints _ _ (T75_12 i) (hfix75_12 i) _)
      ⟨75, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T75_12_2 Q2.hfix75_12_2 Q2.hinj75_12_2
      Q2.hcardT75_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_12_2 i) (Q2.hfix75_12_2 i) _)
      colCert_75_12_3.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T75_12
      hfix75_12 hinj75_12 hcardT75_12
      (fun i => conj_mem_of_fixedPoints _ _ (T75_12 i) (hfix75_12 i) _)
      ⟨75, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T75_12_2 Q2.hfix75_12_2 Q2.hinj75_12_2
      Q2.hcardT75_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_12_2 i) (Q2.hfix75_12_2 i) _)
      colCert_75_12_4.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_27_0 (hp : 0 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 0 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp)) T75_27
      hfix75_27 hinj75_27 hcardT75_27
      (fun i => conj_mem_of_fixedPoints _ _ (T75_27 i) (hfix75_27 i) _)
      ⟨75, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 0 hp) Q2.T75_27_2 Q2.hfix75_27_2 Q2.hinj75_27_2
      Q2.hcardT75_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_27_2 i) (Q2.hfix75_27_2 i) _)
      colCert_75_27_0.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_27_1 (hp : 1 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 1 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp)) T75_27
      hfix75_27 hinj75_27 hcardT75_27
      (fun i => conj_mem_of_fixedPoints _ _ (T75_27 i) (hfix75_27 i) _)
      ⟨75, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 1 hp) Q2.T75_27_2 Q2.hfix75_27_2 Q2.hinj75_27_2
      Q2.hcardT75_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_27_2 i) (Q2.hfix75_27_2 i) _)
      colCert_75_27_1.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_27_2 (hp : 2 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 2 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp)) T75_27
      hfix75_27 hinj75_27 hcardT75_27
      (fun i => conj_mem_of_fixedPoints _ _ (T75_27 i) (hfix75_27 i) _)
      ⟨75, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 2 hp) Q2.T75_27_2 Q2.hfix75_27_2 Q2.hinj75_27_2
      Q2.hcardT75_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_27_2 i) (Q2.hfix75_27_2 i) _)
      colCert_75_27_2.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_27_3 (hp : 3 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 3 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp)) T75_27
      hfix75_27 hinj75_27 hcardT75_27
      (fun i => conj_mem_of_fixedPoints _ _ (T75_27 i) (hfix75_27 i) _)
      ⟨75, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 3 hp) Q2.T75_27_2 Q2.hfix75_27_2 Q2.hinj75_27_2
      Q2.hcardT75_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_27_2 i) (Q2.hfix75_27_2 i) _)
      colCert_75_27_3.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_27_4 (hp : 4 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 4 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp)) T75_27
      hfix75_27 hinj75_27 hcardT75_27
      (fun i => conj_mem_of_fixedPoints _ _ (T75_27 i) (hfix75_27 i) _)
      ⟨75, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 4 hp) Q2.T75_27_2 Q2.hfix75_27_2 Q2.hinj75_27_2
      Q2.hcardT75_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_27_2 i) (Q2.hfix75_27_2 i) _)
      colCert_75_27_4.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_27_5 (hp : 5 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 5 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp)) T75_27
      hfix75_27 hinj75_27 hcardT75_27
      (fun i => conj_mem_of_fixedPoints _ _ (T75_27 i) (hfix75_27 i) _)
      ⟨75, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 5 hp) Q2.T75_27_2 Q2.hfix75_27_2 Q2.hinj75_27_2
      Q2.hcardT75_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_27_2 i) (Q2.hfix75_27_2 i) _)
      colCert_75_27_5.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_27_10 (hp : 10 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 10 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp)) T75_27
      hfix75_27 hinj75_27 hcardT75_27
      (fun i => conj_mem_of_fixedPoints _ _ (T75_27 i) (hfix75_27 i) _)
      ⟨75, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 10 hp) Q2.T75_27_2 Q2.hfix75_27_2 Q2.hinj75_27_2
      Q2.hcardT75_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_27_2 i) (Q2.hfix75_27_2 i) _)
      colCert_75_27_10.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_27_15 (hp : 15 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 15 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp)) T75_27
      hfix75_27 hinj75_27 hcardT75_27
      (fun i => conj_mem_of_fixedPoints _ _ (T75_27 i) (hfix75_27 i) _)
      ⟨75, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 15 hp) Q2.T75_27_2 Q2.hfix75_27_2 Q2.hinj75_27_2
      Q2.hcardT75_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_27_2 i) (Q2.hfix75_27_2 i) _)
      colCert_75_27_15.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_27_20 (hp : 20 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 20 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp)) T75_27
      hfix75_27 hinj75_27 hcardT75_27
      (fun i => conj_mem_of_fixedPoints _ _ (T75_27 i) (hfix75_27 i) _)
      ⟨75, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 20 hp) Q2.T75_27_2 Q2.hfix75_27_2 Q2.hinj75_27_2
      Q2.hcardT75_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_27_2 i) (Q2.hfix75_27_2 i) _)
      colCert_75_27_20.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_32_0 (hp : 0 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 0 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp)) T75_32
      hfix75_32 hinj75_32 hcardT75_32
      (fun i => conj_mem_of_fixedPoints _ _ (T75_32 i) (hfix75_32 i) _)
      ⟨75, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 0 hp) Q2.T75_32_2 Q2.hfix75_32_2 Q2.hinj75_32_2
      Q2.hcardT75_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_32_2 i) (Q2.hfix75_32_2 i) _)
      colCert_75_32_0.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_32_1 (hp : 1 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 1 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp)) T75_32
      hfix75_32 hinj75_32 hcardT75_32
      (fun i => conj_mem_of_fixedPoints _ _ (T75_32 i) (hfix75_32 i) _)
      ⟨75, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 1 hp) Q2.T75_32_2 Q2.hfix75_32_2 Q2.hinj75_32_2
      Q2.hcardT75_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_32_2 i) (Q2.hfix75_32_2 i) _)
      colCert_75_32_1.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_32_2 (hp : 2 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 2 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp)) T75_32
      hfix75_32 hinj75_32 hcardT75_32
      (fun i => conj_mem_of_fixedPoints _ _ (T75_32 i) (hfix75_32 i) _)
      ⟨75, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 2 hp) Q2.T75_32_2 Q2.hfix75_32_2 Q2.hinj75_32_2
      Q2.hcardT75_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_32_2 i) (Q2.hfix75_32_2 i) _)
      colCert_75_32_2.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_32_3 (hp : 3 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 3 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp)) T75_32
      hfix75_32 hinj75_32 hcardT75_32
      (fun i => conj_mem_of_fixedPoints _ _ (T75_32 i) (hfix75_32 i) _)
      ⟨75, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 3 hp) Q2.T75_32_2 Q2.hfix75_32_2 Q2.hinj75_32_2
      Q2.hcardT75_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_32_2 i) (Q2.hfix75_32_2 i) _)
      colCert_75_32_3.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_32_4 (hp : 4 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 4 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp)) T75_32
      hfix75_32 hinj75_32 hcardT75_32
      (fun i => conj_mem_of_fixedPoints _ _ (T75_32 i) (hfix75_32 i) _)
      ⟨75, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 4 hp) Q2.T75_32_2 Q2.hfix75_32_2 Q2.hinj75_32_2
      Q2.hcardT75_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_32_2 i) (Q2.hfix75_32_2 i) _)
      colCert_75_32_4.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_32_5 (hp : 5 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 5 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp)) T75_32
      hfix75_32 hinj75_32 hcardT75_32
      (fun i => conj_mem_of_fixedPoints _ _ (T75_32 i) (hfix75_32 i) _)
      ⟨75, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 5 hp) Q2.T75_32_2 Q2.hfix75_32_2 Q2.hinj75_32_2
      Q2.hcardT75_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_32_2 i) (Q2.hfix75_32_2 i) _)
      colCert_75_32_5.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_32_10 (hp : 10 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 10 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp)) T75_32
      hfix75_32 hinj75_32 hcardT75_32
      (fun i => conj_mem_of_fixedPoints _ _ (T75_32 i) (hfix75_32 i) _)
      ⟨75, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 10 hp) Q2.T75_32_2 Q2.hfix75_32_2 Q2.hinj75_32_2
      Q2.hcardT75_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_32_2 i) (Q2.hfix75_32_2 i) _)
      colCert_75_32_10.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_32_15 (hp : 15 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 15 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp)) T75_32
      hfix75_32 hinj75_32 hcardT75_32
      (fun i => conj_mem_of_fixedPoints _ _ (T75_32 i) (hfix75_32 i) _)
      ⟨75, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 15 hp) Q2.T75_32_2 Q2.hfix75_32_2 Q2.hinj75_32_2
      Q2.hcardT75_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_32_2 i) (Q2.hfix75_32_2 i) _)
      colCert_75_32_15.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_32_20 (hp : 20 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 20 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp)) T75_32
      hfix75_32 hinj75_32 hcardT75_32
      (fun i => conj_mem_of_fixedPoints _ _ (T75_32 i) (hfix75_32 i) _)
      ⟨75, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 20 hp) Q2.T75_32_2 Q2.hfix75_32_2 Q2.hinj75_32_2
      Q2.hcardT75_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_32_2 i) (Q2.hfix75_32_2 i) _)
      colCert_75_32_20.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_37_0 (hp : 0 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 0 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp)) T75_37
      hfix75_37 hinj75_37 hcardT75_37
      (fun i => conj_mem_of_fixedPoints _ _ (T75_37 i) (hfix75_37 i) _)
      ⟨75, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 0 hp) Q2.T75_37_2 Q2.hfix75_37_2 Q2.hinj75_37_2
      Q2.hcardT75_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_37_2 i) (Q2.hfix75_37_2 i) _)
      colCert_75_37_0.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_37_1 (hp : 1 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 1 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp)) T75_37
      hfix75_37 hinj75_37 hcardT75_37
      (fun i => conj_mem_of_fixedPoints _ _ (T75_37 i) (hfix75_37 i) _)
      ⟨75, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 1 hp) Q2.T75_37_2 Q2.hfix75_37_2 Q2.hinj75_37_2
      Q2.hcardT75_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_37_2 i) (Q2.hfix75_37_2 i) _)
      colCert_75_37_1.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_37_2 (hp : 2 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 2 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp)) T75_37
      hfix75_37 hinj75_37 hcardT75_37
      (fun i => conj_mem_of_fixedPoints _ _ (T75_37 i) (hfix75_37 i) _)
      ⟨75, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 2 hp) Q2.T75_37_2 Q2.hfix75_37_2 Q2.hinj75_37_2
      Q2.hcardT75_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_37_2 i) (Q2.hfix75_37_2 i) _)
      colCert_75_37_2.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_37_3 (hp : 3 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 3 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp)) T75_37
      hfix75_37 hinj75_37 hcardT75_37
      (fun i => conj_mem_of_fixedPoints _ _ (T75_37 i) (hfix75_37 i) _)
      ⟨75, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 3 hp) Q2.T75_37_2 Q2.hfix75_37_2 Q2.hinj75_37_2
      Q2.hcardT75_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_37_2 i) (Q2.hfix75_37_2 i) _)
      colCert_75_37_3.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_37_4 (hp : 4 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 4 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp)) T75_37
      hfix75_37 hinj75_37 hcardT75_37
      (fun i => conj_mem_of_fixedPoints _ _ (T75_37 i) (hfix75_37 i) _)
      ⟨75, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 4 hp) Q2.T75_37_2 Q2.hfix75_37_2 Q2.hinj75_37_2
      Q2.hcardT75_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_37_2 i) (Q2.hfix75_37_2 i) _)
      colCert_75_37_4.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_37_5 (hp : 5 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 5 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp)) T75_37
      hfix75_37 hinj75_37 hcardT75_37
      (fun i => conj_mem_of_fixedPoints _ _ (T75_37 i) (hfix75_37 i) _)
      ⟨75, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 5 hp) Q2.T75_37_2 Q2.hfix75_37_2 Q2.hinj75_37_2
      Q2.hcardT75_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_37_2 i) (Q2.hfix75_37_2 i) _)
      colCert_75_37_5.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_37_10 (hp : 10 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 10 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp)) T75_37
      hfix75_37 hinj75_37 hcardT75_37
      (fun i => conj_mem_of_fixedPoints _ _ (T75_37 i) (hfix75_37 i) _)
      ⟨75, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 10 hp) Q2.T75_37_2 Q2.hfix75_37_2 Q2.hinj75_37_2
      Q2.hcardT75_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_37_2 i) (Q2.hfix75_37_2 i) _)
      colCert_75_37_10.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_37_15 (hp : 15 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 15 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp)) T75_37
      hfix75_37 hinj75_37 hcardT75_37
      (fun i => conj_mem_of_fixedPoints _ _ (T75_37 i) (hfix75_37 i) _)
      ⟨75, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 15 hp) Q2.T75_37_2 Q2.hfix75_37_2 Q2.hinj75_37_2
      Q2.hcardT75_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_37_2 i) (Q2.hfix75_37_2 i) _)
      colCert_75_37_15.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_37_20 (hp : 20 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 20 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp)) T75_37
      hfix75_37 hinj75_37 hcardT75_37
      (fun i => conj_mem_of_fixedPoints _ _ (T75_37 i) (hfix75_37 i) _)
      ⟨75, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 20 hp) Q2.T75_37_2 Q2.hfix75_37_2 Q2.hinj75_37_2
      Q2.hcardT75_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_37_2 i) (Q2.hfix75_37_2 i) _)
      colCert_75_37_20.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_42_0 (hp : 0 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 0 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp)) T75_42
      hfix75_42 hinj75_42 hcardT75_42
      (fun i => conj_mem_of_fixedPoints _ _ (T75_42 i) (hfix75_42 i) _)
      ⟨75, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 0 hp) Q2.T75_42_2 Q2.hfix75_42_2 Q2.hinj75_42_2
      Q2.hcardT75_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_42_2 i) (Q2.hfix75_42_2 i) _)
      colCert_75_42_0.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_42_1 (hp : 1 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 1 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp)) T75_42
      hfix75_42 hinj75_42 hcardT75_42
      (fun i => conj_mem_of_fixedPoints _ _ (T75_42 i) (hfix75_42 i) _)
      ⟨75, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 1 hp) Q2.T75_42_2 Q2.hfix75_42_2 Q2.hinj75_42_2
      Q2.hcardT75_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_42_2 i) (Q2.hfix75_42_2 i) _)
      colCert_75_42_1.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_42_2 (hp : 2 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 2 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp)) T75_42
      hfix75_42 hinj75_42 hcardT75_42
      (fun i => conj_mem_of_fixedPoints _ _ (T75_42 i) (hfix75_42 i) _)
      ⟨75, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 2 hp) Q2.T75_42_2 Q2.hfix75_42_2 Q2.hinj75_42_2
      Q2.hcardT75_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_42_2 i) (Q2.hfix75_42_2 i) _)
      colCert_75_42_2.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_42_3 (hp : 3 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 3 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp)) T75_42
      hfix75_42 hinj75_42 hcardT75_42
      (fun i => conj_mem_of_fixedPoints _ _ (T75_42 i) (hfix75_42 i) _)
      ⟨75, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 3 hp) Q2.T75_42_2 Q2.hfix75_42_2 Q2.hinj75_42_2
      Q2.hcardT75_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_42_2 i) (Q2.hfix75_42_2 i) _)
      colCert_75_42_3.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_42_4 (hp : 4 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 4 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp)) T75_42
      hfix75_42 hinj75_42 hcardT75_42
      (fun i => conj_mem_of_fixedPoints _ _ (T75_42 i) (hfix75_42 i) _)
      ⟨75, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 4 hp) Q2.T75_42_2 Q2.hfix75_42_2 Q2.hinj75_42_2
      Q2.hcardT75_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_42_2 i) (Q2.hfix75_42_2 i) _)
      colCert_75_42_4.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_42_5 (hp : 5 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 5 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp)) T75_42
      hfix75_42 hinj75_42 hcardT75_42
      (fun i => conj_mem_of_fixedPoints _ _ (T75_42 i) (hfix75_42 i) _)
      ⟨75, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 5 hp) Q2.T75_42_2 Q2.hfix75_42_2 Q2.hinj75_42_2
      Q2.hcardT75_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_42_2 i) (Q2.hfix75_42_2 i) _)
      colCert_75_42_5.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_42_10 (hp : 10 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 10 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp)) T75_42
      hfix75_42 hinj75_42 hcardT75_42
      (fun i => conj_mem_of_fixedPoints _ _ (T75_42 i) (hfix75_42 i) _)
      ⟨75, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 10 hp) Q2.T75_42_2 Q2.hfix75_42_2 Q2.hinj75_42_2
      Q2.hcardT75_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_42_2 i) (Q2.hfix75_42_2 i) _)
      colCert_75_42_10.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_42_15 (hp : 15 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 15 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp)) T75_42
      hfix75_42 hinj75_42 hcardT75_42
      (fun i => conj_mem_of_fixedPoints _ _ (T75_42 i) (hfix75_42 i) _)
      ⟨75, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 15 hp) Q2.T75_42_2 Q2.hfix75_42_2 Q2.hinj75_42_2
      Q2.hcardT75_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_42_2 i) (Q2.hfix75_42_2 i) _)
      colCert_75_42_15.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_42_20 (hp : 20 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 20 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp)) T75_42
      hfix75_42 hinj75_42 hcardT75_42
      (fun i => conj_mem_of_fixedPoints _ _ (T75_42 i) (hfix75_42 i) _)
      ⟨75, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 20 hp) Q2.T75_42_2 Q2.hfix75_42_2 Q2.hinj75_42_2
      Q2.hcardT75_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_42_2 i) (Q2.hfix75_42_2 i) _)
      colCert_75_42_20.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_47_0 (hp : 0 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 0 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp)) T75_47
      hfix75_47 hinj75_47 hcardT75_47
      (fun i => conj_mem_of_fixedPoints _ _ (T75_47 i) (hfix75_47 i) _)
      ⟨75, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 0 hp) Q2.T75_47_2 Q2.hfix75_47_2 Q2.hinj75_47_2
      Q2.hcardT75_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_47_2 i) (Q2.hfix75_47_2 i) _)
      colCert_75_47_0.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_47_1 (hp : 1 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 1 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp)) T75_47
      hfix75_47 hinj75_47 hcardT75_47
      (fun i => conj_mem_of_fixedPoints _ _ (T75_47 i) (hfix75_47 i) _)
      ⟨75, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 1 hp) Q2.T75_47_2 Q2.hfix75_47_2 Q2.hinj75_47_2
      Q2.hcardT75_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_47_2 i) (Q2.hfix75_47_2 i) _)
      colCert_75_47_1.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_47_2 (hp : 2 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 2 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp)) T75_47
      hfix75_47 hinj75_47 hcardT75_47
      (fun i => conj_mem_of_fixedPoints _ _ (T75_47 i) (hfix75_47 i) _)
      ⟨75, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 2 hp) Q2.T75_47_2 Q2.hfix75_47_2 Q2.hinj75_47_2
      Q2.hcardT75_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_47_2 i) (Q2.hfix75_47_2 i) _)
      colCert_75_47_2.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_47_3 (hp : 3 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 3 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp)) T75_47
      hfix75_47 hinj75_47 hcardT75_47
      (fun i => conj_mem_of_fixedPoints _ _ (T75_47 i) (hfix75_47 i) _)
      ⟨75, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 3 hp) Q2.T75_47_2 Q2.hfix75_47_2 Q2.hinj75_47_2
      Q2.hcardT75_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_47_2 i) (Q2.hfix75_47_2 i) _)
      colCert_75_47_3.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_47_4 (hp : 4 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 4 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp)) T75_47
      hfix75_47 hinj75_47 hcardT75_47
      (fun i => conj_mem_of_fixedPoints _ _ (T75_47 i) (hfix75_47 i) _)
      ⟨75, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 4 hp) Q2.T75_47_2 Q2.hfix75_47_2 Q2.hinj75_47_2
      Q2.hcardT75_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_47_2 i) (Q2.hfix75_47_2 i) _)
      colCert_75_47_4.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_47_5 (hp : 5 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 5 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp)) T75_47
      hfix75_47 hinj75_47 hcardT75_47
      (fun i => conj_mem_of_fixedPoints _ _ (T75_47 i) (hfix75_47 i) _)
      ⟨75, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 5 hp) Q2.T75_47_2 Q2.hfix75_47_2 Q2.hinj75_47_2
      Q2.hcardT75_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_47_2 i) (Q2.hfix75_47_2 i) _)
      colCert_75_47_5.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_47_10 (hp : 10 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 10 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp)) T75_47
      hfix75_47 hinj75_47 hcardT75_47
      (fun i => conj_mem_of_fixedPoints _ _ (T75_47 i) (hfix75_47 i) _)
      ⟨75, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 10 hp) Q2.T75_47_2 Q2.hfix75_47_2 Q2.hinj75_47_2
      Q2.hcardT75_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_47_2 i) (Q2.hfix75_47_2 i) _)
      colCert_75_47_10.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_47_15 (hp : 15 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 15 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp)) T75_47
      hfix75_47 hinj75_47 hcardT75_47
      (fun i => conj_mem_of_fixedPoints _ _ (T75_47 i) (hfix75_47 i) _)
      ⟨75, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 15 hp) Q2.T75_47_2 Q2.hfix75_47_2 Q2.hinj75_47_2
      Q2.hcardT75_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_47_2 i) (Q2.hfix75_47_2 i) _)
      colCert_75_47_15.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_47_20 (hp : 20 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 20 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp)) T75_47
      hfix75_47 hinj75_47 hcardT75_47
      (fun i => conj_mem_of_fixedPoints _ _ (T75_47 i) (hfix75_47 i) _)
      ⟨75, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 20 hp) Q2.T75_47_2 Q2.hfix75_47_2 Q2.hinj75_47_2
      Q2.hcardT75_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_47_2 i) (Q2.hfix75_47_2 i) _)
      colCert_75_47_20.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_52_0 (hp : 0 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 0 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp)) T75_52
      hfix75_52 hinj75_52 hcardT75_52
      (fun i => conj_mem_of_fixedPoints _ _ (T75_52 i) (hfix75_52 i) _)
      ⟨75, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 0 hp) Q2.T75_52_2 Q2.hfix75_52_2 Q2.hinj75_52_2
      Q2.hcardT75_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_52_2 i) (Q2.hfix75_52_2 i) _)
      colCert_75_52_0.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_52_1 (hp : 1 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 1 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp)) T75_52
      hfix75_52 hinj75_52 hcardT75_52
      (fun i => conj_mem_of_fixedPoints _ _ (T75_52 i) (hfix75_52 i) _)
      ⟨75, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 1 hp) Q2.T75_52_2 Q2.hfix75_52_2 Q2.hinj75_52_2
      Q2.hcardT75_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_52_2 i) (Q2.hfix75_52_2 i) _)
      colCert_75_52_1.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_52_2 (hp : 2 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 2 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp)) T75_52
      hfix75_52 hinj75_52 hcardT75_52
      (fun i => conj_mem_of_fixedPoints _ _ (T75_52 i) (hfix75_52 i) _)
      ⟨75, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 2 hp) Q2.T75_52_2 Q2.hfix75_52_2 Q2.hinj75_52_2
      Q2.hcardT75_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_52_2 i) (Q2.hfix75_52_2 i) _)
      colCert_75_52_2.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_52_3 (hp : 3 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 3 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp)) T75_52
      hfix75_52 hinj75_52 hcardT75_52
      (fun i => conj_mem_of_fixedPoints _ _ (T75_52 i) (hfix75_52 i) _)
      ⟨75, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 3 hp) Q2.T75_52_2 Q2.hfix75_52_2 Q2.hinj75_52_2
      Q2.hcardT75_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_52_2 i) (Q2.hfix75_52_2 i) _)
      colCert_75_52_3.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_52_4 (hp : 4 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 4 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp)) T75_52
      hfix75_52 hinj75_52 hcardT75_52
      (fun i => conj_mem_of_fixedPoints _ _ (T75_52 i) (hfix75_52 i) _)
      ⟨75, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 4 hp) Q2.T75_52_2 Q2.hfix75_52_2 Q2.hinj75_52_2
      Q2.hcardT75_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_52_2 i) (Q2.hfix75_52_2 i) _)
      colCert_75_52_4.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_52_5 (hp : 5 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 5 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp)) T75_52
      hfix75_52 hinj75_52 hcardT75_52
      (fun i => conj_mem_of_fixedPoints _ _ (T75_52 i) (hfix75_52 i) _)
      ⟨75, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 5 hp) Q2.T75_52_2 Q2.hfix75_52_2 Q2.hinj75_52_2
      Q2.hcardT75_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_52_2 i) (Q2.hfix75_52_2 i) _)
      colCert_75_52_5.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_52_10 (hp : 10 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 10 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp)) T75_52
      hfix75_52 hinj75_52 hcardT75_52
      (fun i => conj_mem_of_fixedPoints _ _ (T75_52 i) (hfix75_52 i) _)
      ⟨75, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 10 hp) Q2.T75_52_2 Q2.hfix75_52_2 Q2.hinj75_52_2
      Q2.hcardT75_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_52_2 i) (Q2.hfix75_52_2 i) _)
      colCert_75_52_10.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_52_15 (hp : 15 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 15 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp)) T75_52
      hfix75_52 hinj75_52 hcardT75_52
      (fun i => conj_mem_of_fixedPoints _ _ (T75_52 i) (hfix75_52 i) _)
      ⟨75, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 15 hp) Q2.T75_52_2 Q2.hfix75_52_2 Q2.hinj75_52_2
      Q2.hcardT75_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_52_2 i) (Q2.hfix75_52_2 i) _)
      colCert_75_52_15.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_52_20 (hp : 20 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 20 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp)) T75_52
      hfix75_52 hinj75_52 hcardT75_52
      (fun i => conj_mem_of_fixedPoints _ _ (T75_52 i) (hfix75_52 i) _)
      ⟨75, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 20 hp) Q2.T75_52_2 Q2.hfix75_52_2 Q2.hinj75_52_2
      Q2.hcardT75_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_52_2 i) (Q2.hfix75_52_2 i) _)
      colCert_75_52_20.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_75_0 (hp : 0 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 0 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 0 (transLenTr ⟨75, by decide⟩ 0 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 0 (transLenTr ⟨75, by decide⟩ 0 hp)) T75_75
      hfix75_75 hinj75_75 hcardT75_75
      (fun i => conj_mem_of_fixedPoints _ _ (T75_75 i) (hfix75_75 i) _)
      ⟨75, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 0 hp) Q2.T75_75_2 Q2.hfix75_75_2 Q2.hinj75_75_2
      Q2.hcardT75_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_75_2 i) (Q2.hfix75_75_2 i) _)
      colCert_75_75_0.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_75_1 (hp : 1 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 1 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 1 (transLenTr ⟨75, by decide⟩ 1 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 1 (transLenTr ⟨75, by decide⟩ 1 hp)) T75_75
      hfix75_75 hinj75_75 hcardT75_75
      (fun i => conj_mem_of_fixedPoints _ _ (T75_75 i) (hfix75_75 i) _)
      ⟨75, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 1 hp) Q2.T75_75_2 Q2.hfix75_75_2 Q2.hinj75_75_2
      Q2.hcardT75_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_75_2 i) (Q2.hfix75_75_2 i) _)
      colCert_75_75_1.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_75_2 (hp : 2 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 2 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 2 (transLenTr ⟨75, by decide⟩ 2 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 2 (transLenTr ⟨75, by decide⟩ 2 hp)) T75_75
      hfix75_75 hinj75_75 hcardT75_75
      (fun i => conj_mem_of_fixedPoints _ _ (T75_75 i) (hfix75_75 i) _)
      ⟨75, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 2 hp) Q2.T75_75_2 Q2.hfix75_75_2 Q2.hinj75_75_2
      Q2.hcardT75_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_75_2 i) (Q2.hfix75_75_2 i) _)
      colCert_75_75_2.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_75_3 (hp : 3 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 3 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 3 (transLenTr ⟨75, by decide⟩ 3 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 3 (transLenTr ⟨75, by decide⟩ 3 hp)) T75_75
      hfix75_75 hinj75_75 hcardT75_75
      (fun i => conj_mem_of_fixedPoints _ _ (T75_75 i) (hfix75_75 i) _)
      ⟨75, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 3 hp) Q2.T75_75_2 Q2.hfix75_75_2 Q2.hinj75_75_2
      Q2.hcardT75_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_75_2 i) (Q2.hfix75_75_2 i) _)
      colCert_75_75_3.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_75_4 (hp : 4 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 4 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 4 (transLenTr ⟨75, by decide⟩ 4 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 4 (transLenTr ⟨75, by decide⟩ 4 hp)) T75_75
      hfix75_75 hinj75_75 hcardT75_75
      (fun i => conj_mem_of_fixedPoints _ _ (T75_75 i) (hfix75_75 i) _)
      ⟨75, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 4 hp) Q2.T75_75_2 Q2.hfix75_75_2 Q2.hinj75_75_2
      Q2.hcardT75_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_75_2 i) (Q2.hfix75_75_2 i) _)
      colCert_75_75_4.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_75_5 (hp : 5 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 5 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 5 (transLenTr ⟨75, by decide⟩ 5 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 5 (transLenTr ⟨75, by decide⟩ 5 hp)) T75_75
      hfix75_75 hinj75_75 hcardT75_75
      (fun i => conj_mem_of_fixedPoints _ _ (T75_75 i) (hfix75_75 i) _)
      ⟨75, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 5 hp) Q2.T75_75_2 Q2.hfix75_75_2 Q2.hinj75_75_2
      Q2.hcardT75_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_75_2 i) (Q2.hfix75_75_2 i) _)
      colCert_75_75_5.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_75_6 (hp : 6 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 6 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 6 (transLenTr ⟨75, by decide⟩ 6 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 6 (transLenTr ⟨75, by decide⟩ 6 hp)) T75_75
      hfix75_75 hinj75_75 hcardT75_75
      (fun i => conj_mem_of_fixedPoints _ _ (T75_75 i) (hfix75_75 i) _)
      ⟨75, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 6 hp) Q2.T75_75_2 Q2.hfix75_75_2 Q2.hinj75_75_2
      Q2.hcardT75_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_75_2 i) (Q2.hfix75_75_2 i) _)
      colCert_75_75_6.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_75_7 (hp : 7 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 7 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 7 (transLenTr ⟨75, by decide⟩ 7 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 7 (transLenTr ⟨75, by decide⟩ 7 hp)) T75_75
      hfix75_75 hinj75_75 hcardT75_75
      (fun i => conj_mem_of_fixedPoints _ _ (T75_75 i) (hfix75_75 i) _)
      ⟨75, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 7 hp) Q2.T75_75_2 Q2.hfix75_75_2 Q2.hinj75_75_2
      Q2.hcardT75_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_75_2 i) (Q2.hfix75_75_2 i) _)
      colCert_75_75_7.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_75_8 (hp : 8 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 8 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 8 (transLenTr ⟨75, by decide⟩ 8 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 8 (transLenTr ⟨75, by decide⟩ 8 hp)) T75_75
      hfix75_75 hinj75_75 hcardT75_75
      (fun i => conj_mem_of_fixedPoints _ _ (T75_75 i) (hfix75_75 i) _)
      ⟨75, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 8 hp) Q2.T75_75_2 Q2.hfix75_75_2 Q2.hinj75_75_2
      Q2.hcardT75_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_75_2 i) (Q2.hfix75_75_2 i) _)
      colCert_75_75_8.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_75_9 (hp : 9 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 9 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 9 (transLenTr ⟨75, by decide⟩ 9 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 9 (transLenTr ⟨75, by decide⟩ 9 hp)) T75_75
      hfix75_75 hinj75_75 hcardT75_75
      (fun i => conj_mem_of_fixedPoints _ _ (T75_75 i) (hfix75_75 i) _)
      ⟨75, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 9 hp) Q2.T75_75_2 Q2.hfix75_75_2 Q2.hinj75_75_2
      Q2.hcardT75_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_75_2 i) (Q2.hfix75_75_2 i) _)
      colCert_75_75_9.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_75_10 (hp : 10 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 10 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 10 (transLenTr ⟨75, by decide⟩ 10 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 10 (transLenTr ⟨75, by decide⟩ 10 hp)) T75_75
      hfix75_75 hinj75_75 hcardT75_75
      (fun i => conj_mem_of_fixedPoints _ _ (T75_75 i) (hfix75_75 i) _)
      ⟨75, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 10 hp) Q2.T75_75_2 Q2.hfix75_75_2 Q2.hinj75_75_2
      Q2.hcardT75_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_75_2 i) (Q2.hfix75_75_2 i) _)
      colCert_75_75_10.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_75_11 (hp : 11 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 11 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 11 (transLenTr ⟨75, by decide⟩ 11 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 11 (transLenTr ⟨75, by decide⟩ 11 hp)) T75_75
      hfix75_75 hinj75_75 hcardT75_75
      (fun i => conj_mem_of_fixedPoints _ _ (T75_75 i) (hfix75_75 i) _)
      ⟨75, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 11 hp) Q2.T75_75_2 Q2.hfix75_75_2 Q2.hinj75_75_2
      Q2.hcardT75_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_75_2 i) (Q2.hfix75_75_2 i) _)
      colCert_75_75_11.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_75_12 (hp : 12 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 12 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 12 (transLenTr ⟨75, by decide⟩ 12 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 12 (transLenTr ⟨75, by decide⟩ 12 hp)) T75_75
      hfix75_75 hinj75_75 hcardT75_75
      (fun i => conj_mem_of_fixedPoints _ _ (T75_75 i) (hfix75_75 i) _)
      ⟨75, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 12 hp) Q2.T75_75_2 Q2.hfix75_75_2 Q2.hinj75_75_2
      Q2.hcardT75_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_75_2 i) (Q2.hfix75_75_2 i) _)
      colCert_75_75_12.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_75_13 (hp : 13 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 13 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 13 (transLenTr ⟨75, by decide⟩ 13 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 13 (transLenTr ⟨75, by decide⟩ 13 hp)) T75_75
      hfix75_75 hinj75_75 hcardT75_75
      (fun i => conj_mem_of_fixedPoints _ _ (T75_75 i) (hfix75_75 i) _)
      ⟨75, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 13 hp) Q2.T75_75_2 Q2.hfix75_75_2 Q2.hinj75_75_2
      Q2.hcardT75_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_75_2 i) (Q2.hfix75_75_2 i) _)
      colCert_75_75_13.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_75_14 (hp : 14 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 14 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 14 (transLenTr ⟨75, by decide⟩ 14 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 14 (transLenTr ⟨75, by decide⟩ 14 hp)) T75_75
      hfix75_75 hinj75_75 hcardT75_75
      (fun i => conj_mem_of_fixedPoints _ _ (T75_75 i) (hfix75_75 i) _)
      ⟨75, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 14 hp) Q2.T75_75_2 Q2.hfix75_75_2 Q2.hinj75_75_2
      Q2.hcardT75_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_75_2 i) (Q2.hfix75_75_2 i) _)
      colCert_75_75_14.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_75_15 (hp : 15 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 15 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 15 (transLenTr ⟨75, by decide⟩ 15 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 15 (transLenTr ⟨75, by decide⟩ 15 hp)) T75_75
      hfix75_75 hinj75_75 hcardT75_75
      (fun i => conj_mem_of_fixedPoints _ _ (T75_75 i) (hfix75_75 i) _)
      ⟨75, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 15 hp) Q2.T75_75_2 Q2.hfix75_75_2 Q2.hinj75_75_2
      Q2.hcardT75_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_75_2 i) (Q2.hfix75_75_2 i) _)
      colCert_75_75_15.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_75_16 (hp : 16 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 16 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 16 (transLenTr ⟨75, by decide⟩ 16 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 16 (transLenTr ⟨75, by decide⟩ 16 hp)) T75_75
      hfix75_75 hinj75_75 hcardT75_75
      (fun i => conj_mem_of_fixedPoints _ _ (T75_75 i) (hfix75_75 i) _)
      ⟨75, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 16 hp) Q2.T75_75_2 Q2.hfix75_75_2 Q2.hinj75_75_2
      Q2.hcardT75_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_75_2 i) (Q2.hfix75_75_2 i) _)
      colCert_75_75_16.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_75_17 (hp : 17 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 17 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 17 (transLenTr ⟨75, by decide⟩ 17 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 17 (transLenTr ⟨75, by decide⟩ 17 hp)) T75_75
      hfix75_75 hinj75_75 hcardT75_75
      (fun i => conj_mem_of_fixedPoints _ _ (T75_75 i) (hfix75_75 i) _)
      ⟨75, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 17 hp) Q2.T75_75_2 Q2.hfix75_75_2 Q2.hinj75_75_2
      Q2.hcardT75_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_75_2 i) (Q2.hfix75_75_2 i) _)
      colCert_75_75_17.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_75_18 (hp : 18 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 18 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 18 (transLenTr ⟨75, by decide⟩ 18 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 18 (transLenTr ⟨75, by decide⟩ 18 hp)) T75_75
      hfix75_75 hinj75_75 hcardT75_75
      (fun i => conj_mem_of_fixedPoints _ _ (T75_75 i) (hfix75_75 i) _)
      ⟨75, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 18 hp) Q2.T75_75_2 Q2.hfix75_75_2 Q2.hinj75_75_2
      Q2.hcardT75_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_75_2 i) (Q2.hfix75_75_2 i) _)
      colCert_75_75_18.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_75_19 (hp : 19 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 19 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 19 (transLenTr ⟨75, by decide⟩ 19 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 19 (transLenTr ⟨75, by decide⟩ 19 hp)) T75_75
      hfix75_75 hinj75_75 hcardT75_75
      (fun i => conj_mem_of_fixedPoints _ _ (T75_75 i) (hfix75_75 i) _)
      ⟨75, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 19 hp) Q2.T75_75_2 Q2.hfix75_75_2 Q2.hinj75_75_2
      Q2.hcardT75_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_75_2 i) (Q2.hfix75_75_2 i) _)
      colCert_75_75_19.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_75_20 (hp : 20 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 20 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 20 (transLenTr ⟨75, by decide⟩ 20 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 20 (transLenTr ⟨75, by decide⟩ 20 hp)) T75_75
      hfix75_75 hinj75_75 hcardT75_75
      (fun i => conj_mem_of_fixedPoints _ _ (T75_75 i) (hfix75_75 i) _)
      ⟨75, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 20 hp) Q2.T75_75_2 Q2.hfix75_75_2 Q2.hinj75_75_2
      Q2.hcardT75_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_75_2 i) (Q2.hfix75_75_2 i) _)
      colCert_75_75_20.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_75_21 (hp : 21 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 21 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 21 (transLenTr ⟨75, by decide⟩ 21 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 21 (transLenTr ⟨75, by decide⟩ 21 hp)) T75_75
      hfix75_75 hinj75_75 hcardT75_75
      (fun i => conj_mem_of_fixedPoints _ _ (T75_75 i) (hfix75_75 i) _)
      ⟨75, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 21 hp) Q2.T75_75_2 Q2.hfix75_75_2 Q2.hinj75_75_2
      Q2.hcardT75_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_75_2 i) (Q2.hfix75_75_2 i) _)
      colCert_75_75_21.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_75_22 (hp : 22 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 22 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 22 (transLenTr ⟨75, by decide⟩ 22 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 22 (transLenTr ⟨75, by decide⟩ 22 hp)) T75_75
      hfix75_75 hinj75_75 hcardT75_75
      (fun i => conj_mem_of_fixedPoints _ _ (T75_75 i) (hfix75_75 i) _)
      ⟨75, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 22 hp) Q2.T75_75_2 Q2.hfix75_75_2 Q2.hinj75_75_2
      Q2.hcardT75_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_75_2 i) (Q2.hfix75_75_2 i) _)
      colCert_75_75_22.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_75_23 (hp : 23 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 23 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 23 (transLenTr ⟨75, by decide⟩ 23 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 23 (transLenTr ⟨75, by decide⟩ 23 hp)) T75_75
      hfix75_75 hinj75_75 hcardT75_75
      (fun i => conj_mem_of_fixedPoints _ _ (T75_75 i) (hfix75_75 i) _)
      ⟨75, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 23 hp) Q2.T75_75_2 Q2.hfix75_75_2 Q2.hinj75_75_2
      Q2.hcardT75_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_75_2 i) (Q2.hfix75_75_2 i) _)
      colCert_75_75_23.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_75_75_24 (hp : 24 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 24 hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 24 (transLenTr ⟨75, by decide⟩ 24 hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨75, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨75, by decide⟩ (listedAt ⟨75, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 24 (transLenTr ⟨75, by decide⟩ 24 hp)) T75_75
      hfix75_75 hinj75_75 hcardT75_75
      (fun i => conj_mem_of_fixedPoints _ _ (T75_75 i) (hfix75_75 i) _)
      ⟨75, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨75, by decide⟩ (Q2.listedAt ⟨75, by decide⟩
        (alnCheck_rep ⟨75, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 24 hp) Q2.T75_75_2 Q2.hfix75_75_2 Q2.hinj75_75_2
      Q2.hcardT75_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T75_75_2 i) (Q2.hfix75_75_2 i) _)
      colCert_75_75_24.hD ?_).symm
  rw [alnId_75 j hj]


theorem leaf_76_1_0 (hp : 0 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 0 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp)) T76_1
      hfix76_1 hinj76_1 hcardT76_1
      (fun i => conj_mem_of_fixedPoints _ _ (T76_1 i) (hfix76_1 i) _)
      ⟨76, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 0 hp) Q2.T76_1_2 Q2.hfix76_1_2 Q2.hinj76_1_2
      Q2.hcardT76_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_1_2 i) (Q2.hfix76_1_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp) : ↥(reps ⟨1, by decide⟩)) : Coordinate 1)
        T76_1 = colFn colCert_76_1_0.D (m := 25) from colCert_76_1_0.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨1, by decide⟩ 0 hp : ↥(Q2.reps ⟨1, by decide⟩)) : Coordinate 2)
        Q2.T76_1_2 = colFn colCert_76_1_0.D (m := 25) from colCert_76_1_0.bind2]
  exact alnAll_76_1_0 j hj hq

theorem leaf_76_1_1 (hp : 1 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 1 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp)) T76_1
      hfix76_1 hinj76_1 hcardT76_1
      (fun i => conj_mem_of_fixedPoints _ _ (T76_1 i) (hfix76_1 i) _)
      ⟨76, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 1 hp) Q2.T76_1_2 Q2.hfix76_1_2 Q2.hinj76_1_2
      Q2.hcardT76_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_1_2 i) (Q2.hfix76_1_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp) : ↥(reps ⟨1, by decide⟩)) : Coordinate 1)
        T76_1 = colFn colCert_76_1_1.D (m := 25) from colCert_76_1_1.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨1, by decide⟩ 1 hp : ↥(Q2.reps ⟨1, by decide⟩)) : Coordinate 2)
        Q2.T76_1_2 = colFn colCert_76_1_1.D (m := 25) from colCert_76_1_1.bind2]
  exact alnAll_76_1_1 j hj hq

theorem leaf_76_1_2 (hp : 2 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 2 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp)) T76_1
      hfix76_1 hinj76_1 hcardT76_1
      (fun i => conj_mem_of_fixedPoints _ _ (T76_1 i) (hfix76_1 i) _)
      ⟨76, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 2 hp) Q2.T76_1_2 Q2.hfix76_1_2 Q2.hinj76_1_2
      Q2.hcardT76_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_1_2 i) (Q2.hfix76_1_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp) : ↥(reps ⟨1, by decide⟩)) : Coordinate 1)
        T76_1 = colFn colCert_76_1_2.D (m := 25) from colCert_76_1_2.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨1, by decide⟩ 2 hp : ↥(Q2.reps ⟨1, by decide⟩)) : Coordinate 2)
        Q2.T76_1_2 = colFn colCert_76_1_2.D (m := 25) from colCert_76_1_2.bind2]
  exact alnAll_76_1_2 j hj hq

theorem leaf_76_1_3 (hp : 3 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 3 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp)) T76_1
      hfix76_1 hinj76_1 hcardT76_1
      (fun i => conj_mem_of_fixedPoints _ _ (T76_1 i) (hfix76_1 i) _)
      ⟨76, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 3 hp) Q2.T76_1_2 Q2.hfix76_1_2 Q2.hinj76_1_2
      Q2.hcardT76_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_1_2 i) (Q2.hfix76_1_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp) : ↥(reps ⟨1, by decide⟩)) : Coordinate 1)
        T76_1 = colFn colCert_76_1_3.D (m := 25) from colCert_76_1_3.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨1, by decide⟩ 3 hp : ↥(Q2.reps ⟨1, by decide⟩)) : Coordinate 2)
        Q2.T76_1_2 = colFn colCert_76_1_3.D (m := 25) from colCert_76_1_3.bind2]
  exact alnAll_76_1_3 j hj hq

theorem leaf_76_1_4 (hp : 4 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 4 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp)) T76_1
      hfix76_1 hinj76_1 hcardT76_1
      (fun i => conj_mem_of_fixedPoints _ _ (T76_1 i) (hfix76_1 i) _)
      ⟨76, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 4 hp) Q2.T76_1_2 Q2.hfix76_1_2 Q2.hinj76_1_2
      Q2.hcardT76_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_1_2 i) (Q2.hfix76_1_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp) : ↥(reps ⟨1, by decide⟩)) : Coordinate 1)
        T76_1 = colFn colCert_76_1_4.D (m := 25) from colCert_76_1_4.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨1, by decide⟩ 4 hp : ↥(Q2.reps ⟨1, by decide⟩)) : Coordinate 2)
        Q2.T76_1_2 = colFn colCert_76_1_4.D (m := 25) from colCert_76_1_4.bind2]
  exact alnAll_76_1_4 j hj hq

theorem leaf_76_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T76_12
      hfix76_12 hinj76_12 hcardT76_12
      (fun i => conj_mem_of_fixedPoints _ _ (T76_12 i) (hfix76_12 i) _)
      ⟨76, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T76_12_2 Q2.hfix76_12_2 Q2.hinj76_12_2
      Q2.hcardT76_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_12_2 i) (Q2.hfix76_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T76_12 = colFn colCert_76_12_0.D (m := 25) from colCert_76_12_0.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T76_12_2 = colFn colCert_76_12_0.D (m := 25) from colCert_76_12_0.bind2]
  exact alnAll_76_12_0 j hj hq

theorem leaf_76_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T76_12
      hfix76_12 hinj76_12 hcardT76_12
      (fun i => conj_mem_of_fixedPoints _ _ (T76_12 i) (hfix76_12 i) _)
      ⟨76, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T76_12_2 Q2.hfix76_12_2 Q2.hinj76_12_2
      Q2.hcardT76_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_12_2 i) (Q2.hfix76_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T76_12 = colFn colCert_76_12_1.D (m := 25) from colCert_76_12_1.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T76_12_2 = colFn colCert_76_12_1.D (m := 25) from colCert_76_12_1.bind2]
  exact alnAll_76_12_1 j hj hq

theorem leaf_76_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T76_12
      hfix76_12 hinj76_12 hcardT76_12
      (fun i => conj_mem_of_fixedPoints _ _ (T76_12 i) (hfix76_12 i) _)
      ⟨76, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T76_12_2 Q2.hfix76_12_2 Q2.hinj76_12_2
      Q2.hcardT76_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_12_2 i) (Q2.hfix76_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T76_12 = colFn colCert_76_12_2.D (m := 25) from colCert_76_12_2.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T76_12_2 = colFn colCert_76_12_2.D (m := 25) from colCert_76_12_2.bind2]
  exact alnAll_76_12_2 j hj hq

theorem leaf_76_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T76_12
      hfix76_12 hinj76_12 hcardT76_12
      (fun i => conj_mem_of_fixedPoints _ _ (T76_12 i) (hfix76_12 i) _)
      ⟨76, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T76_12_2 Q2.hfix76_12_2 Q2.hinj76_12_2
      Q2.hcardT76_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_12_2 i) (Q2.hfix76_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T76_12 = colFn colCert_76_12_3.D (m := 25) from colCert_76_12_3.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T76_12_2 = colFn colCert_76_12_3.D (m := 25) from colCert_76_12_3.bind2]
  exact alnAll_76_12_3 j hj hq

theorem leaf_76_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T76_12
      hfix76_12 hinj76_12 hcardT76_12
      (fun i => conj_mem_of_fixedPoints _ _ (T76_12 i) (hfix76_12 i) _)
      ⟨76, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T76_12_2 Q2.hfix76_12_2 Q2.hinj76_12_2
      Q2.hcardT76_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_12_2 i) (Q2.hfix76_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T76_12 = colFn colCert_76_12_4.D (m := 25) from colCert_76_12_4.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T76_12_2 = colFn colCert_76_12_4.D (m := 25) from colCert_76_12_4.bind2]
  exact alnAll_76_12_4 j hj hq

theorem leaf_76_19_0 (hp : 0 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 0 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp)) T76_19
      hfix76_19 hinj76_19 hcardT76_19
      (fun i => conj_mem_of_fixedPoints _ _ (T76_19 i) (hfix76_19 i) _)
      ⟨76, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 0 hp) Q2.T76_19_2 Q2.hfix76_19_2 Q2.hinj76_19_2
      Q2.hcardT76_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_19_2 i) (Q2.hfix76_19_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp) : ↥(reps ⟨19, by decide⟩)) : Coordinate 1)
        T76_19 = colFn colCert_76_19_0.D (m := 25) from colCert_76_19_0.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨19, by decide⟩ 0 hp : ↥(Q2.reps ⟨19, by decide⟩)) : Coordinate 2)
        Q2.T76_19_2 = colFn colCert_76_19_0.D (m := 25) from colCert_76_19_0.bind2]
  exact alnAll_76_19_0 j hj hq

theorem leaf_76_19_1 (hp : 1 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 1 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp)) T76_19
      hfix76_19 hinj76_19 hcardT76_19
      (fun i => conj_mem_of_fixedPoints _ _ (T76_19 i) (hfix76_19 i) _)
      ⟨76, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 1 hp) Q2.T76_19_2 Q2.hfix76_19_2 Q2.hinj76_19_2
      Q2.hcardT76_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_19_2 i) (Q2.hfix76_19_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp) : ↥(reps ⟨19, by decide⟩)) : Coordinate 1)
        T76_19 = colFn colCert_76_19_1.D (m := 25) from colCert_76_19_1.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨19, by decide⟩ 1 hp : ↥(Q2.reps ⟨19, by decide⟩)) : Coordinate 2)
        Q2.T76_19_2 = colFn colCert_76_19_1.D (m := 25) from colCert_76_19_1.bind2]
  exact alnAll_76_19_1 j hj hq

theorem leaf_76_19_2 (hp : 2 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 2 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp)) T76_19
      hfix76_19 hinj76_19 hcardT76_19
      (fun i => conj_mem_of_fixedPoints _ _ (T76_19 i) (hfix76_19 i) _)
      ⟨76, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 2 hp) Q2.T76_19_2 Q2.hfix76_19_2 Q2.hinj76_19_2
      Q2.hcardT76_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_19_2 i) (Q2.hfix76_19_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp) : ↥(reps ⟨19, by decide⟩)) : Coordinate 1)
        T76_19 = colFn colCert_76_19_2.D (m := 25) from colCert_76_19_2.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨19, by decide⟩ 2 hp : ↥(Q2.reps ⟨19, by decide⟩)) : Coordinate 2)
        Q2.T76_19_2 = colFn colCert_76_19_2.D (m := 25) from colCert_76_19_2.bind2]
  exact alnAll_76_19_2 j hj hq

theorem leaf_76_19_3 (hp : 3 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 3 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp)) T76_19
      hfix76_19 hinj76_19 hcardT76_19
      (fun i => conj_mem_of_fixedPoints _ _ (T76_19 i) (hfix76_19 i) _)
      ⟨76, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 3 hp) Q2.T76_19_2 Q2.hfix76_19_2 Q2.hinj76_19_2
      Q2.hcardT76_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_19_2 i) (Q2.hfix76_19_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp) : ↥(reps ⟨19, by decide⟩)) : Coordinate 1)
        T76_19 = colFn colCert_76_19_3.D (m := 25) from colCert_76_19_3.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨19, by decide⟩ 3 hp : ↥(Q2.reps ⟨19, by decide⟩)) : Coordinate 2)
        Q2.T76_19_2 = colFn colCert_76_19_3.D (m := 25) from colCert_76_19_3.bind2]
  exact alnAll_76_19_3 j hj hq

theorem leaf_76_19_4 (hp : 4 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 4 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp)) T76_19
      hfix76_19 hinj76_19 hcardT76_19
      (fun i => conj_mem_of_fixedPoints _ _ (T76_19 i) (hfix76_19 i) _)
      ⟨76, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 4 hp) Q2.T76_19_2 Q2.hfix76_19_2 Q2.hinj76_19_2
      Q2.hcardT76_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_19_2 i) (Q2.hfix76_19_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp) : ↥(reps ⟨19, by decide⟩)) : Coordinate 1)
        T76_19 = colFn colCert_76_19_4.D (m := 25) from colCert_76_19_4.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨19, by decide⟩ 4 hp : ↥(Q2.reps ⟨19, by decide⟩)) : Coordinate 2)
        Q2.T76_19_2 = colFn colCert_76_19_4.D (m := 25) from colCert_76_19_4.bind2]
  exact alnAll_76_19_4 j hj hq

theorem leaf_76_19_5 (hp : 5 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 5 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp)) T76_19
      hfix76_19 hinj76_19 hcardT76_19
      (fun i => conj_mem_of_fixedPoints _ _ (T76_19 i) (hfix76_19 i) _)
      ⟨76, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 5 hp) Q2.T76_19_2 Q2.hfix76_19_2 Q2.hinj76_19_2
      Q2.hcardT76_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_19_2 i) (Q2.hfix76_19_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp) : ↥(reps ⟨19, by decide⟩)) : Coordinate 1)
        T76_19 = colFn colCert_76_19_5.D (m := 25) from colCert_76_19_5.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨19, by decide⟩ 5 hp : ↥(Q2.reps ⟨19, by decide⟩)) : Coordinate 2)
        Q2.T76_19_2 = colFn colCert_76_19_5.D (m := 25) from colCert_76_19_5.bind2]
  exact alnAll_76_19_5 j hj hq

theorem leaf_76_19_10 (hp : 10 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 10 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp)) T76_19
      hfix76_19 hinj76_19 hcardT76_19
      (fun i => conj_mem_of_fixedPoints _ _ (T76_19 i) (hfix76_19 i) _)
      ⟨76, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 10 hp) Q2.T76_19_2 Q2.hfix76_19_2 Q2.hinj76_19_2
      Q2.hcardT76_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_19_2 i) (Q2.hfix76_19_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp) : ↥(reps ⟨19, by decide⟩)) : Coordinate 1)
        T76_19 = colFn colCert_76_19_10.D (m := 25) from colCert_76_19_10.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨19, by decide⟩ 10 hp : ↥(Q2.reps ⟨19, by decide⟩)) : Coordinate 2)
        Q2.T76_19_2 = colFn colCert_76_19_10.D (m := 25) from colCert_76_19_10.bind2]
  exact alnAll_76_19_10 j hj hq

theorem leaf_76_19_15 (hp : 15 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 15 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp)) T76_19
      hfix76_19 hinj76_19 hcardT76_19
      (fun i => conj_mem_of_fixedPoints _ _ (T76_19 i) (hfix76_19 i) _)
      ⟨76, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 15 hp) Q2.T76_19_2 Q2.hfix76_19_2 Q2.hinj76_19_2
      Q2.hcardT76_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_19_2 i) (Q2.hfix76_19_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp) : ↥(reps ⟨19, by decide⟩)) : Coordinate 1)
        T76_19 = colFn colCert_76_19_15.D (m := 25) from colCert_76_19_15.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨19, by decide⟩ 15 hp : ↥(Q2.reps ⟨19, by decide⟩)) : Coordinate 2)
        Q2.T76_19_2 = colFn colCert_76_19_15.D (m := 25) from colCert_76_19_15.bind2]
  exact alnAll_76_19_15 j hj hq

theorem leaf_76_19_20 (hp : 20 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 20 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp)) T76_19
      hfix76_19 hinj76_19 hcardT76_19
      (fun i => conj_mem_of_fixedPoints _ _ (T76_19 i) (hfix76_19 i) _)
      ⟨76, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 20 hp) Q2.T76_19_2 Q2.hfix76_19_2 Q2.hinj76_19_2
      Q2.hcardT76_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_19_2 i) (Q2.hfix76_19_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp) : ↥(reps ⟨19, by decide⟩)) : Coordinate 1)
        T76_19 = colFn colCert_76_19_20.D (m := 25) from colCert_76_19_20.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨19, by decide⟩ 20 hp : ↥(Q2.reps ⟨19, by decide⟩)) : Coordinate 2)
        Q2.T76_19_2 = colFn colCert_76_19_20.D (m := 25) from colCert_76_19_20.bind2]
  exact alnAll_76_19_20 j hj hq

theorem leaf_76_32_0 (hp : 0 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 0 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp)) T76_32
      hfix76_32 hinj76_32 hcardT76_32
      (fun i => conj_mem_of_fixedPoints _ _ (T76_32 i) (hfix76_32 i) _)
      ⟨76, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 0 hp) Q2.T76_32_2 Q2.hfix76_32_2 Q2.hinj76_32_2
      Q2.hcardT76_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_32_2 i) (Q2.hfix76_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T76_32 = colFn colCert_76_32_0.D (m := 5) from colCert_76_32_0.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 0 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T76_32_2 = colFn colCert_76_32_0.D (m := 5) from colCert_76_32_0.bind2]
  exact alnAll_76_32_0 j hj hq

theorem leaf_76_32_1 (hp : 1 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 1 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp)) T76_32
      hfix76_32 hinj76_32 hcardT76_32
      (fun i => conj_mem_of_fixedPoints _ _ (T76_32 i) (hfix76_32 i) _)
      ⟨76, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 1 hp) Q2.T76_32_2 Q2.hfix76_32_2 Q2.hinj76_32_2
      Q2.hcardT76_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_32_2 i) (Q2.hfix76_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T76_32 = colFn colCert_76_32_1.D (m := 5) from colCert_76_32_1.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 1 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T76_32_2 = colFn colCert_76_32_1.D (m := 5) from colCert_76_32_1.bind2]
  exact alnAll_76_32_1 j hj hq

theorem leaf_76_32_2 (hp : 2 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 2 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp)) T76_32
      hfix76_32 hinj76_32 hcardT76_32
      (fun i => conj_mem_of_fixedPoints _ _ (T76_32 i) (hfix76_32 i) _)
      ⟨76, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 2 hp) Q2.T76_32_2 Q2.hfix76_32_2 Q2.hinj76_32_2
      Q2.hcardT76_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_32_2 i) (Q2.hfix76_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T76_32 = colFn colCert_76_32_2.D (m := 5) from colCert_76_32_2.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 2 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T76_32_2 = colFn colCert_76_32_2.D (m := 5) from colCert_76_32_2.bind2]
  exact alnAll_76_32_2 j hj hq

theorem leaf_76_32_3 (hp : 3 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 3 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp)) T76_32
      hfix76_32 hinj76_32 hcardT76_32
      (fun i => conj_mem_of_fixedPoints _ _ (T76_32 i) (hfix76_32 i) _)
      ⟨76, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 3 hp) Q2.T76_32_2 Q2.hfix76_32_2 Q2.hinj76_32_2
      Q2.hcardT76_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_32_2 i) (Q2.hfix76_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T76_32 = colFn colCert_76_32_3.D (m := 5) from colCert_76_32_3.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 3 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T76_32_2 = colFn colCert_76_32_3.D (m := 5) from colCert_76_32_3.bind2]
  exact alnAll_76_32_3 j hj hq

theorem leaf_76_32_4 (hp : 4 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 4 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp)) T76_32
      hfix76_32 hinj76_32 hcardT76_32
      (fun i => conj_mem_of_fixedPoints _ _ (T76_32 i) (hfix76_32 i) _)
      ⟨76, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 4 hp) Q2.T76_32_2 Q2.hfix76_32_2 Q2.hinj76_32_2
      Q2.hcardT76_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_32_2 i) (Q2.hfix76_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T76_32 = colFn colCert_76_32_4.D (m := 5) from colCert_76_32_4.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 4 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T76_32_2 = colFn colCert_76_32_4.D (m := 5) from colCert_76_32_4.bind2]
  exact alnAll_76_32_4 j hj hq

theorem leaf_76_32_5 (hp : 5 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 5 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp)) T76_32
      hfix76_32 hinj76_32 hcardT76_32
      (fun i => conj_mem_of_fixedPoints _ _ (T76_32 i) (hfix76_32 i) _)
      ⟨76, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 5 hp) Q2.T76_32_2 Q2.hfix76_32_2 Q2.hinj76_32_2
      Q2.hcardT76_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_32_2 i) (Q2.hfix76_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T76_32 = colFn colCert_76_32_5.D (m := 5) from colCert_76_32_5.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 5 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T76_32_2 = colFn colCert_76_32_5.D (m := 5) from colCert_76_32_5.bind2]
  exact alnAll_76_32_5 j hj hq

theorem leaf_76_32_10 (hp : 10 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 10 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp)) T76_32
      hfix76_32 hinj76_32 hcardT76_32
      (fun i => conj_mem_of_fixedPoints _ _ (T76_32 i) (hfix76_32 i) _)
      ⟨76, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 10 hp) Q2.T76_32_2 Q2.hfix76_32_2 Q2.hinj76_32_2
      Q2.hcardT76_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_32_2 i) (Q2.hfix76_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T76_32 = colFn colCert_76_32_10.D (m := 5) from colCert_76_32_10.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 10 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T76_32_2 = colFn colCert_76_32_10.D (m := 5) from colCert_76_32_10.bind2]
  exact alnAll_76_32_10 j hj hq

theorem leaf_76_32_15 (hp : 15 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 15 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp)) T76_32
      hfix76_32 hinj76_32 hcardT76_32
      (fun i => conj_mem_of_fixedPoints _ _ (T76_32 i) (hfix76_32 i) _)
      ⟨76, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 15 hp) Q2.T76_32_2 Q2.hfix76_32_2 Q2.hinj76_32_2
      Q2.hcardT76_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_32_2 i) (Q2.hfix76_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T76_32 = colFn colCert_76_32_15.D (m := 5) from colCert_76_32_15.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 15 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T76_32_2 = colFn colCert_76_32_15.D (m := 5) from colCert_76_32_15.bind2]
  exact alnAll_76_32_15 j hj hq

theorem leaf_76_32_20 (hp : 20 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 20 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp)) T76_32
      hfix76_32 hinj76_32 hcardT76_32
      (fun i => conj_mem_of_fixedPoints _ _ (T76_32 i) (hfix76_32 i) _)
      ⟨76, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 20 hp) Q2.T76_32_2 Q2.hfix76_32_2 Q2.hinj76_32_2
      Q2.hcardT76_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_32_2 i) (Q2.hfix76_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T76_32 = colFn colCert_76_32_20.D (m := 5) from colCert_76_32_20.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 20 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T76_32_2 = colFn colCert_76_32_20.D (m := 5) from colCert_76_32_20.bind2]
  exact alnAll_76_32_20 j hj hq

theorem leaf_76_37_0 (hp : 0 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 0 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp)) T76_37
      hfix76_37 hinj76_37 hcardT76_37
      (fun i => conj_mem_of_fixedPoints _ _ (T76_37 i) (hfix76_37 i) _)
      ⟨76, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 0 hp) Q2.T76_37_2 Q2.hfix76_37_2 Q2.hinj76_37_2
      Q2.hcardT76_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_37_2 i) (Q2.hfix76_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T76_37 = colFn colCert_76_37_0.D (m := 5) from colCert_76_37_0.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 0 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T76_37_2 = colFn colCert_76_37_0.D (m := 5) from colCert_76_37_0.bind2]
  exact alnAll_76_37_0 j hj hq

theorem leaf_76_37_1 (hp : 1 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 1 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp)) T76_37
      hfix76_37 hinj76_37 hcardT76_37
      (fun i => conj_mem_of_fixedPoints _ _ (T76_37 i) (hfix76_37 i) _)
      ⟨76, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 1 hp) Q2.T76_37_2 Q2.hfix76_37_2 Q2.hinj76_37_2
      Q2.hcardT76_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_37_2 i) (Q2.hfix76_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T76_37 = colFn colCert_76_37_1.D (m := 5) from colCert_76_37_1.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 1 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T76_37_2 = colFn colCert_76_37_1.D (m := 5) from colCert_76_37_1.bind2]
  exact alnAll_76_37_1 j hj hq

theorem leaf_76_37_2 (hp : 2 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 2 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp)) T76_37
      hfix76_37 hinj76_37 hcardT76_37
      (fun i => conj_mem_of_fixedPoints _ _ (T76_37 i) (hfix76_37 i) _)
      ⟨76, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 2 hp) Q2.T76_37_2 Q2.hfix76_37_2 Q2.hinj76_37_2
      Q2.hcardT76_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_37_2 i) (Q2.hfix76_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T76_37 = colFn colCert_76_37_2.D (m := 5) from colCert_76_37_2.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 2 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T76_37_2 = colFn colCert_76_37_2.D (m := 5) from colCert_76_37_2.bind2]
  exact alnAll_76_37_2 j hj hq

theorem leaf_76_37_3 (hp : 3 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 3 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp)) T76_37
      hfix76_37 hinj76_37 hcardT76_37
      (fun i => conj_mem_of_fixedPoints _ _ (T76_37 i) (hfix76_37 i) _)
      ⟨76, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 3 hp) Q2.T76_37_2 Q2.hfix76_37_2 Q2.hinj76_37_2
      Q2.hcardT76_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_37_2 i) (Q2.hfix76_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T76_37 = colFn colCert_76_37_3.D (m := 5) from colCert_76_37_3.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 3 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T76_37_2 = colFn colCert_76_37_3.D (m := 5) from colCert_76_37_3.bind2]
  exact alnAll_76_37_3 j hj hq

theorem leaf_76_37_4 (hp : 4 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 4 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp)) T76_37
      hfix76_37 hinj76_37 hcardT76_37
      (fun i => conj_mem_of_fixedPoints _ _ (T76_37 i) (hfix76_37 i) _)
      ⟨76, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 4 hp) Q2.T76_37_2 Q2.hfix76_37_2 Q2.hinj76_37_2
      Q2.hcardT76_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_37_2 i) (Q2.hfix76_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T76_37 = colFn colCert_76_37_4.D (m := 5) from colCert_76_37_4.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 4 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T76_37_2 = colFn colCert_76_37_4.D (m := 5) from colCert_76_37_4.bind2]
  exact alnAll_76_37_4 j hj hq

theorem leaf_76_37_5 (hp : 5 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 5 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp)) T76_37
      hfix76_37 hinj76_37 hcardT76_37
      (fun i => conj_mem_of_fixedPoints _ _ (T76_37 i) (hfix76_37 i) _)
      ⟨76, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 5 hp) Q2.T76_37_2 Q2.hfix76_37_2 Q2.hinj76_37_2
      Q2.hcardT76_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_37_2 i) (Q2.hfix76_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T76_37 = colFn colCert_76_37_5.D (m := 5) from colCert_76_37_5.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 5 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T76_37_2 = colFn colCert_76_37_5.D (m := 5) from colCert_76_37_5.bind2]
  exact alnAll_76_37_5 j hj hq

theorem leaf_76_37_10 (hp : 10 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 10 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp)) T76_37
      hfix76_37 hinj76_37 hcardT76_37
      (fun i => conj_mem_of_fixedPoints _ _ (T76_37 i) (hfix76_37 i) _)
      ⟨76, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 10 hp) Q2.T76_37_2 Q2.hfix76_37_2 Q2.hinj76_37_2
      Q2.hcardT76_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_37_2 i) (Q2.hfix76_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T76_37 = colFn colCert_76_37_10.D (m := 5) from colCert_76_37_10.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 10 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T76_37_2 = colFn colCert_76_37_10.D (m := 5) from colCert_76_37_10.bind2]
  exact alnAll_76_37_10 j hj hq

theorem leaf_76_37_15 (hp : 15 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 15 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp)) T76_37
      hfix76_37 hinj76_37 hcardT76_37
      (fun i => conj_mem_of_fixedPoints _ _ (T76_37 i) (hfix76_37 i) _)
      ⟨76, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 15 hp) Q2.T76_37_2 Q2.hfix76_37_2 Q2.hinj76_37_2
      Q2.hcardT76_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_37_2 i) (Q2.hfix76_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T76_37 = colFn colCert_76_37_15.D (m := 5) from colCert_76_37_15.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 15 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T76_37_2 = colFn colCert_76_37_15.D (m := 5) from colCert_76_37_15.bind2]
  exact alnAll_76_37_15 j hj hq

theorem leaf_76_37_20 (hp : 20 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 20 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp)) T76_37
      hfix76_37 hinj76_37 hcardT76_37
      (fun i => conj_mem_of_fixedPoints _ _ (T76_37 i) (hfix76_37 i) _)
      ⟨76, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 20 hp) Q2.T76_37_2 Q2.hfix76_37_2 Q2.hinj76_37_2
      Q2.hcardT76_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_37_2 i) (Q2.hfix76_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T76_37 = colFn colCert_76_37_20.D (m := 5) from colCert_76_37_20.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 20 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T76_37_2 = colFn colCert_76_37_20.D (m := 5) from colCert_76_37_20.bind2]
  exact alnAll_76_37_20 j hj hq

theorem leaf_76_42_0 (hp : 0 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 0 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp)) T76_42
      hfix76_42 hinj76_42 hcardT76_42
      (fun i => conj_mem_of_fixedPoints _ _ (T76_42 i) (hfix76_42 i) _)
      ⟨76, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 0 hp) Q2.T76_42_2 Q2.hfix76_42_2 Q2.hinj76_42_2
      Q2.hcardT76_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_42_2 i) (Q2.hfix76_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T76_42 = colFn colCert_76_42_0.D (m := 5) from colCert_76_42_0.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 0 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T76_42_2 = colFn colCert_76_42_0.D (m := 5) from colCert_76_42_0.bind2]
  exact alnAll_76_42_0 j hj hq

theorem leaf_76_42_1 (hp : 1 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 1 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp)) T76_42
      hfix76_42 hinj76_42 hcardT76_42
      (fun i => conj_mem_of_fixedPoints _ _ (T76_42 i) (hfix76_42 i) _)
      ⟨76, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 1 hp) Q2.T76_42_2 Q2.hfix76_42_2 Q2.hinj76_42_2
      Q2.hcardT76_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_42_2 i) (Q2.hfix76_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T76_42 = colFn colCert_76_42_1.D (m := 5) from colCert_76_42_1.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 1 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T76_42_2 = colFn colCert_76_42_1.D (m := 5) from colCert_76_42_1.bind2]
  exact alnAll_76_42_1 j hj hq

theorem leaf_76_42_2 (hp : 2 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 2 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp)) T76_42
      hfix76_42 hinj76_42 hcardT76_42
      (fun i => conj_mem_of_fixedPoints _ _ (T76_42 i) (hfix76_42 i) _)
      ⟨76, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 2 hp) Q2.T76_42_2 Q2.hfix76_42_2 Q2.hinj76_42_2
      Q2.hcardT76_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_42_2 i) (Q2.hfix76_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T76_42 = colFn colCert_76_42_2.D (m := 5) from colCert_76_42_2.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 2 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T76_42_2 = colFn colCert_76_42_2.D (m := 5) from colCert_76_42_2.bind2]
  exact alnAll_76_42_2 j hj hq

theorem leaf_76_42_3 (hp : 3 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 3 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp)) T76_42
      hfix76_42 hinj76_42 hcardT76_42
      (fun i => conj_mem_of_fixedPoints _ _ (T76_42 i) (hfix76_42 i) _)
      ⟨76, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 3 hp) Q2.T76_42_2 Q2.hfix76_42_2 Q2.hinj76_42_2
      Q2.hcardT76_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_42_2 i) (Q2.hfix76_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T76_42 = colFn colCert_76_42_3.D (m := 5) from colCert_76_42_3.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 3 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T76_42_2 = colFn colCert_76_42_3.D (m := 5) from colCert_76_42_3.bind2]
  exact alnAll_76_42_3 j hj hq

theorem leaf_76_42_4 (hp : 4 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 4 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp)) T76_42
      hfix76_42 hinj76_42 hcardT76_42
      (fun i => conj_mem_of_fixedPoints _ _ (T76_42 i) (hfix76_42 i) _)
      ⟨76, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 4 hp) Q2.T76_42_2 Q2.hfix76_42_2 Q2.hinj76_42_2
      Q2.hcardT76_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_42_2 i) (Q2.hfix76_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T76_42 = colFn colCert_76_42_4.D (m := 5) from colCert_76_42_4.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 4 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T76_42_2 = colFn colCert_76_42_4.D (m := 5) from colCert_76_42_4.bind2]
  exact alnAll_76_42_4 j hj hq

theorem leaf_76_42_5 (hp : 5 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 5 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp)) T76_42
      hfix76_42 hinj76_42 hcardT76_42
      (fun i => conj_mem_of_fixedPoints _ _ (T76_42 i) (hfix76_42 i) _)
      ⟨76, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 5 hp) Q2.T76_42_2 Q2.hfix76_42_2 Q2.hinj76_42_2
      Q2.hcardT76_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_42_2 i) (Q2.hfix76_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T76_42 = colFn colCert_76_42_5.D (m := 5) from colCert_76_42_5.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 5 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T76_42_2 = colFn colCert_76_42_5.D (m := 5) from colCert_76_42_5.bind2]
  exact alnAll_76_42_5 j hj hq

theorem leaf_76_42_10 (hp : 10 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 10 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp)) T76_42
      hfix76_42 hinj76_42 hcardT76_42
      (fun i => conj_mem_of_fixedPoints _ _ (T76_42 i) (hfix76_42 i) _)
      ⟨76, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 10 hp) Q2.T76_42_2 Q2.hfix76_42_2 Q2.hinj76_42_2
      Q2.hcardT76_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_42_2 i) (Q2.hfix76_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T76_42 = colFn colCert_76_42_10.D (m := 5) from colCert_76_42_10.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 10 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T76_42_2 = colFn colCert_76_42_10.D (m := 5) from colCert_76_42_10.bind2]
  exact alnAll_76_42_10 j hj hq

theorem leaf_76_42_15 (hp : 15 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 15 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp)) T76_42
      hfix76_42 hinj76_42 hcardT76_42
      (fun i => conj_mem_of_fixedPoints _ _ (T76_42 i) (hfix76_42 i) _)
      ⟨76, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 15 hp) Q2.T76_42_2 Q2.hfix76_42_2 Q2.hinj76_42_2
      Q2.hcardT76_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_42_2 i) (Q2.hfix76_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T76_42 = colFn colCert_76_42_15.D (m := 5) from colCert_76_42_15.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 15 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T76_42_2 = colFn colCert_76_42_15.D (m := 5) from colCert_76_42_15.bind2]
  exact alnAll_76_42_15 j hj hq

theorem leaf_76_42_20 (hp : 20 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 20 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp)) T76_42
      hfix76_42 hinj76_42 hcardT76_42
      (fun i => conj_mem_of_fixedPoints _ _ (T76_42 i) (hfix76_42 i) _)
      ⟨76, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 20 hp) Q2.T76_42_2 Q2.hfix76_42_2 Q2.hinj76_42_2
      Q2.hcardT76_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_42_2 i) (Q2.hfix76_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T76_42 = colFn colCert_76_42_20.D (m := 5) from colCert_76_42_20.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 20 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T76_42_2 = colFn colCert_76_42_20.D (m := 5) from colCert_76_42_20.bind2]
  exact alnAll_76_42_20 j hj hq

theorem leaf_76_47_0 (hp : 0 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 0 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp)) T76_47
      hfix76_47 hinj76_47 hcardT76_47
      (fun i => conj_mem_of_fixedPoints _ _ (T76_47 i) (hfix76_47 i) _)
      ⟨76, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 0 hp) Q2.T76_47_2 Q2.hfix76_47_2 Q2.hinj76_47_2
      Q2.hcardT76_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_47_2 i) (Q2.hfix76_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T76_47 = colFn colCert_76_47_0.D (m := 5) from colCert_76_47_0.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 0 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T76_47_2 = colFn colCert_76_47_0.D (m := 5) from colCert_76_47_0.bind2]
  exact alnAll_76_47_0 j hj hq

theorem leaf_76_47_1 (hp : 1 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 1 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp)) T76_47
      hfix76_47 hinj76_47 hcardT76_47
      (fun i => conj_mem_of_fixedPoints _ _ (T76_47 i) (hfix76_47 i) _)
      ⟨76, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 1 hp) Q2.T76_47_2 Q2.hfix76_47_2 Q2.hinj76_47_2
      Q2.hcardT76_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_47_2 i) (Q2.hfix76_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T76_47 = colFn colCert_76_47_1.D (m := 5) from colCert_76_47_1.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 1 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T76_47_2 = colFn colCert_76_47_1.D (m := 5) from colCert_76_47_1.bind2]
  exact alnAll_76_47_1 j hj hq

theorem leaf_76_47_2 (hp : 2 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 2 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp)) T76_47
      hfix76_47 hinj76_47 hcardT76_47
      (fun i => conj_mem_of_fixedPoints _ _ (T76_47 i) (hfix76_47 i) _)
      ⟨76, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 2 hp) Q2.T76_47_2 Q2.hfix76_47_2 Q2.hinj76_47_2
      Q2.hcardT76_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_47_2 i) (Q2.hfix76_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T76_47 = colFn colCert_76_47_2.D (m := 5) from colCert_76_47_2.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 2 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T76_47_2 = colFn colCert_76_47_2.D (m := 5) from colCert_76_47_2.bind2]
  exact alnAll_76_47_2 j hj hq

theorem leaf_76_47_3 (hp : 3 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 3 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp)) T76_47
      hfix76_47 hinj76_47 hcardT76_47
      (fun i => conj_mem_of_fixedPoints _ _ (T76_47 i) (hfix76_47 i) _)
      ⟨76, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 3 hp) Q2.T76_47_2 Q2.hfix76_47_2 Q2.hinj76_47_2
      Q2.hcardT76_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_47_2 i) (Q2.hfix76_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T76_47 = colFn colCert_76_47_3.D (m := 5) from colCert_76_47_3.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 3 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T76_47_2 = colFn colCert_76_47_3.D (m := 5) from colCert_76_47_3.bind2]
  exact alnAll_76_47_3 j hj hq

theorem leaf_76_47_4 (hp : 4 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 4 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp)) T76_47
      hfix76_47 hinj76_47 hcardT76_47
      (fun i => conj_mem_of_fixedPoints _ _ (T76_47 i) (hfix76_47 i) _)
      ⟨76, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 4 hp) Q2.T76_47_2 Q2.hfix76_47_2 Q2.hinj76_47_2
      Q2.hcardT76_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_47_2 i) (Q2.hfix76_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T76_47 = colFn colCert_76_47_4.D (m := 5) from colCert_76_47_4.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 4 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T76_47_2 = colFn colCert_76_47_4.D (m := 5) from colCert_76_47_4.bind2]
  exact alnAll_76_47_4 j hj hq

theorem leaf_76_47_5 (hp : 5 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 5 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp)) T76_47
      hfix76_47 hinj76_47 hcardT76_47
      (fun i => conj_mem_of_fixedPoints _ _ (T76_47 i) (hfix76_47 i) _)
      ⟨76, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 5 hp) Q2.T76_47_2 Q2.hfix76_47_2 Q2.hinj76_47_2
      Q2.hcardT76_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_47_2 i) (Q2.hfix76_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T76_47 = colFn colCert_76_47_5.D (m := 5) from colCert_76_47_5.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 5 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T76_47_2 = colFn colCert_76_47_5.D (m := 5) from colCert_76_47_5.bind2]
  exact alnAll_76_47_5 j hj hq

theorem leaf_76_47_10 (hp : 10 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 10 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp)) T76_47
      hfix76_47 hinj76_47 hcardT76_47
      (fun i => conj_mem_of_fixedPoints _ _ (T76_47 i) (hfix76_47 i) _)
      ⟨76, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 10 hp) Q2.T76_47_2 Q2.hfix76_47_2 Q2.hinj76_47_2
      Q2.hcardT76_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_47_2 i) (Q2.hfix76_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T76_47 = colFn colCert_76_47_10.D (m := 5) from colCert_76_47_10.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 10 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T76_47_2 = colFn colCert_76_47_10.D (m := 5) from colCert_76_47_10.bind2]
  exact alnAll_76_47_10 j hj hq

theorem leaf_76_47_15 (hp : 15 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 15 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp)) T76_47
      hfix76_47 hinj76_47 hcardT76_47
      (fun i => conj_mem_of_fixedPoints _ _ (T76_47 i) (hfix76_47 i) _)
      ⟨76, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 15 hp) Q2.T76_47_2 Q2.hfix76_47_2 Q2.hinj76_47_2
      Q2.hcardT76_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_47_2 i) (Q2.hfix76_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T76_47 = colFn colCert_76_47_15.D (m := 5) from colCert_76_47_15.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 15 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T76_47_2 = colFn colCert_76_47_15.D (m := 5) from colCert_76_47_15.bind2]
  exact alnAll_76_47_15 j hj hq

theorem leaf_76_47_20 (hp : 20 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 20 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp)) T76_47
      hfix76_47 hinj76_47 hcardT76_47
      (fun i => conj_mem_of_fixedPoints _ _ (T76_47 i) (hfix76_47 i) _)
      ⟨76, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 20 hp) Q2.T76_47_2 Q2.hfix76_47_2 Q2.hinj76_47_2
      Q2.hcardT76_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_47_2 i) (Q2.hfix76_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T76_47 = colFn colCert_76_47_20.D (m := 5) from colCert_76_47_20.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 20 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T76_47_2 = colFn colCert_76_47_20.D (m := 5) from colCert_76_47_20.bind2]
  exact alnAll_76_47_20 j hj hq

theorem leaf_76_52_0 (hp : 0 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 0 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp)) T76_52
      hfix76_52 hinj76_52 hcardT76_52
      (fun i => conj_mem_of_fixedPoints _ _ (T76_52 i) (hfix76_52 i) _)
      ⟨76, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 0 hp) Q2.T76_52_2 Q2.hfix76_52_2 Q2.hinj76_52_2
      Q2.hcardT76_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_52_2 i) (Q2.hfix76_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T76_52 = colFn colCert_76_52_0.D (m := 5) from colCert_76_52_0.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 0 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T76_52_2 = colFn colCert_76_52_0.D (m := 5) from colCert_76_52_0.bind2]
  exact alnAll_76_52_0 j hj hq

theorem leaf_76_52_1 (hp : 1 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 1 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp)) T76_52
      hfix76_52 hinj76_52 hcardT76_52
      (fun i => conj_mem_of_fixedPoints _ _ (T76_52 i) (hfix76_52 i) _)
      ⟨76, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 1 hp) Q2.T76_52_2 Q2.hfix76_52_2 Q2.hinj76_52_2
      Q2.hcardT76_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_52_2 i) (Q2.hfix76_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T76_52 = colFn colCert_76_52_1.D (m := 5) from colCert_76_52_1.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 1 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T76_52_2 = colFn colCert_76_52_1.D (m := 5) from colCert_76_52_1.bind2]
  exact alnAll_76_52_1 j hj hq

theorem leaf_76_52_2 (hp : 2 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 2 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp)) T76_52
      hfix76_52 hinj76_52 hcardT76_52
      (fun i => conj_mem_of_fixedPoints _ _ (T76_52 i) (hfix76_52 i) _)
      ⟨76, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 2 hp) Q2.T76_52_2 Q2.hfix76_52_2 Q2.hinj76_52_2
      Q2.hcardT76_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_52_2 i) (Q2.hfix76_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T76_52 = colFn colCert_76_52_2.D (m := 5) from colCert_76_52_2.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 2 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T76_52_2 = colFn colCert_76_52_2.D (m := 5) from colCert_76_52_2.bind2]
  exact alnAll_76_52_2 j hj hq

theorem leaf_76_52_3 (hp : 3 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 3 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp)) T76_52
      hfix76_52 hinj76_52 hcardT76_52
      (fun i => conj_mem_of_fixedPoints _ _ (T76_52 i) (hfix76_52 i) _)
      ⟨76, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 3 hp) Q2.T76_52_2 Q2.hfix76_52_2 Q2.hinj76_52_2
      Q2.hcardT76_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_52_2 i) (Q2.hfix76_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T76_52 = colFn colCert_76_52_3.D (m := 5) from colCert_76_52_3.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 3 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T76_52_2 = colFn colCert_76_52_3.D (m := 5) from colCert_76_52_3.bind2]
  exact alnAll_76_52_3 j hj hq

theorem leaf_76_52_4 (hp : 4 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 4 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp)) T76_52
      hfix76_52 hinj76_52 hcardT76_52
      (fun i => conj_mem_of_fixedPoints _ _ (T76_52 i) (hfix76_52 i) _)
      ⟨76, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 4 hp) Q2.T76_52_2 Q2.hfix76_52_2 Q2.hinj76_52_2
      Q2.hcardT76_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_52_2 i) (Q2.hfix76_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T76_52 = colFn colCert_76_52_4.D (m := 5) from colCert_76_52_4.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 4 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T76_52_2 = colFn colCert_76_52_4.D (m := 5) from colCert_76_52_4.bind2]
  exact alnAll_76_52_4 j hj hq

theorem leaf_76_52_5 (hp : 5 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 5 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp)) T76_52
      hfix76_52 hinj76_52 hcardT76_52
      (fun i => conj_mem_of_fixedPoints _ _ (T76_52 i) (hfix76_52 i) _)
      ⟨76, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 5 hp) Q2.T76_52_2 Q2.hfix76_52_2 Q2.hinj76_52_2
      Q2.hcardT76_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_52_2 i) (Q2.hfix76_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T76_52 = colFn colCert_76_52_5.D (m := 5) from colCert_76_52_5.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 5 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T76_52_2 = colFn colCert_76_52_5.D (m := 5) from colCert_76_52_5.bind2]
  exact alnAll_76_52_5 j hj hq

theorem leaf_76_52_10 (hp : 10 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 10 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp)) T76_52
      hfix76_52 hinj76_52 hcardT76_52
      (fun i => conj_mem_of_fixedPoints _ _ (T76_52 i) (hfix76_52 i) _)
      ⟨76, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 10 hp) Q2.T76_52_2 Q2.hfix76_52_2 Q2.hinj76_52_2
      Q2.hcardT76_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_52_2 i) (Q2.hfix76_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T76_52 = colFn colCert_76_52_10.D (m := 5) from colCert_76_52_10.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 10 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T76_52_2 = colFn colCert_76_52_10.D (m := 5) from colCert_76_52_10.bind2]
  exact alnAll_76_52_10 j hj hq

theorem leaf_76_52_15 (hp : 15 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 15 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp)) T76_52
      hfix76_52 hinj76_52 hcardT76_52
      (fun i => conj_mem_of_fixedPoints _ _ (T76_52 i) (hfix76_52 i) _)
      ⟨76, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 15 hp) Q2.T76_52_2 Q2.hfix76_52_2 Q2.hinj76_52_2
      Q2.hcardT76_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_52_2 i) (Q2.hfix76_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T76_52 = colFn colCert_76_52_15.D (m := 5) from colCert_76_52_15.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 15 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T76_52_2 = colFn colCert_76_52_15.D (m := 5) from colCert_76_52_15.bind2]
  exact alnAll_76_52_15 j hj hq

theorem leaf_76_52_20 (hp : 20 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 20 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp)) T76_52
      hfix76_52 hinj76_52 hcardT76_52
      (fun i => conj_mem_of_fixedPoints _ _ (T76_52 i) (hfix76_52 i) _)
      ⟨76, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 20 hp) Q2.T76_52_2 Q2.hfix76_52_2 Q2.hinj76_52_2
      Q2.hcardT76_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_52_2 i) (Q2.hfix76_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T76_52 = colFn colCert_76_52_20.D (m := 5) from colCert_76_52_20.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 20 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T76_52_2 = colFn colCert_76_52_20.D (m := 5) from colCert_76_52_20.bind2]
  exact alnAll_76_52_20 j hj hq

theorem leaf_76_76_0 (hp : 0 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 0 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 0 (transLenTr ⟨76, by decide⟩ 0 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 0 (transLenTr ⟨76, by decide⟩ 0 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 0 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 0 (transLenTr ⟨76, by decide⟩ 0 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_0.D (m := 5) from colCert_76_76_0.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 0 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_0.D (m := 5) from colCert_76_76_0.bind2]
  exact alnAll_76_76_0 j hj hq

theorem leaf_76_76_1 (hp : 1 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 1 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 1 (transLenTr ⟨76, by decide⟩ 1 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 1 (transLenTr ⟨76, by decide⟩ 1 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 1 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 1 (transLenTr ⟨76, by decide⟩ 1 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_1.D (m := 5) from colCert_76_76_1.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 1 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_1.D (m := 5) from colCert_76_76_1.bind2]
  exact alnAll_76_76_1 j hj hq

theorem leaf_76_76_2 (hp : 2 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 2 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 2 (transLenTr ⟨76, by decide⟩ 2 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 2 (transLenTr ⟨76, by decide⟩ 2 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 2 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 2 (transLenTr ⟨76, by decide⟩ 2 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_2.D (m := 5) from colCert_76_76_2.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 2 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_2.D (m := 5) from colCert_76_76_2.bind2]
  exact alnAll_76_76_2 j hj hq

theorem leaf_76_76_3 (hp : 3 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 3 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 3 (transLenTr ⟨76, by decide⟩ 3 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 3 (transLenTr ⟨76, by decide⟩ 3 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 3 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 3 (transLenTr ⟨76, by decide⟩ 3 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_3.D (m := 5) from colCert_76_76_3.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 3 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_3.D (m := 5) from colCert_76_76_3.bind2]
  exact alnAll_76_76_3 j hj hq

theorem leaf_76_76_4 (hp : 4 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 4 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 4 (transLenTr ⟨76, by decide⟩ 4 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 4 (transLenTr ⟨76, by decide⟩ 4 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 4 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 4 (transLenTr ⟨76, by decide⟩ 4 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_4.D (m := 5) from colCert_76_76_4.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 4 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_4.D (m := 5) from colCert_76_76_4.bind2]
  exact alnAll_76_76_4 j hj hq

theorem leaf_76_76_5 (hp : 5 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 5 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 5 (transLenTr ⟨76, by decide⟩ 5 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 5 (transLenTr ⟨76, by decide⟩ 5 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 5 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 5 (transLenTr ⟨76, by decide⟩ 5 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_5.D (m := 5) from colCert_76_76_5.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 5 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_5.D (m := 5) from colCert_76_76_5.bind2]
  exact alnAll_76_76_5 j hj hq

theorem leaf_76_76_6 (hp : 6 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 6 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 6 (transLenTr ⟨76, by decide⟩ 6 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 6 (transLenTr ⟨76, by decide⟩ 6 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 6 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 6 (transLenTr ⟨76, by decide⟩ 6 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_6.D (m := 5) from colCert_76_76_6.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 6 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_6.D (m := 5) from colCert_76_76_6.bind2]
  exact alnAll_76_76_6 j hj hq

theorem leaf_76_76_7 (hp : 7 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 7 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 7 (transLenTr ⟨76, by decide⟩ 7 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 7 (transLenTr ⟨76, by decide⟩ 7 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 7 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 7 (transLenTr ⟨76, by decide⟩ 7 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_7.D (m := 5) from colCert_76_76_7.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 7 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_7.D (m := 5) from colCert_76_76_7.bind2]
  exact alnAll_76_76_7 j hj hq

theorem leaf_76_76_8 (hp : 8 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 8 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 8 (transLenTr ⟨76, by decide⟩ 8 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 8 (transLenTr ⟨76, by decide⟩ 8 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 8 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 8 (transLenTr ⟨76, by decide⟩ 8 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_8.D (m := 5) from colCert_76_76_8.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 8 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_8.D (m := 5) from colCert_76_76_8.bind2]
  exact alnAll_76_76_8 j hj hq

theorem leaf_76_76_9 (hp : 9 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 9 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 9 (transLenTr ⟨76, by decide⟩ 9 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 9 (transLenTr ⟨76, by decide⟩ 9 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 9 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 9 (transLenTr ⟨76, by decide⟩ 9 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_9.D (m := 5) from colCert_76_76_9.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 9 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_9.D (m := 5) from colCert_76_76_9.bind2]
  exact alnAll_76_76_9 j hj hq

theorem leaf_76_76_10 (hp : 10 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 10 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 10 (transLenTr ⟨76, by decide⟩ 10 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 10 (transLenTr ⟨76, by decide⟩ 10 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 10 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 10 (transLenTr ⟨76, by decide⟩ 10 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_10.D (m := 5) from colCert_76_76_10.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 10 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_10.D (m := 5) from colCert_76_76_10.bind2]
  exact alnAll_76_76_10 j hj hq

theorem leaf_76_76_11 (hp : 11 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 11 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 11 (transLenTr ⟨76, by decide⟩ 11 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 11 (transLenTr ⟨76, by decide⟩ 11 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 11 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 11 (transLenTr ⟨76, by decide⟩ 11 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_11.D (m := 5) from colCert_76_76_11.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 11 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_11.D (m := 5) from colCert_76_76_11.bind2]
  exact alnAll_76_76_11 j hj hq

theorem leaf_76_76_12 (hp : 12 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 12 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 12 (transLenTr ⟨76, by decide⟩ 12 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 12 (transLenTr ⟨76, by decide⟩ 12 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 12 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 12 (transLenTr ⟨76, by decide⟩ 12 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_12.D (m := 5) from colCert_76_76_12.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 12 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_12.D (m := 5) from colCert_76_76_12.bind2]
  exact alnAll_76_76_12 j hj hq

theorem leaf_76_76_13 (hp : 13 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 13 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 13 (transLenTr ⟨76, by decide⟩ 13 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 13 (transLenTr ⟨76, by decide⟩ 13 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 13 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 13 (transLenTr ⟨76, by decide⟩ 13 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_13.D (m := 5) from colCert_76_76_13.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 13 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_13.D (m := 5) from colCert_76_76_13.bind2]
  exact alnAll_76_76_13 j hj hq

theorem leaf_76_76_14 (hp : 14 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 14 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 14 (transLenTr ⟨76, by decide⟩ 14 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 14 (transLenTr ⟨76, by decide⟩ 14 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 14 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 14 (transLenTr ⟨76, by decide⟩ 14 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_14.D (m := 5) from colCert_76_76_14.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 14 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_14.D (m := 5) from colCert_76_76_14.bind2]
  exact alnAll_76_76_14 j hj hq

theorem leaf_76_76_15 (hp : 15 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 15 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 15 (transLenTr ⟨76, by decide⟩ 15 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 15 (transLenTr ⟨76, by decide⟩ 15 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 15 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 15 (transLenTr ⟨76, by decide⟩ 15 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_15.D (m := 5) from colCert_76_76_15.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 15 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_15.D (m := 5) from colCert_76_76_15.bind2]
  exact alnAll_76_76_15 j hj hq

theorem leaf_76_76_16 (hp : 16 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 16 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 16 (transLenTr ⟨76, by decide⟩ 16 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 16 (transLenTr ⟨76, by decide⟩ 16 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 16 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 16 (transLenTr ⟨76, by decide⟩ 16 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_16.D (m := 5) from colCert_76_76_16.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 16 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_16.D (m := 5) from colCert_76_76_16.bind2]
  exact alnAll_76_76_16 j hj hq

theorem leaf_76_76_17 (hp : 17 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 17 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 17 (transLenTr ⟨76, by decide⟩ 17 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 17 (transLenTr ⟨76, by decide⟩ 17 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 17 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 17 (transLenTr ⟨76, by decide⟩ 17 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_17.D (m := 5) from colCert_76_76_17.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 17 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_17.D (m := 5) from colCert_76_76_17.bind2]
  exact alnAll_76_76_17 j hj hq

theorem leaf_76_76_18 (hp : 18 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 18 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 18 (transLenTr ⟨76, by decide⟩ 18 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 18 (transLenTr ⟨76, by decide⟩ 18 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 18 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 18 (transLenTr ⟨76, by decide⟩ 18 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_18.D (m := 5) from colCert_76_76_18.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 18 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_18.D (m := 5) from colCert_76_76_18.bind2]
  exact alnAll_76_76_18 j hj hq

theorem leaf_76_76_19 (hp : 19 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 19 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 19 (transLenTr ⟨76, by decide⟩ 19 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 19 (transLenTr ⟨76, by decide⟩ 19 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 19 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 19 (transLenTr ⟨76, by decide⟩ 19 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_19.D (m := 5) from colCert_76_76_19.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 19 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_19.D (m := 5) from colCert_76_76_19.bind2]
  exact alnAll_76_76_19 j hj hq

theorem leaf_76_76_20 (hp : 20 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 20 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 20 (transLenTr ⟨76, by decide⟩ 20 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 20 (transLenTr ⟨76, by decide⟩ 20 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 20 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 20 (transLenTr ⟨76, by decide⟩ 20 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_20.D (m := 5) from colCert_76_76_20.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 20 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_20.D (m := 5) from colCert_76_76_20.bind2]
  exact alnAll_76_76_20 j hj hq

theorem leaf_76_76_21 (hp : 21 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 21 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 21 (transLenTr ⟨76, by decide⟩ 21 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 21 (transLenTr ⟨76, by decide⟩ 21 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 21 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 21 (transLenTr ⟨76, by decide⟩ 21 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_21.D (m := 5) from colCert_76_76_21.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 21 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_21.D (m := 5) from colCert_76_76_21.bind2]
  exact alnAll_76_76_21 j hj hq

theorem leaf_76_76_22 (hp : 22 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 22 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 22 (transLenTr ⟨76, by decide⟩ 22 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 22 (transLenTr ⟨76, by decide⟩ 22 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 22 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 22 (transLenTr ⟨76, by decide⟩ 22 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_22.D (m := 5) from colCert_76_76_22.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 22 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_22.D (m := 5) from colCert_76_76_22.bind2]
  exact alnAll_76_76_22 j hj hq

theorem leaf_76_76_23 (hp : 23 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 23 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 23 (transLenTr ⟨76, by decide⟩ 23 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 23 (transLenTr ⟨76, by decide⟩ 23 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 23 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 23 (transLenTr ⟨76, by decide⟩ 23 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_23.D (m := 5) from colCert_76_76_23.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 23 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_23.D (m := 5) from colCert_76_76_23.bind2]
  exact alnAll_76_76_23 j hj hq

theorem leaf_76_76_24 (hp : 24 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 24 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 24 (transLenTr ⟨76, by decide⟩ 24 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 24 (transLenTr ⟨76, by decide⟩ 24 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 24 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 24 (transLenTr ⟨76, by decide⟩ 24 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_24.D (m := 5) from colCert_76_76_24.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 24 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_24.D (m := 5) from colCert_76_76_24.bind2]
  exact alnAll_76_76_24 j hj hq

theorem leaf_76_76_25 (hp : 25 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 25 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 25 (transLenTr ⟨76, by decide⟩ 25 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 25 (transLenTr ⟨76, by decide⟩ 25 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 25 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 25 (transLenTr ⟨76, by decide⟩ 25 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_25.D (m := 5) from colCert_76_76_25.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 25 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_25.D (m := 5) from colCert_76_76_25.bind2]
  exact alnAll_76_76_25 j hj hq

theorem leaf_76_76_30 (hp : 30 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 30 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 30 (transLenTr ⟨76, by decide⟩ 30 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 30 (transLenTr ⟨76, by decide⟩ 30 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 30 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 30 (transLenTr ⟨76, by decide⟩ 30 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_30.D (m := 5) from colCert_76_76_30.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 30 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_30.D (m := 5) from colCert_76_76_30.bind2]
  exact alnAll_76_76_30 j hj hq

theorem leaf_76_76_35 (hp : 35 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 35 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 35 (transLenTr ⟨76, by decide⟩ 35 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 35 (transLenTr ⟨76, by decide⟩ 35 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 35 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 35 (transLenTr ⟨76, by decide⟩ 35 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_35.D (m := 5) from colCert_76_76_35.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 35 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_35.D (m := 5) from colCert_76_76_35.bind2]
  exact alnAll_76_76_35 j hj hq

theorem leaf_76_76_40 (hp : 40 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 40 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 40 (transLenTr ⟨76, by decide⟩ 40 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 40 (transLenTr ⟨76, by decide⟩ 40 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 40 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 40 (transLenTr ⟨76, by decide⟩ 40 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_40.D (m := 5) from colCert_76_76_40.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 40 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_40.D (m := 5) from colCert_76_76_40.bind2]
  exact alnAll_76_76_40 j hj hq

theorem leaf_76_76_45 (hp : 45 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 45 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 45 (transLenTr ⟨76, by decide⟩ 45 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 45 (transLenTr ⟨76, by decide⟩ 45 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 45 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 45 (transLenTr ⟨76, by decide⟩ 45 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_45.D (m := 5) from colCert_76_76_45.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 45 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_45.D (m := 5) from colCert_76_76_45.bind2]
  exact alnAll_76_76_45 j hj hq

theorem leaf_76_76_50 (hp : 50 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 50 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 50 (transLenTr ⟨76, by decide⟩ 50 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 50 (transLenTr ⟨76, by decide⟩ 50 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 50 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 50 (transLenTr ⟨76, by decide⟩ 50 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_50.D (m := 5) from colCert_76_76_50.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 50 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_50.D (m := 5) from colCert_76_76_50.bind2]
  exact alnAll_76_76_50 j hj hq

theorem leaf_76_76_55 (hp : 55 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 55 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 55 (transLenTr ⟨76, by decide⟩ 55 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 55 (transLenTr ⟨76, by decide⟩ 55 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 55 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 55 (transLenTr ⟨76, by decide⟩ 55 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_55.D (m := 5) from colCert_76_76_55.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 55 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_55.D (m := 5) from colCert_76_76_55.bind2]
  exact alnAll_76_76_55 j hj hq

theorem leaf_76_76_60 (hp : 60 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 60 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 60 (transLenTr ⟨76, by decide⟩ 60 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 60 (transLenTr ⟨76, by decide⟩ 60 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 60 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 60 (transLenTr ⟨76, by decide⟩ 60 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_60.D (m := 5) from colCert_76_76_60.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 60 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_60.D (m := 5) from colCert_76_76_60.bind2]
  exact alnAll_76_76_60 j hj hq

theorem leaf_76_76_65 (hp : 65 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 65 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 65 (transLenTr ⟨76, by decide⟩ 65 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 65 (transLenTr ⟨76, by decide⟩ 65 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 65 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 65 (transLenTr ⟨76, by decide⟩ 65 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_65.D (m := 5) from colCert_76_76_65.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 65 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_65.D (m := 5) from colCert_76_76_65.bind2]
  exact alnAll_76_76_65 j hj hq

theorem leaf_76_76_70 (hp : 70 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 70 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 70 (transLenTr ⟨76, by decide⟩ 70 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 70 (transLenTr ⟨76, by decide⟩ 70 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 70 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 70 (transLenTr ⟨76, by decide⟩ 70 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_70.D (m := 5) from colCert_76_76_70.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 70 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_70.D (m := 5) from colCert_76_76_70.bind2]
  exact alnAll_76_76_70 j hj hq

theorem leaf_76_76_75 (hp : 75 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 75 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 75 (transLenTr ⟨76, by decide⟩ 75 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 75 (transLenTr ⟨76, by decide⟩ 75 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 75 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 75 (transLenTr ⟨76, by decide⟩ 75 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_75.D (m := 5) from colCert_76_76_75.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 75 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_75.D (m := 5) from colCert_76_76_75.bind2]
  exact alnAll_76_76_75 j hj hq

theorem leaf_76_76_80 (hp : 80 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 80 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 80 (transLenTr ⟨76, by decide⟩ 80 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 80 (transLenTr ⟨76, by decide⟩ 80 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 80 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 80 (transLenTr ⟨76, by decide⟩ 80 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_80.D (m := 5) from colCert_76_76_80.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 80 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_80.D (m := 5) from colCert_76_76_80.bind2]
  exact alnAll_76_76_80 j hj hq

theorem leaf_76_76_85 (hp : 85 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 85 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 85 (transLenTr ⟨76, by decide⟩ 85 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 85 (transLenTr ⟨76, by decide⟩ 85 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 85 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 85 (transLenTr ⟨76, by decide⟩ 85 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_85.D (m := 5) from colCert_76_76_85.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 85 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_85.D (m := 5) from colCert_76_76_85.bind2]
  exact alnAll_76_76_85 j hj hq

theorem leaf_76_76_90 (hp : 90 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 90 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 90 (transLenTr ⟨76, by decide⟩ 90 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 90 (transLenTr ⟨76, by decide⟩ 90 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 90 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 90 (transLenTr ⟨76, by decide⟩ 90 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_90.D (m := 5) from colCert_76_76_90.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 90 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_90.D (m := 5) from colCert_76_76_90.bind2]
  exact alnAll_76_76_90 j hj hq

theorem leaf_76_76_95 (hp : 95 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 95 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 95 (transLenTr ⟨76, by decide⟩ 95 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 95 (transLenTr ⟨76, by decide⟩ 95 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 95 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 95 (transLenTr ⟨76, by decide⟩ 95 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_95.D (m := 5) from colCert_76_76_95.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 95 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_95.D (m := 5) from colCert_76_76_95.bind2]
  exact alnAll_76_76_95 j hj hq

theorem leaf_76_76_100 (hp : 100 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 100 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 100 (transLenTr ⟨76, by decide⟩ 100 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 100 (transLenTr ⟨76, by decide⟩ 100 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 100 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 100 (transLenTr ⟨76, by decide⟩ 100 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_100.D (m := 5) from colCert_76_76_100.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 100 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_100.D (m := 5) from colCert_76_76_100.bind2]
  exact alnAll_76_76_100 j hj hq

theorem leaf_76_76_105 (hp : 105 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 105 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 105 (transLenTr ⟨76, by decide⟩ 105 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 105 (transLenTr ⟨76, by decide⟩ 105 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 105 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 105 (transLenTr ⟨76, by decide⟩ 105 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_105.D (m := 5) from colCert_76_76_105.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 105 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_105.D (m := 5) from colCert_76_76_105.bind2]
  exact alnAll_76_76_105 j hj hq

theorem leaf_76_76_110 (hp : 110 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 110 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 110 (transLenTr ⟨76, by decide⟩ 110 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 110 (transLenTr ⟨76, by decide⟩ 110 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 110 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 110 (transLenTr ⟨76, by decide⟩ 110 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_110.D (m := 5) from colCert_76_76_110.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 110 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_110.D (m := 5) from colCert_76_76_110.bind2]
  exact alnAll_76_76_110 j hj hq

theorem leaf_76_76_115 (hp : 115 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 115 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 115 (transLenTr ⟨76, by decide⟩ 115 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 115 (transLenTr ⟨76, by decide⟩ 115 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 115 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 115 (transLenTr ⟨76, by decide⟩ 115 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_115.D (m := 5) from colCert_76_76_115.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 115 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_115.D (m := 5) from colCert_76_76_115.bind2]
  exact alnAll_76_76_115 j hj hq

theorem leaf_76_76_120 (hp : 120 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 120 hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 120 (transLenTr ⟨76, by decide⟩ 120 hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨76, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨76, by decide⟩ (listedAt ⟨76, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 120 (transLenTr ⟨76, by decide⟩ 120 hp)) T76_76
      hfix76_76 hinj76_76 hcardT76_76
      (fun i => conj_mem_of_fixedPoints _ _ (T76_76 i) (hfix76_76 i) _)
      ⟨76, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨76, by decide⟩ (Q2.listedAt ⟨76, by decide⟩
        (alnCheck_rep ⟨76, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 120 hp) Q2.T76_76_2 Q2.hfix76_76_2 Q2.hinj76_76_2
      Q2.hcardT76_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T76_76_2 i) (Q2.hfix76_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨76, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 120 (transLenTr ⟨76, by decide⟩ 120 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T76_76 = colFn colCert_76_76_120.D (m := 5) from colCert_76_76_120.bind1,
    show colData2 (⟨76, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 120 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T76_76_2 = colFn colCert_76_76_120.D (m := 5) from colCert_76_76_120.bind2]
  exact alnAll_76_76_120 j hj hq

theorem leaf_77_7_0 (hp : 0 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 0 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp)) T77_7
      hfix77_7 hinj77_7 hcardT77_7
      (fun i => conj_mem_of_fixedPoints _ _ (T77_7 i) (hfix77_7 i) _)
      ⟨77, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 0 hp) Q2.T77_7_2 Q2.hfix77_7_2 Q2.hinj77_7_2
      Q2.hcardT77_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_7_2 i) (Q2.hfix77_7_2 i) _)
      colCert_77_7_0.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_7_1 (hp : 1 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 1 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp)) T77_7
      hfix77_7 hinj77_7 hcardT77_7
      (fun i => conj_mem_of_fixedPoints _ _ (T77_7 i) (hfix77_7 i) _)
      ⟨77, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 1 hp) Q2.T77_7_2 Q2.hfix77_7_2 Q2.hinj77_7_2
      Q2.hcardT77_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_7_2 i) (Q2.hfix77_7_2 i) _)
      colCert_77_7_1.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_7_2 (hp : 2 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 2 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp)) T77_7
      hfix77_7 hinj77_7 hcardT77_7
      (fun i => conj_mem_of_fixedPoints _ _ (T77_7 i) (hfix77_7 i) _)
      ⟨77, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 2 hp) Q2.T77_7_2 Q2.hfix77_7_2 Q2.hinj77_7_2
      Q2.hcardT77_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_7_2 i) (Q2.hfix77_7_2 i) _)
      colCert_77_7_2.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_7_3 (hp : 3 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 3 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp)) T77_7
      hfix77_7 hinj77_7 hcardT77_7
      (fun i => conj_mem_of_fixedPoints _ _ (T77_7 i) (hfix77_7 i) _)
      ⟨77, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 3 hp) Q2.T77_7_2 Q2.hfix77_7_2 Q2.hinj77_7_2
      Q2.hcardT77_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_7_2 i) (Q2.hfix77_7_2 i) _)
      colCert_77_7_3.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_7_4 (hp : 4 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 4 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp)) T77_7
      hfix77_7 hinj77_7 hcardT77_7
      (fun i => conj_mem_of_fixedPoints _ _ (T77_7 i) (hfix77_7 i) _)
      ⟨77, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 4 hp) Q2.T77_7_2 Q2.hfix77_7_2 Q2.hinj77_7_2
      Q2.hcardT77_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_7_2 i) (Q2.hfix77_7_2 i) _)
      colCert_77_7_4.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T77_12
      hfix77_12 hinj77_12 hcardT77_12
      (fun i => conj_mem_of_fixedPoints _ _ (T77_12 i) (hfix77_12 i) _)
      ⟨77, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T77_12_2 Q2.hfix77_12_2 Q2.hinj77_12_2
      Q2.hcardT77_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_12_2 i) (Q2.hfix77_12_2 i) _)
      colCert_77_12_0.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T77_12
      hfix77_12 hinj77_12 hcardT77_12
      (fun i => conj_mem_of_fixedPoints _ _ (T77_12 i) (hfix77_12 i) _)
      ⟨77, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T77_12_2 Q2.hfix77_12_2 Q2.hinj77_12_2
      Q2.hcardT77_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_12_2 i) (Q2.hfix77_12_2 i) _)
      colCert_77_12_1.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T77_12
      hfix77_12 hinj77_12 hcardT77_12
      (fun i => conj_mem_of_fixedPoints _ _ (T77_12 i) (hfix77_12 i) _)
      ⟨77, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T77_12_2 Q2.hfix77_12_2 Q2.hinj77_12_2
      Q2.hcardT77_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_12_2 i) (Q2.hfix77_12_2 i) _)
      colCert_77_12_2.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T77_12
      hfix77_12 hinj77_12 hcardT77_12
      (fun i => conj_mem_of_fixedPoints _ _ (T77_12 i) (hfix77_12 i) _)
      ⟨77, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T77_12_2 Q2.hfix77_12_2 Q2.hinj77_12_2
      Q2.hcardT77_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_12_2 i) (Q2.hfix77_12_2 i) _)
      colCert_77_12_3.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T77_12
      hfix77_12 hinj77_12 hcardT77_12
      (fun i => conj_mem_of_fixedPoints _ _ (T77_12 i) (hfix77_12 i) _)
      ⟨77, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T77_12_2 Q2.hfix77_12_2 Q2.hinj77_12_2
      Q2.hcardT77_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_12_2 i) (Q2.hfix77_12_2 i) _)
      colCert_77_12_4.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_25_0 (hp : 0 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 0 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp)) T77_25
      hfix77_25 hinj77_25 hcardT77_25
      (fun i => conj_mem_of_fixedPoints _ _ (T77_25 i) (hfix77_25 i) _)
      ⟨77, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 0 hp) Q2.T77_25_2 Q2.hfix77_25_2 Q2.hinj77_25_2
      Q2.hcardT77_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_25_2 i) (Q2.hfix77_25_2 i) _)
      colCert_77_25_0.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_25_1 (hp : 1 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 1 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp)) T77_25
      hfix77_25 hinj77_25 hcardT77_25
      (fun i => conj_mem_of_fixedPoints _ _ (T77_25 i) (hfix77_25 i) _)
      ⟨77, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 1 hp) Q2.T77_25_2 Q2.hfix77_25_2 Q2.hinj77_25_2
      Q2.hcardT77_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_25_2 i) (Q2.hfix77_25_2 i) _)
      colCert_77_25_1.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_25_2 (hp : 2 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 2 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp)) T77_25
      hfix77_25 hinj77_25 hcardT77_25
      (fun i => conj_mem_of_fixedPoints _ _ (T77_25 i) (hfix77_25 i) _)
      ⟨77, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 2 hp) Q2.T77_25_2 Q2.hfix77_25_2 Q2.hinj77_25_2
      Q2.hcardT77_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_25_2 i) (Q2.hfix77_25_2 i) _)
      colCert_77_25_2.hD ?_).symm
  rw [alnId_77 j hj]


end LeanDring.P5Presentation
