/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C037
import LeanDring.P5.Data.ColCdd.C038
import LeanDring.P5.Data.ColRestCheap.C143
import LeanDring.P5.Data.ColRestCheap.C144
import LeanDring.P5.Data.ColRestCheap.C145
import LeanDring.P5.Data.ColRestCheap.C146
import LeanDring.P5.Data.ColRestCheap.C147
import LeanDring.P5.Data.EntryK.C014
import LeanDring.P5.Data.EntryK.C015
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C044
import LeanDring.P5.Data.SpeciesDiv.C045

/-! # Stage-5 leaves, chunk 5 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_58_33_10 (hp : 10 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 10 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨58, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp)) T58_33
      hfix58_33 hinj58_33 hcardT58_33
      (fun i => conj_mem_of_fixedPoints _ _ (T58_33 i) (hfix58_33 i) _)
      ⟨58, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 10 hp) Q2.T58_33_2 Q2.hfix58_33_2 Q2.hinj58_33_2
      Q2.hcardT58_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_33_2 i) (Q2.hfix58_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨58, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T58_33 = colFn colCertDiv_58_33_10.D1 (m := 5) from colCertDiv_58_33_10.bind1,
    show colData2 (⟨58, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 10 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T58_33_2 = colFn colCertDiv_58_33_10.D2 (m := 5) from colCertDiv_58_33_10.bind2]
  rw [alnId_58 j hj]
  exact fastcode_of_div ⟨58, by decide⟩ _ _ _
    ((alnId_58 j hj) ▸ Q2.listedAt (⟨58, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨58, by decide⟩ : Fin 148) hj hq).1) colCertDiv_58_33_10_match


theorem leaf_58_33_15 (hp : 15 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 15 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨58, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp)) T58_33
      hfix58_33 hinj58_33 hcardT58_33
      (fun i => conj_mem_of_fixedPoints _ _ (T58_33 i) (hfix58_33 i) _)
      ⟨58, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 15 hp) Q2.T58_33_2 Q2.hfix58_33_2 Q2.hinj58_33_2
      Q2.hcardT58_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_33_2 i) (Q2.hfix58_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨58, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T58_33 = colFn colCertDiv_58_33_15.D1 (m := 5) from colCertDiv_58_33_15.bind1,
    show colData2 (⟨58, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 15 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T58_33_2 = colFn colCertDiv_58_33_15.D2 (m := 5) from colCertDiv_58_33_15.bind2]
  rw [alnId_58 j hj]
  exact fastcode_of_div ⟨58, by decide⟩ _ _ _
    ((alnId_58 j hj) ▸ Q2.listedAt (⟨58, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨58, by decide⟩ : Fin 148) hj hq).1) colCertDiv_58_33_15_match


theorem leaf_58_33_20 (hp : 20 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 20 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨58, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp)) T58_33
      hfix58_33 hinj58_33 hcardT58_33
      (fun i => conj_mem_of_fixedPoints _ _ (T58_33 i) (hfix58_33 i) _)
      ⟨58, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 20 hp) Q2.T58_33_2 Q2.hfix58_33_2 Q2.hinj58_33_2
      Q2.hcardT58_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_33_2 i) (Q2.hfix58_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨58, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T58_33 = colFn colCertDiv_58_33_20.D1 (m := 5) from colCertDiv_58_33_20.bind1,
    show colData2 (⟨58, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 20 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T58_33_2 = colFn colCertDiv_58_33_20.D2 (m := 5) from colCertDiv_58_33_20.bind2]
  rw [alnId_58 j hj]
  exact fastcode_of_div ⟨58, by decide⟩ _ _ _
    ((alnId_58 j hj) ▸ Q2.listedAt (⟨58, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨58, by decide⟩ : Fin 148) hj hq).1) colCertDiv_58_33_20_match


theorem leaf_58_38_0 (hp : 0 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 0 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp)) T58_38
      hfix58_38 hinj58_38 hcardT58_38
      (fun i => conj_mem_of_fixedPoints _ _ (T58_38 i) (hfix58_38 i) _)
      ⟨58, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 0 hp) Q2.T58_38_2 Q2.hfix58_38_2 Q2.hinj58_38_2
      Q2.hcardT58_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_38_2 i) (Q2.hfix58_38_2 i) _)
      colCert_58_38_0.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_38_1 (hp : 1 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 1 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp)) T58_38
      hfix58_38 hinj58_38 hcardT58_38
      (fun i => conj_mem_of_fixedPoints _ _ (T58_38 i) (hfix58_38 i) _)
      ⟨58, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 1 hp) Q2.T58_38_2 Q2.hfix58_38_2 Q2.hinj58_38_2
      Q2.hcardT58_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_38_2 i) (Q2.hfix58_38_2 i) _)
      colCert_58_38_1.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_38_2 (hp : 2 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 2 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp)) T58_38
      hfix58_38 hinj58_38 hcardT58_38
      (fun i => conj_mem_of_fixedPoints _ _ (T58_38 i) (hfix58_38 i) _)
      ⟨58, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 2 hp) Q2.T58_38_2 Q2.hfix58_38_2 Q2.hinj58_38_2
      Q2.hcardT58_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_38_2 i) (Q2.hfix58_38_2 i) _)
      colCert_58_38_2.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_38_3 (hp : 3 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 3 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp)) T58_38
      hfix58_38 hinj58_38 hcardT58_38
      (fun i => conj_mem_of_fixedPoints _ _ (T58_38 i) (hfix58_38 i) _)
      ⟨58, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 3 hp) Q2.T58_38_2 Q2.hfix58_38_2 Q2.hinj58_38_2
      Q2.hcardT58_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_38_2 i) (Q2.hfix58_38_2 i) _)
      colCert_58_38_3.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_38_4 (hp : 4 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 4 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp)) T58_38
      hfix58_38 hinj58_38 hcardT58_38
      (fun i => conj_mem_of_fixedPoints _ _ (T58_38 i) (hfix58_38 i) _)
      ⟨58, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 4 hp) Q2.T58_38_2 Q2.hfix58_38_2 Q2.hinj58_38_2
      Q2.hcardT58_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_38_2 i) (Q2.hfix58_38_2 i) _)
      colCert_58_38_4.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_38_5 (hp : 5 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 5 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨58, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp)) T58_38
      hfix58_38 hinj58_38 hcardT58_38
      (fun i => conj_mem_of_fixedPoints _ _ (T58_38 i) (hfix58_38 i) _)
      ⟨58, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 5 hp) Q2.T58_38_2 Q2.hfix58_38_2 Q2.hinj58_38_2
      Q2.hcardT58_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_38_2 i) (Q2.hfix58_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨58, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T58_38 = colFn colCertDiv_58_38_5.D1 (m := 5) from colCertDiv_58_38_5.bind1,
    show colData2 (⟨58, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 5 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T58_38_2 = colFn colCertDiv_58_38_5.D2 (m := 5) from colCertDiv_58_38_5.bind2]
  rw [alnId_58 j hj]
  exact fastcode_of_div ⟨58, by decide⟩ _ _ _
    ((alnId_58 j hj) ▸ Q2.listedAt (⟨58, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨58, by decide⟩ : Fin 148) hj hq).1) colCertDiv_58_38_5_match


theorem leaf_58_38_10 (hp : 10 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 10 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨58, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp)) T58_38
      hfix58_38 hinj58_38 hcardT58_38
      (fun i => conj_mem_of_fixedPoints _ _ (T58_38 i) (hfix58_38 i) _)
      ⟨58, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 10 hp) Q2.T58_38_2 Q2.hfix58_38_2 Q2.hinj58_38_2
      Q2.hcardT58_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_38_2 i) (Q2.hfix58_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨58, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T58_38 = colFn colCertDiv_58_38_10.D1 (m := 5) from colCertDiv_58_38_10.bind1,
    show colData2 (⟨58, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 10 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T58_38_2 = colFn colCertDiv_58_38_10.D2 (m := 5) from colCertDiv_58_38_10.bind2]
  rw [alnId_58 j hj]
  exact fastcode_of_div ⟨58, by decide⟩ _ _ _
    ((alnId_58 j hj) ▸ Q2.listedAt (⟨58, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨58, by decide⟩ : Fin 148) hj hq).1) colCertDiv_58_38_10_match


theorem leaf_58_38_15 (hp : 15 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 15 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨58, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp)) T58_38
      hfix58_38 hinj58_38 hcardT58_38
      (fun i => conj_mem_of_fixedPoints _ _ (T58_38 i) (hfix58_38 i) _)
      ⟨58, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 15 hp) Q2.T58_38_2 Q2.hfix58_38_2 Q2.hinj58_38_2
      Q2.hcardT58_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_38_2 i) (Q2.hfix58_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨58, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T58_38 = colFn colCertDiv_58_38_15.D1 (m := 5) from colCertDiv_58_38_15.bind1,
    show colData2 (⟨58, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 15 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T58_38_2 = colFn colCertDiv_58_38_15.D2 (m := 5) from colCertDiv_58_38_15.bind2]
  rw [alnId_58 j hj]
  exact fastcode_of_div ⟨58, by decide⟩ _ _ _
    ((alnId_58 j hj) ▸ Q2.listedAt (⟨58, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨58, by decide⟩ : Fin 148) hj hq).1) colCertDiv_58_38_15_match


theorem leaf_58_38_20 (hp : 20 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 20 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨58, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp)) T58_38
      hfix58_38 hinj58_38 hcardT58_38
      (fun i => conj_mem_of_fixedPoints _ _ (T58_38 i) (hfix58_38 i) _)
      ⟨58, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 20 hp) Q2.T58_38_2 Q2.hfix58_38_2 Q2.hinj58_38_2
      Q2.hcardT58_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_38_2 i) (Q2.hfix58_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨58, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T58_38 = colFn colCertDiv_58_38_20.D1 (m := 5) from colCertDiv_58_38_20.bind1,
    show colData2 (⟨58, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 20 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T58_38_2 = colFn colCertDiv_58_38_20.D2 (m := 5) from colCertDiv_58_38_20.bind2]
  rw [alnId_58 j hj]
  exact fastcode_of_div ⟨58, by decide⟩ _ _ _
    ((alnId_58 j hj) ▸ Q2.listedAt (⟨58, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨58, by decide⟩ : Fin 148) hj hq).1) colCertDiv_58_38_20_match


theorem leaf_58_43_0 (hp : 0 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 0 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp)) T58_43
      hfix58_43 hinj58_43 hcardT58_43
      (fun i => conj_mem_of_fixedPoints _ _ (T58_43 i) (hfix58_43 i) _)
      ⟨58, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 0 hp) Q2.T58_43_2 Q2.hfix58_43_2 Q2.hinj58_43_2
      Q2.hcardT58_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_43_2 i) (Q2.hfix58_43_2 i) _)
      colCert_58_43_0.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_43_1 (hp : 1 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 1 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp)) T58_43
      hfix58_43 hinj58_43 hcardT58_43
      (fun i => conj_mem_of_fixedPoints _ _ (T58_43 i) (hfix58_43 i) _)
      ⟨58, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 1 hp) Q2.T58_43_2 Q2.hfix58_43_2 Q2.hinj58_43_2
      Q2.hcardT58_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_43_2 i) (Q2.hfix58_43_2 i) _)
      colCert_58_43_1.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_43_2 (hp : 2 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 2 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp)) T58_43
      hfix58_43 hinj58_43 hcardT58_43
      (fun i => conj_mem_of_fixedPoints _ _ (T58_43 i) (hfix58_43 i) _)
      ⟨58, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 2 hp) Q2.T58_43_2 Q2.hfix58_43_2 Q2.hinj58_43_2
      Q2.hcardT58_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_43_2 i) (Q2.hfix58_43_2 i) _)
      colCert_58_43_2.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_43_3 (hp : 3 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 3 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp)) T58_43
      hfix58_43 hinj58_43 hcardT58_43
      (fun i => conj_mem_of_fixedPoints _ _ (T58_43 i) (hfix58_43 i) _)
      ⟨58, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 3 hp) Q2.T58_43_2 Q2.hfix58_43_2 Q2.hinj58_43_2
      Q2.hcardT58_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_43_2 i) (Q2.hfix58_43_2 i) _)
      colCert_58_43_3.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_43_4 (hp : 4 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 4 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp)) T58_43
      hfix58_43 hinj58_43 hcardT58_43
      (fun i => conj_mem_of_fixedPoints _ _ (T58_43 i) (hfix58_43 i) _)
      ⟨58, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 4 hp) Q2.T58_43_2 Q2.hfix58_43_2 Q2.hinj58_43_2
      Q2.hcardT58_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_43_2 i) (Q2.hfix58_43_2 i) _)
      colCert_58_43_4.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_43_5 (hp : 5 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 5 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨58, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp)) T58_43
      hfix58_43 hinj58_43 hcardT58_43
      (fun i => conj_mem_of_fixedPoints _ _ (T58_43 i) (hfix58_43 i) _)
      ⟨58, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 5 hp) Q2.T58_43_2 Q2.hfix58_43_2 Q2.hinj58_43_2
      Q2.hcardT58_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_43_2 i) (Q2.hfix58_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨58, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T58_43 = colFn colCertDiv_58_43_5.D1 (m := 5) from colCertDiv_58_43_5.bind1,
    show colData2 (⟨58, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 5 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T58_43_2 = colFn colCertDiv_58_43_5.D2 (m := 5) from colCertDiv_58_43_5.bind2]
  rw [alnId_58 j hj]
  exact fastcode_of_div ⟨58, by decide⟩ _ _ _
    ((alnId_58 j hj) ▸ Q2.listedAt (⟨58, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨58, by decide⟩ : Fin 148) hj hq).1) colCertDiv_58_43_5_match


theorem leaf_58_43_10 (hp : 10 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 10 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨58, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp)) T58_43
      hfix58_43 hinj58_43 hcardT58_43
      (fun i => conj_mem_of_fixedPoints _ _ (T58_43 i) (hfix58_43 i) _)
      ⟨58, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 10 hp) Q2.T58_43_2 Q2.hfix58_43_2 Q2.hinj58_43_2
      Q2.hcardT58_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_43_2 i) (Q2.hfix58_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨58, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T58_43 = colFn colCertDiv_58_43_10.D1 (m := 5) from colCertDiv_58_43_10.bind1,
    show colData2 (⟨58, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 10 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T58_43_2 = colFn colCertDiv_58_43_10.D2 (m := 5) from colCertDiv_58_43_10.bind2]
  rw [alnId_58 j hj]
  exact fastcode_of_div ⟨58, by decide⟩ _ _ _
    ((alnId_58 j hj) ▸ Q2.listedAt (⟨58, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨58, by decide⟩ : Fin 148) hj hq).1) colCertDiv_58_43_10_match


theorem leaf_58_43_15 (hp : 15 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 15 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨58, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp)) T58_43
      hfix58_43 hinj58_43 hcardT58_43
      (fun i => conj_mem_of_fixedPoints _ _ (T58_43 i) (hfix58_43 i) _)
      ⟨58, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 15 hp) Q2.T58_43_2 Q2.hfix58_43_2 Q2.hinj58_43_2
      Q2.hcardT58_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_43_2 i) (Q2.hfix58_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨58, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T58_43 = colFn colCertDiv_58_43_15.D1 (m := 5) from colCertDiv_58_43_15.bind1,
    show colData2 (⟨58, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 15 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T58_43_2 = colFn colCertDiv_58_43_15.D2 (m := 5) from colCertDiv_58_43_15.bind2]
  rw [alnId_58 j hj]
  exact fastcode_of_div ⟨58, by decide⟩ _ _ _
    ((alnId_58 j hj) ▸ Q2.listedAt (⟨58, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨58, by decide⟩ : Fin 148) hj hq).1) colCertDiv_58_43_15_match


theorem leaf_58_43_20 (hp : 20 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 20 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨58, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp)) T58_43
      hfix58_43 hinj58_43 hcardT58_43
      (fun i => conj_mem_of_fixedPoints _ _ (T58_43 i) (hfix58_43 i) _)
      ⟨58, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 20 hp) Q2.T58_43_2 Q2.hfix58_43_2 Q2.hinj58_43_2
      Q2.hcardT58_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_43_2 i) (Q2.hfix58_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨58, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T58_43 = colFn colCertDiv_58_43_20.D1 (m := 5) from colCertDiv_58_43_20.bind1,
    show colData2 (⟨58, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 20 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T58_43_2 = colFn colCertDiv_58_43_20.D2 (m := 5) from colCertDiv_58_43_20.bind2]
  rw [alnId_58 j hj]
  exact fastcode_of_div ⟨58, by decide⟩ _ _ _
    ((alnId_58 j hj) ▸ Q2.listedAt (⟨58, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨58, by decide⟩ : Fin 148) hj hq).1) colCertDiv_58_43_20_match


theorem leaf_58_48_0 (hp : 0 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 0 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp)) T58_48
      hfix58_48 hinj58_48 hcardT58_48
      (fun i => conj_mem_of_fixedPoints _ _ (T58_48 i) (hfix58_48 i) _)
      ⟨58, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 0 hp) Q2.T58_48_2 Q2.hfix58_48_2 Q2.hinj58_48_2
      Q2.hcardT58_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_48_2 i) (Q2.hfix58_48_2 i) _)
      colCert_58_48_0.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_48_1 (hp : 1 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 1 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp)) T58_48
      hfix58_48 hinj58_48 hcardT58_48
      (fun i => conj_mem_of_fixedPoints _ _ (T58_48 i) (hfix58_48 i) _)
      ⟨58, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 1 hp) Q2.T58_48_2 Q2.hfix58_48_2 Q2.hinj58_48_2
      Q2.hcardT58_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_48_2 i) (Q2.hfix58_48_2 i) _)
      colCert_58_48_1.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_48_2 (hp : 2 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 2 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp)) T58_48
      hfix58_48 hinj58_48 hcardT58_48
      (fun i => conj_mem_of_fixedPoints _ _ (T58_48 i) (hfix58_48 i) _)
      ⟨58, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 2 hp) Q2.T58_48_2 Q2.hfix58_48_2 Q2.hinj58_48_2
      Q2.hcardT58_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_48_2 i) (Q2.hfix58_48_2 i) _)
      colCert_58_48_2.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_48_3 (hp : 3 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 3 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp)) T58_48
      hfix58_48 hinj58_48 hcardT58_48
      (fun i => conj_mem_of_fixedPoints _ _ (T58_48 i) (hfix58_48 i) _)
      ⟨58, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 3 hp) Q2.T58_48_2 Q2.hfix58_48_2 Q2.hinj58_48_2
      Q2.hcardT58_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_48_2 i) (Q2.hfix58_48_2 i) _)
      colCert_58_48_3.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_48_4 (hp : 4 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 4 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp)) T58_48
      hfix58_48 hinj58_48 hcardT58_48
      (fun i => conj_mem_of_fixedPoints _ _ (T58_48 i) (hfix58_48 i) _)
      ⟨58, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 4 hp) Q2.T58_48_2 Q2.hfix58_48_2 Q2.hinj58_48_2
      Q2.hcardT58_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_48_2 i) (Q2.hfix58_48_2 i) _)
      colCert_58_48_4.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_48_5 (hp : 5 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 5 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨58, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp)) T58_48
      hfix58_48 hinj58_48 hcardT58_48
      (fun i => conj_mem_of_fixedPoints _ _ (T58_48 i) (hfix58_48 i) _)
      ⟨58, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 5 hp) Q2.T58_48_2 Q2.hfix58_48_2 Q2.hinj58_48_2
      Q2.hcardT58_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_48_2 i) (Q2.hfix58_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨58, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T58_48 = colFn colCertDiv_58_48_5.D1 (m := 5) from colCertDiv_58_48_5.bind1,
    show colData2 (⟨58, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 5 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T58_48_2 = colFn colCertDiv_58_48_5.D2 (m := 5) from colCertDiv_58_48_5.bind2]
  rw [alnId_58 j hj]
  exact fastcode_of_div ⟨58, by decide⟩ _ _ _
    ((alnId_58 j hj) ▸ Q2.listedAt (⟨58, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨58, by decide⟩ : Fin 148) hj hq).1) colCertDiv_58_48_5_match


theorem leaf_58_48_10 (hp : 10 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 10 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨58, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp)) T58_48
      hfix58_48 hinj58_48 hcardT58_48
      (fun i => conj_mem_of_fixedPoints _ _ (T58_48 i) (hfix58_48 i) _)
      ⟨58, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 10 hp) Q2.T58_48_2 Q2.hfix58_48_2 Q2.hinj58_48_2
      Q2.hcardT58_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_48_2 i) (Q2.hfix58_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨58, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T58_48 = colFn colCertDiv_58_48_10.D1 (m := 5) from colCertDiv_58_48_10.bind1,
    show colData2 (⟨58, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 10 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T58_48_2 = colFn colCertDiv_58_48_10.D2 (m := 5) from colCertDiv_58_48_10.bind2]
  rw [alnId_58 j hj]
  exact fastcode_of_div ⟨58, by decide⟩ _ _ _
    ((alnId_58 j hj) ▸ Q2.listedAt (⟨58, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨58, by decide⟩ : Fin 148) hj hq).1) colCertDiv_58_48_10_match


theorem leaf_58_48_15 (hp : 15 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 15 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨58, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp)) T58_48
      hfix58_48 hinj58_48 hcardT58_48
      (fun i => conj_mem_of_fixedPoints _ _ (T58_48 i) (hfix58_48 i) _)
      ⟨58, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 15 hp) Q2.T58_48_2 Q2.hfix58_48_2 Q2.hinj58_48_2
      Q2.hcardT58_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_48_2 i) (Q2.hfix58_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨58, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T58_48 = colFn colCertDiv_58_48_15.D1 (m := 5) from colCertDiv_58_48_15.bind1,
    show colData2 (⟨58, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 15 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T58_48_2 = colFn colCertDiv_58_48_15.D2 (m := 5) from colCertDiv_58_48_15.bind2]
  rw [alnId_58 j hj]
  exact fastcode_of_div ⟨58, by decide⟩ _ _ _
    ((alnId_58 j hj) ▸ Q2.listedAt (⟨58, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨58, by decide⟩ : Fin 148) hj hq).1) colCertDiv_58_48_15_match


theorem leaf_58_48_20 (hp : 20 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 20 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨58, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp)) T58_48
      hfix58_48 hinj58_48 hcardT58_48
      (fun i => conj_mem_of_fixedPoints _ _ (T58_48 i) (hfix58_48 i) _)
      ⟨58, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 20 hp) Q2.T58_48_2 Q2.hfix58_48_2 Q2.hinj58_48_2
      Q2.hcardT58_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_48_2 i) (Q2.hfix58_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨58, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T58_48 = colFn colCertDiv_58_48_20.D1 (m := 5) from colCertDiv_58_48_20.bind1,
    show colData2 (⟨58, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 20 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T58_48_2 = colFn colCertDiv_58_48_20.D2 (m := 5) from colCertDiv_58_48_20.bind2]
  rw [alnId_58 j hj]
  exact fastcode_of_div ⟨58, by decide⟩ _ _ _
    ((alnId_58 j hj) ▸ Q2.listedAt (⟨58, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨58, by decide⟩ : Fin 148) hj hq).1) colCertDiv_58_48_20_match


theorem leaf_58_58_0 (hp : 0 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 0 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 0 (transLenTr ⟨58, by decide⟩ 0 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 0 (transLenTr ⟨58, by decide⟩ 0 hp)) T58_58
      hfix58_58 hinj58_58 hcardT58_58
      (fun i => conj_mem_of_fixedPoints _ _ (T58_58 i) (hfix58_58 i) _)
      ⟨58, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 0 hp) Q2.T58_58_2 Q2.hfix58_58_2 Q2.hinj58_58_2
      Q2.hcardT58_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_58_2 i) (Q2.hfix58_58_2 i) _)
      colCert_58_58_0.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_58_1 (hp : 1 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 1 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 1 (transLenTr ⟨58, by decide⟩ 1 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 1 (transLenTr ⟨58, by decide⟩ 1 hp)) T58_58
      hfix58_58 hinj58_58 hcardT58_58
      (fun i => conj_mem_of_fixedPoints _ _ (T58_58 i) (hfix58_58 i) _)
      ⟨58, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 1 hp) Q2.T58_58_2 Q2.hfix58_58_2 Q2.hinj58_58_2
      Q2.hcardT58_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_58_2 i) (Q2.hfix58_58_2 i) _)
      colCert_58_58_1.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_58_2 (hp : 2 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 2 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 2 (transLenTr ⟨58, by decide⟩ 2 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 2 (transLenTr ⟨58, by decide⟩ 2 hp)) T58_58
      hfix58_58 hinj58_58 hcardT58_58
      (fun i => conj_mem_of_fixedPoints _ _ (T58_58 i) (hfix58_58 i) _)
      ⟨58, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 2 hp) Q2.T58_58_2 Q2.hfix58_58_2 Q2.hinj58_58_2
      Q2.hcardT58_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_58_2 i) (Q2.hfix58_58_2 i) _)
      colCert_58_58_2.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_58_3 (hp : 3 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 3 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 3 (transLenTr ⟨58, by decide⟩ 3 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 3 (transLenTr ⟨58, by decide⟩ 3 hp)) T58_58
      hfix58_58 hinj58_58 hcardT58_58
      (fun i => conj_mem_of_fixedPoints _ _ (T58_58 i) (hfix58_58 i) _)
      ⟨58, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 3 hp) Q2.T58_58_2 Q2.hfix58_58_2 Q2.hinj58_58_2
      Q2.hcardT58_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_58_2 i) (Q2.hfix58_58_2 i) _)
      colCert_58_58_3.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_58_4 (hp : 4 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 4 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 4 (transLenTr ⟨58, by decide⟩ 4 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 4 (transLenTr ⟨58, by decide⟩ 4 hp)) T58_58
      hfix58_58 hinj58_58 hcardT58_58
      (fun i => conj_mem_of_fixedPoints _ _ (T58_58 i) (hfix58_58 i) _)
      ⟨58, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 4 hp) Q2.T58_58_2 Q2.hfix58_58_2 Q2.hinj58_58_2
      Q2.hcardT58_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_58_2 i) (Q2.hfix58_58_2 i) _)
      colCert_58_58_4.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_58_5 (hp : 5 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 5 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 5 (transLenTr ⟨58, by decide⟩ 5 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 5 (transLenTr ⟨58, by decide⟩ 5 hp)) T58_58
      hfix58_58 hinj58_58 hcardT58_58
      (fun i => conj_mem_of_fixedPoints _ _ (T58_58 i) (hfix58_58 i) _)
      ⟨58, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 5 hp) Q2.T58_58_2 Q2.hfix58_58_2 Q2.hinj58_58_2
      Q2.hcardT58_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_58_2 i) (Q2.hfix58_58_2 i) _)
      colCert_58_58_5.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_58_6 (hp : 6 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 6 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 6 (transLenTr ⟨58, by decide⟩ 6 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 6 (transLenTr ⟨58, by decide⟩ 6 hp)) T58_58
      hfix58_58 hinj58_58 hcardT58_58
      (fun i => conj_mem_of_fixedPoints _ _ (T58_58 i) (hfix58_58 i) _)
      ⟨58, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 6 hp) Q2.T58_58_2 Q2.hfix58_58_2 Q2.hinj58_58_2
      Q2.hcardT58_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_58_2 i) (Q2.hfix58_58_2 i) _)
      colCert_58_58_6.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_58_7 (hp : 7 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 7 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 7 (transLenTr ⟨58, by decide⟩ 7 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 7 (transLenTr ⟨58, by decide⟩ 7 hp)) T58_58
      hfix58_58 hinj58_58 hcardT58_58
      (fun i => conj_mem_of_fixedPoints _ _ (T58_58 i) (hfix58_58 i) _)
      ⟨58, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 7 hp) Q2.T58_58_2 Q2.hfix58_58_2 Q2.hinj58_58_2
      Q2.hcardT58_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_58_2 i) (Q2.hfix58_58_2 i) _)
      colCert_58_58_7.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_58_8 (hp : 8 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 8 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 8 (transLenTr ⟨58, by decide⟩ 8 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 8 (transLenTr ⟨58, by decide⟩ 8 hp)) T58_58
      hfix58_58 hinj58_58 hcardT58_58
      (fun i => conj_mem_of_fixedPoints _ _ (T58_58 i) (hfix58_58 i) _)
      ⟨58, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 8 hp) Q2.T58_58_2 Q2.hfix58_58_2 Q2.hinj58_58_2
      Q2.hcardT58_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_58_2 i) (Q2.hfix58_58_2 i) _)
      colCert_58_58_8.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_58_9 (hp : 9 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 9 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 9 (transLenTr ⟨58, by decide⟩ 9 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 9 (transLenTr ⟨58, by decide⟩ 9 hp)) T58_58
      hfix58_58 hinj58_58 hcardT58_58
      (fun i => conj_mem_of_fixedPoints _ _ (T58_58 i) (hfix58_58 i) _)
      ⟨58, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 9 hp) Q2.T58_58_2 Q2.hfix58_58_2 Q2.hinj58_58_2
      Q2.hcardT58_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_58_2 i) (Q2.hfix58_58_2 i) _)
      colCert_58_58_9.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_58_10 (hp : 10 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 10 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 10 (transLenTr ⟨58, by decide⟩ 10 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 10 (transLenTr ⟨58, by decide⟩ 10 hp)) T58_58
      hfix58_58 hinj58_58 hcardT58_58
      (fun i => conj_mem_of_fixedPoints _ _ (T58_58 i) (hfix58_58 i) _)
      ⟨58, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 10 hp) Q2.T58_58_2 Q2.hfix58_58_2 Q2.hinj58_58_2
      Q2.hcardT58_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_58_2 i) (Q2.hfix58_58_2 i) _)
      colCert_58_58_10.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_58_11 (hp : 11 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 11 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 11 (transLenTr ⟨58, by decide⟩ 11 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 11 (transLenTr ⟨58, by decide⟩ 11 hp)) T58_58
      hfix58_58 hinj58_58 hcardT58_58
      (fun i => conj_mem_of_fixedPoints _ _ (T58_58 i) (hfix58_58 i) _)
      ⟨58, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 11 hp) Q2.T58_58_2 Q2.hfix58_58_2 Q2.hinj58_58_2
      Q2.hcardT58_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_58_2 i) (Q2.hfix58_58_2 i) _)
      colCert_58_58_11.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_58_12 (hp : 12 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 12 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 12 (transLenTr ⟨58, by decide⟩ 12 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 12 (transLenTr ⟨58, by decide⟩ 12 hp)) T58_58
      hfix58_58 hinj58_58 hcardT58_58
      (fun i => conj_mem_of_fixedPoints _ _ (T58_58 i) (hfix58_58 i) _)
      ⟨58, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 12 hp) Q2.T58_58_2 Q2.hfix58_58_2 Q2.hinj58_58_2
      Q2.hcardT58_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_58_2 i) (Q2.hfix58_58_2 i) _)
      colCert_58_58_12.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_58_13 (hp : 13 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 13 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 13 (transLenTr ⟨58, by decide⟩ 13 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 13 (transLenTr ⟨58, by decide⟩ 13 hp)) T58_58
      hfix58_58 hinj58_58 hcardT58_58
      (fun i => conj_mem_of_fixedPoints _ _ (T58_58 i) (hfix58_58 i) _)
      ⟨58, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 13 hp) Q2.T58_58_2 Q2.hfix58_58_2 Q2.hinj58_58_2
      Q2.hcardT58_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_58_2 i) (Q2.hfix58_58_2 i) _)
      colCert_58_58_13.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_58_14 (hp : 14 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 14 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 14 (transLenTr ⟨58, by decide⟩ 14 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 14 (transLenTr ⟨58, by decide⟩ 14 hp)) T58_58
      hfix58_58 hinj58_58 hcardT58_58
      (fun i => conj_mem_of_fixedPoints _ _ (T58_58 i) (hfix58_58 i) _)
      ⟨58, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 14 hp) Q2.T58_58_2 Q2.hfix58_58_2 Q2.hinj58_58_2
      Q2.hcardT58_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_58_2 i) (Q2.hfix58_58_2 i) _)
      colCert_58_58_14.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_58_15 (hp : 15 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 15 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 15 (transLenTr ⟨58, by decide⟩ 15 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 15 (transLenTr ⟨58, by decide⟩ 15 hp)) T58_58
      hfix58_58 hinj58_58 hcardT58_58
      (fun i => conj_mem_of_fixedPoints _ _ (T58_58 i) (hfix58_58 i) _)
      ⟨58, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 15 hp) Q2.T58_58_2 Q2.hfix58_58_2 Q2.hinj58_58_2
      Q2.hcardT58_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_58_2 i) (Q2.hfix58_58_2 i) _)
      colCert_58_58_15.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_58_16 (hp : 16 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 16 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 16 (transLenTr ⟨58, by decide⟩ 16 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 16 (transLenTr ⟨58, by decide⟩ 16 hp)) T58_58
      hfix58_58 hinj58_58 hcardT58_58
      (fun i => conj_mem_of_fixedPoints _ _ (T58_58 i) (hfix58_58 i) _)
      ⟨58, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 16 hp) Q2.T58_58_2 Q2.hfix58_58_2 Q2.hinj58_58_2
      Q2.hcardT58_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_58_2 i) (Q2.hfix58_58_2 i) _)
      colCert_58_58_16.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_58_17 (hp : 17 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 17 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 17 (transLenTr ⟨58, by decide⟩ 17 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 17 (transLenTr ⟨58, by decide⟩ 17 hp)) T58_58
      hfix58_58 hinj58_58 hcardT58_58
      (fun i => conj_mem_of_fixedPoints _ _ (T58_58 i) (hfix58_58 i) _)
      ⟨58, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 17 hp) Q2.T58_58_2 Q2.hfix58_58_2 Q2.hinj58_58_2
      Q2.hcardT58_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_58_2 i) (Q2.hfix58_58_2 i) _)
      colCert_58_58_17.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_58_18 (hp : 18 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 18 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 18 (transLenTr ⟨58, by decide⟩ 18 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 18 (transLenTr ⟨58, by decide⟩ 18 hp)) T58_58
      hfix58_58 hinj58_58 hcardT58_58
      (fun i => conj_mem_of_fixedPoints _ _ (T58_58 i) (hfix58_58 i) _)
      ⟨58, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 18 hp) Q2.T58_58_2 Q2.hfix58_58_2 Q2.hinj58_58_2
      Q2.hcardT58_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_58_2 i) (Q2.hfix58_58_2 i) _)
      colCert_58_58_18.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_58_19 (hp : 19 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 19 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 19 (transLenTr ⟨58, by decide⟩ 19 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 19 (transLenTr ⟨58, by decide⟩ 19 hp)) T58_58
      hfix58_58 hinj58_58 hcardT58_58
      (fun i => conj_mem_of_fixedPoints _ _ (T58_58 i) (hfix58_58 i) _)
      ⟨58, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 19 hp) Q2.T58_58_2 Q2.hfix58_58_2 Q2.hinj58_58_2
      Q2.hcardT58_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_58_2 i) (Q2.hfix58_58_2 i) _)
      colCert_58_58_19.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_58_20 (hp : 20 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 20 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 20 (transLenTr ⟨58, by decide⟩ 20 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 20 (transLenTr ⟨58, by decide⟩ 20 hp)) T58_58
      hfix58_58 hinj58_58 hcardT58_58
      (fun i => conj_mem_of_fixedPoints _ _ (T58_58 i) (hfix58_58 i) _)
      ⟨58, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 20 hp) Q2.T58_58_2 Q2.hfix58_58_2 Q2.hinj58_58_2
      Q2.hcardT58_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_58_2 i) (Q2.hfix58_58_2 i) _)
      colCert_58_58_20.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_58_21 (hp : 21 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 21 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 21 (transLenTr ⟨58, by decide⟩ 21 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 21 (transLenTr ⟨58, by decide⟩ 21 hp)) T58_58
      hfix58_58 hinj58_58 hcardT58_58
      (fun i => conj_mem_of_fixedPoints _ _ (T58_58 i) (hfix58_58 i) _)
      ⟨58, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 21 hp) Q2.T58_58_2 Q2.hfix58_58_2 Q2.hinj58_58_2
      Q2.hcardT58_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_58_2 i) (Q2.hfix58_58_2 i) _)
      colCert_58_58_21.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_58_22 (hp : 22 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 22 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 22 (transLenTr ⟨58, by decide⟩ 22 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 22 (transLenTr ⟨58, by decide⟩ 22 hp)) T58_58
      hfix58_58 hinj58_58 hcardT58_58
      (fun i => conj_mem_of_fixedPoints _ _ (T58_58 i) (hfix58_58 i) _)
      ⟨58, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 22 hp) Q2.T58_58_2 Q2.hfix58_58_2 Q2.hinj58_58_2
      Q2.hcardT58_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_58_2 i) (Q2.hfix58_58_2 i) _)
      colCert_58_58_22.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_58_23 (hp : 23 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 23 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 23 (transLenTr ⟨58, by decide⟩ 23 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 23 (transLenTr ⟨58, by decide⟩ 23 hp)) T58_58
      hfix58_58 hinj58_58 hcardT58_58
      (fun i => conj_mem_of_fixedPoints _ _ (T58_58 i) (hfix58_58 i) _)
      ⟨58, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 23 hp) Q2.T58_58_2 Q2.hfix58_58_2 Q2.hinj58_58_2
      Q2.hcardT58_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_58_2 i) (Q2.hfix58_58_2 i) _)
      colCert_58_58_23.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_58_24 (hp : 24 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 24 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 24 (transLenTr ⟨58, by decide⟩ 24 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 24 (transLenTr ⟨58, by decide⟩ 24 hp)) T58_58
      hfix58_58 hinj58_58 hcardT58_58
      (fun i => conj_mem_of_fixedPoints _ _ (T58_58 i) (hfix58_58 i) _)
      ⟨58, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 24 hp) Q2.T58_58_2 Q2.hfix58_58_2 Q2.hinj58_58_2
      Q2.hcardT58_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_58_2 i) (Q2.hfix58_58_2 i) _)
      colCert_58_58_24.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_59_8_0 (hp : 0 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 0 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp)) T59_8
      hfix59_8 hinj59_8 hcardT59_8
      (fun i => conj_mem_of_fixedPoints _ _ (T59_8 i) (hfix59_8 i) _)
      ⟨59, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 0 hp) Q2.T59_8_2 Q2.hfix59_8_2 Q2.hinj59_8_2
      Q2.hcardT59_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_8_2 i) (Q2.hfix59_8_2 i) _)
      colCert_59_8_0.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_8_1 (hp : 1 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 1 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp)) T59_8
      hfix59_8 hinj59_8 hcardT59_8
      (fun i => conj_mem_of_fixedPoints _ _ (T59_8 i) (hfix59_8 i) _)
      ⟨59, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 1 hp) Q2.T59_8_2 Q2.hfix59_8_2 Q2.hinj59_8_2
      Q2.hcardT59_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_8_2 i) (Q2.hfix59_8_2 i) _)
      colCert_59_8_1.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_8_2 (hp : 2 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 2 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp)) T59_8
      hfix59_8 hinj59_8 hcardT59_8
      (fun i => conj_mem_of_fixedPoints _ _ (T59_8 i) (hfix59_8 i) _)
      ⟨59, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 2 hp) Q2.T59_8_2 Q2.hfix59_8_2 Q2.hinj59_8_2
      Q2.hcardT59_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_8_2 i) (Q2.hfix59_8_2 i) _)
      colCert_59_8_2.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_8_3 (hp : 3 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 3 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp)) T59_8
      hfix59_8 hinj59_8 hcardT59_8
      (fun i => conj_mem_of_fixedPoints _ _ (T59_8 i) (hfix59_8 i) _)
      ⟨59, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 3 hp) Q2.T59_8_2 Q2.hfix59_8_2 Q2.hinj59_8_2
      Q2.hcardT59_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_8_2 i) (Q2.hfix59_8_2 i) _)
      colCert_59_8_3.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_8_4 (hp : 4 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 4 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp)) T59_8
      hfix59_8 hinj59_8 hcardT59_8
      (fun i => conj_mem_of_fixedPoints _ _ (T59_8 i) (hfix59_8 i) _)
      ⟨59, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 4 hp) Q2.T59_8_2 Q2.hfix59_8_2 Q2.hinj59_8_2
      Q2.hcardT59_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_8_2 i) (Q2.hfix59_8_2 i) _)
      colCert_59_8_4.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T59_12
      hfix59_12 hinj59_12 hcardT59_12
      (fun i => conj_mem_of_fixedPoints _ _ (T59_12 i) (hfix59_12 i) _)
      ⟨59, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T59_12_2 Q2.hfix59_12_2 Q2.hinj59_12_2
      Q2.hcardT59_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_12_2 i) (Q2.hfix59_12_2 i) _)
      colCert_59_12_0.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T59_12
      hfix59_12 hinj59_12 hcardT59_12
      (fun i => conj_mem_of_fixedPoints _ _ (T59_12 i) (hfix59_12 i) _)
      ⟨59, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T59_12_2 Q2.hfix59_12_2 Q2.hinj59_12_2
      Q2.hcardT59_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_12_2 i) (Q2.hfix59_12_2 i) _)
      colCert_59_12_1.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T59_12
      hfix59_12 hinj59_12 hcardT59_12
      (fun i => conj_mem_of_fixedPoints _ _ (T59_12 i) (hfix59_12 i) _)
      ⟨59, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T59_12_2 Q2.hfix59_12_2 Q2.hinj59_12_2
      Q2.hcardT59_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_12_2 i) (Q2.hfix59_12_2 i) _)
      colCert_59_12_2.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T59_12
      hfix59_12 hinj59_12 hcardT59_12
      (fun i => conj_mem_of_fixedPoints _ _ (T59_12 i) (hfix59_12 i) _)
      ⟨59, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T59_12_2 Q2.hfix59_12_2 Q2.hinj59_12_2
      Q2.hcardT59_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_12_2 i) (Q2.hfix59_12_2 i) _)
      colCert_59_12_3.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T59_12
      hfix59_12 hinj59_12 hcardT59_12
      (fun i => conj_mem_of_fixedPoints _ _ (T59_12 i) (hfix59_12 i) _)
      ⟨59, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T59_12_2 Q2.hfix59_12_2 Q2.hinj59_12_2
      Q2.hcardT59_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_12_2 i) (Q2.hfix59_12_2 i) _)
      colCert_59_12_4.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_26_0 (hp : 0 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 0 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp)) T59_26
      hfix59_26 hinj59_26 hcardT59_26
      (fun i => conj_mem_of_fixedPoints _ _ (T59_26 i) (hfix59_26 i) _)
      ⟨59, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 0 hp) Q2.T59_26_2 Q2.hfix59_26_2 Q2.hinj59_26_2
      Q2.hcardT59_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_26_2 i) (Q2.hfix59_26_2 i) _)
      colCert_59_26_0.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_26_1 (hp : 1 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 1 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp)) T59_26
      hfix59_26 hinj59_26 hcardT59_26
      (fun i => conj_mem_of_fixedPoints _ _ (T59_26 i) (hfix59_26 i) _)
      ⟨59, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 1 hp) Q2.T59_26_2 Q2.hfix59_26_2 Q2.hinj59_26_2
      Q2.hcardT59_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_26_2 i) (Q2.hfix59_26_2 i) _)
      colCert_59_26_1.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_26_2 (hp : 2 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 2 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp)) T59_26
      hfix59_26 hinj59_26 hcardT59_26
      (fun i => conj_mem_of_fixedPoints _ _ (T59_26 i) (hfix59_26 i) _)
      ⟨59, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 2 hp) Q2.T59_26_2 Q2.hfix59_26_2 Q2.hinj59_26_2
      Q2.hcardT59_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_26_2 i) (Q2.hfix59_26_2 i) _)
      colCert_59_26_2.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_26_3 (hp : 3 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 3 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp)) T59_26
      hfix59_26 hinj59_26 hcardT59_26
      (fun i => conj_mem_of_fixedPoints _ _ (T59_26 i) (hfix59_26 i) _)
      ⟨59, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 3 hp) Q2.T59_26_2 Q2.hfix59_26_2 Q2.hinj59_26_2
      Q2.hcardT59_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_26_2 i) (Q2.hfix59_26_2 i) _)
      colCert_59_26_3.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_26_4 (hp : 4 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 4 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp)) T59_26
      hfix59_26 hinj59_26 hcardT59_26
      (fun i => conj_mem_of_fixedPoints _ _ (T59_26 i) (hfix59_26 i) _)
      ⟨59, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 4 hp) Q2.T59_26_2 Q2.hfix59_26_2 Q2.hinj59_26_2
      Q2.hcardT59_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_26_2 i) (Q2.hfix59_26_2 i) _)
      colCert_59_26_4.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_26_5 (hp : 5 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 5 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp)) T59_26
      hfix59_26 hinj59_26 hcardT59_26
      (fun i => conj_mem_of_fixedPoints _ _ (T59_26 i) (hfix59_26 i) _)
      ⟨59, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 5 hp) Q2.T59_26_2 Q2.hfix59_26_2 Q2.hinj59_26_2
      Q2.hcardT59_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_26_2 i) (Q2.hfix59_26_2 i) _)
      colCert_59_26_5.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_26_10 (hp : 10 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 10 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp)) T59_26
      hfix59_26 hinj59_26 hcardT59_26
      (fun i => conj_mem_of_fixedPoints _ _ (T59_26 i) (hfix59_26 i) _)
      ⟨59, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 10 hp) Q2.T59_26_2 Q2.hfix59_26_2 Q2.hinj59_26_2
      Q2.hcardT59_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_26_2 i) (Q2.hfix59_26_2 i) _)
      colCert_59_26_10.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_26_15 (hp : 15 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 15 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp)) T59_26
      hfix59_26 hinj59_26 hcardT59_26
      (fun i => conj_mem_of_fixedPoints _ _ (T59_26 i) (hfix59_26 i) _)
      ⟨59, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 15 hp) Q2.T59_26_2 Q2.hfix59_26_2 Q2.hinj59_26_2
      Q2.hcardT59_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_26_2 i) (Q2.hfix59_26_2 i) _)
      colCert_59_26_15.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_26_20 (hp : 20 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 20 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp)) T59_26
      hfix59_26 hinj59_26 hcardT59_26
      (fun i => conj_mem_of_fixedPoints _ _ (T59_26 i) (hfix59_26 i) _)
      ⟨59, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 20 hp) Q2.T59_26_2 Q2.hfix59_26_2 Q2.hinj59_26_2
      Q2.hcardT59_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_26_2 i) (Q2.hfix59_26_2 i) _)
      colCert_59_26_20.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_28_0 (hp : 0 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 0 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp)) T59_28
      hfix59_28 hinj59_28 hcardT59_28
      (fun i => conj_mem_of_fixedPoints _ _ (T59_28 i) (hfix59_28 i) _)
      ⟨59, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 0 hp) Q2.T59_28_2 Q2.hfix59_28_2 Q2.hinj59_28_2
      Q2.hcardT59_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_28_2 i) (Q2.hfix59_28_2 i) _)
      colCert_59_28_0.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_28_1 (hp : 1 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 1 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp)) T59_28
      hfix59_28 hinj59_28 hcardT59_28
      (fun i => conj_mem_of_fixedPoints _ _ (T59_28 i) (hfix59_28 i) _)
      ⟨59, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 1 hp) Q2.T59_28_2 Q2.hfix59_28_2 Q2.hinj59_28_2
      Q2.hcardT59_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_28_2 i) (Q2.hfix59_28_2 i) _)
      colCert_59_28_1.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_28_2 (hp : 2 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 2 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp)) T59_28
      hfix59_28 hinj59_28 hcardT59_28
      (fun i => conj_mem_of_fixedPoints _ _ (T59_28 i) (hfix59_28 i) _)
      ⟨59, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 2 hp) Q2.T59_28_2 Q2.hfix59_28_2 Q2.hinj59_28_2
      Q2.hcardT59_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_28_2 i) (Q2.hfix59_28_2 i) _)
      colCert_59_28_2.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_28_3 (hp : 3 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 3 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp)) T59_28
      hfix59_28 hinj59_28 hcardT59_28
      (fun i => conj_mem_of_fixedPoints _ _ (T59_28 i) (hfix59_28 i) _)
      ⟨59, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 3 hp) Q2.T59_28_2 Q2.hfix59_28_2 Q2.hinj59_28_2
      Q2.hcardT59_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_28_2 i) (Q2.hfix59_28_2 i) _)
      colCert_59_28_3.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_28_4 (hp : 4 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 4 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp)) T59_28
      hfix59_28 hinj59_28 hcardT59_28
      (fun i => conj_mem_of_fixedPoints _ _ (T59_28 i) (hfix59_28 i) _)
      ⟨59, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 4 hp) Q2.T59_28_2 Q2.hfix59_28_2 Q2.hinj59_28_2
      Q2.hcardT59_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_28_2 i) (Q2.hfix59_28_2 i) _)
      colCert_59_28_4.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_28_5 (hp : 5 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 5 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨59, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp)) T59_28
      hfix59_28 hinj59_28 hcardT59_28
      (fun i => conj_mem_of_fixedPoints _ _ (T59_28 i) (hfix59_28 i) _)
      ⟨59, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 5 hp) Q2.T59_28_2 Q2.hfix59_28_2 Q2.hinj59_28_2
      Q2.hcardT59_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_28_2 i) (Q2.hfix59_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨59, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T59_28 = colFn colCertDiv_59_28_5.D1 (m := 5) from colCertDiv_59_28_5.bind1,
    show colData2 (⟨59, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 5 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T59_28_2 = colFn colCertDiv_59_28_5.D2 (m := 5) from colCertDiv_59_28_5.bind2]
  rw [alnId_59 j hj]
  exact fastcode_of_div ⟨59, by decide⟩ _ _ _
    ((alnId_59 j hj) ▸ Q2.listedAt (⟨59, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨59, by decide⟩ : Fin 148) hj hq).1) colCertDiv_59_28_5_match


theorem leaf_59_28_10 (hp : 10 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 10 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨59, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp)) T59_28
      hfix59_28 hinj59_28 hcardT59_28
      (fun i => conj_mem_of_fixedPoints _ _ (T59_28 i) (hfix59_28 i) _)
      ⟨59, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 10 hp) Q2.T59_28_2 Q2.hfix59_28_2 Q2.hinj59_28_2
      Q2.hcardT59_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_28_2 i) (Q2.hfix59_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨59, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T59_28 = colFn colCertDiv_59_28_10.D1 (m := 5) from colCertDiv_59_28_10.bind1,
    show colData2 (⟨59, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 10 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T59_28_2 = colFn colCertDiv_59_28_10.D2 (m := 5) from colCertDiv_59_28_10.bind2]
  rw [alnId_59 j hj]
  exact fastcode_of_div ⟨59, by decide⟩ _ _ _
    ((alnId_59 j hj) ▸ Q2.listedAt (⟨59, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨59, by decide⟩ : Fin 148) hj hq).1) colCertDiv_59_28_10_match


theorem leaf_59_28_15 (hp : 15 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 15 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨59, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp)) T59_28
      hfix59_28 hinj59_28 hcardT59_28
      (fun i => conj_mem_of_fixedPoints _ _ (T59_28 i) (hfix59_28 i) _)
      ⟨59, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 15 hp) Q2.T59_28_2 Q2.hfix59_28_2 Q2.hinj59_28_2
      Q2.hcardT59_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_28_2 i) (Q2.hfix59_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨59, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T59_28 = colFn colCertDiv_59_28_15.D1 (m := 5) from colCertDiv_59_28_15.bind1,
    show colData2 (⟨59, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 15 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T59_28_2 = colFn colCertDiv_59_28_15.D2 (m := 5) from colCertDiv_59_28_15.bind2]
  rw [alnId_59 j hj]
  exact fastcode_of_div ⟨59, by decide⟩ _ _ _
    ((alnId_59 j hj) ▸ Q2.listedAt (⟨59, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨59, by decide⟩ : Fin 148) hj hq).1) colCertDiv_59_28_15_match


theorem leaf_59_28_20 (hp : 20 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 20 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨59, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp)) T59_28
      hfix59_28 hinj59_28 hcardT59_28
      (fun i => conj_mem_of_fixedPoints _ _ (T59_28 i) (hfix59_28 i) _)
      ⟨59, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 20 hp) Q2.T59_28_2 Q2.hfix59_28_2 Q2.hinj59_28_2
      Q2.hcardT59_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_28_2 i) (Q2.hfix59_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨59, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T59_28 = colFn colCertDiv_59_28_20.D1 (m := 5) from colCertDiv_59_28_20.bind1,
    show colData2 (⟨59, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 20 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T59_28_2 = colFn colCertDiv_59_28_20.D2 (m := 5) from colCertDiv_59_28_20.bind2]
  rw [alnId_59 j hj]
  exact fastcode_of_div ⟨59, by decide⟩ _ _ _
    ((alnId_59 j hj) ▸ Q2.listedAt (⟨59, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨59, by decide⟩ : Fin 148) hj hq).1) colCertDiv_59_28_20_match


theorem leaf_59_33_0 (hp : 0 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 0 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp)) T59_33
      hfix59_33 hinj59_33 hcardT59_33
      (fun i => conj_mem_of_fixedPoints _ _ (T59_33 i) (hfix59_33 i) _)
      ⟨59, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 0 hp) Q2.T59_33_2 Q2.hfix59_33_2 Q2.hinj59_33_2
      Q2.hcardT59_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_33_2 i) (Q2.hfix59_33_2 i) _)
      colCert_59_33_0.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_33_1 (hp : 1 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 1 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp)) T59_33
      hfix59_33 hinj59_33 hcardT59_33
      (fun i => conj_mem_of_fixedPoints _ _ (T59_33 i) (hfix59_33 i) _)
      ⟨59, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 1 hp) Q2.T59_33_2 Q2.hfix59_33_2 Q2.hinj59_33_2
      Q2.hcardT59_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_33_2 i) (Q2.hfix59_33_2 i) _)
      colCert_59_33_1.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_33_2 (hp : 2 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 2 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp)) T59_33
      hfix59_33 hinj59_33 hcardT59_33
      (fun i => conj_mem_of_fixedPoints _ _ (T59_33 i) (hfix59_33 i) _)
      ⟨59, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 2 hp) Q2.T59_33_2 Q2.hfix59_33_2 Q2.hinj59_33_2
      Q2.hcardT59_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_33_2 i) (Q2.hfix59_33_2 i) _)
      colCert_59_33_2.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_33_3 (hp : 3 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 3 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp)) T59_33
      hfix59_33 hinj59_33 hcardT59_33
      (fun i => conj_mem_of_fixedPoints _ _ (T59_33 i) (hfix59_33 i) _)
      ⟨59, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 3 hp) Q2.T59_33_2 Q2.hfix59_33_2 Q2.hinj59_33_2
      Q2.hcardT59_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_33_2 i) (Q2.hfix59_33_2 i) _)
      colCert_59_33_3.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_33_4 (hp : 4 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 4 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp)) T59_33
      hfix59_33 hinj59_33 hcardT59_33
      (fun i => conj_mem_of_fixedPoints _ _ (T59_33 i) (hfix59_33 i) _)
      ⟨59, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 4 hp) Q2.T59_33_2 Q2.hfix59_33_2 Q2.hinj59_33_2
      Q2.hcardT59_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_33_2 i) (Q2.hfix59_33_2 i) _)
      colCert_59_33_4.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_33_5 (hp : 5 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 5 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨59, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp)) T59_33
      hfix59_33 hinj59_33 hcardT59_33
      (fun i => conj_mem_of_fixedPoints _ _ (T59_33 i) (hfix59_33 i) _)
      ⟨59, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 5 hp) Q2.T59_33_2 Q2.hfix59_33_2 Q2.hinj59_33_2
      Q2.hcardT59_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_33_2 i) (Q2.hfix59_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨59, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T59_33 = colFn colCertDiv_59_33_5.D1 (m := 5) from colCertDiv_59_33_5.bind1,
    show colData2 (⟨59, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 5 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T59_33_2 = colFn colCertDiv_59_33_5.D2 (m := 5) from colCertDiv_59_33_5.bind2]
  rw [alnId_59 j hj]
  exact fastcode_of_div ⟨59, by decide⟩ _ _ _
    ((alnId_59 j hj) ▸ Q2.listedAt (⟨59, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨59, by decide⟩ : Fin 148) hj hq).1) colCertDiv_59_33_5_match


theorem leaf_59_33_10 (hp : 10 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 10 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨59, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp)) T59_33
      hfix59_33 hinj59_33 hcardT59_33
      (fun i => conj_mem_of_fixedPoints _ _ (T59_33 i) (hfix59_33 i) _)
      ⟨59, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 10 hp) Q2.T59_33_2 Q2.hfix59_33_2 Q2.hinj59_33_2
      Q2.hcardT59_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_33_2 i) (Q2.hfix59_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨59, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T59_33 = colFn colCertDiv_59_33_10.D1 (m := 5) from colCertDiv_59_33_10.bind1,
    show colData2 (⟨59, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 10 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T59_33_2 = colFn colCertDiv_59_33_10.D2 (m := 5) from colCertDiv_59_33_10.bind2]
  rw [alnId_59 j hj]
  exact fastcode_of_div ⟨59, by decide⟩ _ _ _
    ((alnId_59 j hj) ▸ Q2.listedAt (⟨59, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨59, by decide⟩ : Fin 148) hj hq).1) colCertDiv_59_33_10_match


theorem leaf_59_33_15 (hp : 15 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 15 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨59, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp)) T59_33
      hfix59_33 hinj59_33 hcardT59_33
      (fun i => conj_mem_of_fixedPoints _ _ (T59_33 i) (hfix59_33 i) _)
      ⟨59, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 15 hp) Q2.T59_33_2 Q2.hfix59_33_2 Q2.hinj59_33_2
      Q2.hcardT59_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_33_2 i) (Q2.hfix59_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨59, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T59_33 = colFn colCertDiv_59_33_15.D1 (m := 5) from colCertDiv_59_33_15.bind1,
    show colData2 (⟨59, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 15 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T59_33_2 = colFn colCertDiv_59_33_15.D2 (m := 5) from colCertDiv_59_33_15.bind2]
  rw [alnId_59 j hj]
  exact fastcode_of_div ⟨59, by decide⟩ _ _ _
    ((alnId_59 j hj) ▸ Q2.listedAt (⟨59, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨59, by decide⟩ : Fin 148) hj hq).1) colCertDiv_59_33_15_match


theorem leaf_59_33_20 (hp : 20 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 20 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨59, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp)) T59_33
      hfix59_33 hinj59_33 hcardT59_33
      (fun i => conj_mem_of_fixedPoints _ _ (T59_33 i) (hfix59_33 i) _)
      ⟨59, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 20 hp) Q2.T59_33_2 Q2.hfix59_33_2 Q2.hinj59_33_2
      Q2.hcardT59_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_33_2 i) (Q2.hfix59_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨59, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T59_33 = colFn colCertDiv_59_33_20.D1 (m := 5) from colCertDiv_59_33_20.bind1,
    show colData2 (⟨59, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 20 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T59_33_2 = colFn colCertDiv_59_33_20.D2 (m := 5) from colCertDiv_59_33_20.bind2]
  rw [alnId_59 j hj]
  exact fastcode_of_div ⟨59, by decide⟩ _ _ _
    ((alnId_59 j hj) ▸ Q2.listedAt (⟨59, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨59, by decide⟩ : Fin 148) hj hq).1) colCertDiv_59_33_20_match


theorem leaf_59_38_0 (hp : 0 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 0 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp)) T59_38
      hfix59_38 hinj59_38 hcardT59_38
      (fun i => conj_mem_of_fixedPoints _ _ (T59_38 i) (hfix59_38 i) _)
      ⟨59, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 0 hp) Q2.T59_38_2 Q2.hfix59_38_2 Q2.hinj59_38_2
      Q2.hcardT59_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_38_2 i) (Q2.hfix59_38_2 i) _)
      colCert_59_38_0.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_38_1 (hp : 1 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 1 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp)) T59_38
      hfix59_38 hinj59_38 hcardT59_38
      (fun i => conj_mem_of_fixedPoints _ _ (T59_38 i) (hfix59_38 i) _)
      ⟨59, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 1 hp) Q2.T59_38_2 Q2.hfix59_38_2 Q2.hinj59_38_2
      Q2.hcardT59_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_38_2 i) (Q2.hfix59_38_2 i) _)
      colCert_59_38_1.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_38_2 (hp : 2 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 2 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp)) T59_38
      hfix59_38 hinj59_38 hcardT59_38
      (fun i => conj_mem_of_fixedPoints _ _ (T59_38 i) (hfix59_38 i) _)
      ⟨59, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 2 hp) Q2.T59_38_2 Q2.hfix59_38_2 Q2.hinj59_38_2
      Q2.hcardT59_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_38_2 i) (Q2.hfix59_38_2 i) _)
      colCert_59_38_2.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_38_3 (hp : 3 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 3 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp)) T59_38
      hfix59_38 hinj59_38 hcardT59_38
      (fun i => conj_mem_of_fixedPoints _ _ (T59_38 i) (hfix59_38 i) _)
      ⟨59, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 3 hp) Q2.T59_38_2 Q2.hfix59_38_2 Q2.hinj59_38_2
      Q2.hcardT59_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_38_2 i) (Q2.hfix59_38_2 i) _)
      colCert_59_38_3.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_38_4 (hp : 4 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 4 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp)) T59_38
      hfix59_38 hinj59_38 hcardT59_38
      (fun i => conj_mem_of_fixedPoints _ _ (T59_38 i) (hfix59_38 i) _)
      ⟨59, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 4 hp) Q2.T59_38_2 Q2.hfix59_38_2 Q2.hinj59_38_2
      Q2.hcardT59_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_38_2 i) (Q2.hfix59_38_2 i) _)
      colCert_59_38_4.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_38_5 (hp : 5 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 5 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨59, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp)) T59_38
      hfix59_38 hinj59_38 hcardT59_38
      (fun i => conj_mem_of_fixedPoints _ _ (T59_38 i) (hfix59_38 i) _)
      ⟨59, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 5 hp) Q2.T59_38_2 Q2.hfix59_38_2 Q2.hinj59_38_2
      Q2.hcardT59_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_38_2 i) (Q2.hfix59_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨59, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T59_38 = colFn colCertDiv_59_38_5.D1 (m := 5) from colCertDiv_59_38_5.bind1,
    show colData2 (⟨59, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 5 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T59_38_2 = colFn colCertDiv_59_38_5.D2 (m := 5) from colCertDiv_59_38_5.bind2]
  rw [alnId_59 j hj]
  exact fastcode_of_div ⟨59, by decide⟩ _ _ _
    ((alnId_59 j hj) ▸ Q2.listedAt (⟨59, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨59, by decide⟩ : Fin 148) hj hq).1) colCertDiv_59_38_5_match


theorem leaf_59_38_10 (hp : 10 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 10 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨59, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp)) T59_38
      hfix59_38 hinj59_38 hcardT59_38
      (fun i => conj_mem_of_fixedPoints _ _ (T59_38 i) (hfix59_38 i) _)
      ⟨59, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 10 hp) Q2.T59_38_2 Q2.hfix59_38_2 Q2.hinj59_38_2
      Q2.hcardT59_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_38_2 i) (Q2.hfix59_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨59, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T59_38 = colFn colCertDiv_59_38_10.D1 (m := 5) from colCertDiv_59_38_10.bind1,
    show colData2 (⟨59, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 10 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T59_38_2 = colFn colCertDiv_59_38_10.D2 (m := 5) from colCertDiv_59_38_10.bind2]
  rw [alnId_59 j hj]
  exact fastcode_of_div ⟨59, by decide⟩ _ _ _
    ((alnId_59 j hj) ▸ Q2.listedAt (⟨59, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨59, by decide⟩ : Fin 148) hj hq).1) colCertDiv_59_38_10_match


theorem leaf_59_38_15 (hp : 15 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 15 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨59, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp)) T59_38
      hfix59_38 hinj59_38 hcardT59_38
      (fun i => conj_mem_of_fixedPoints _ _ (T59_38 i) (hfix59_38 i) _)
      ⟨59, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 15 hp) Q2.T59_38_2 Q2.hfix59_38_2 Q2.hinj59_38_2
      Q2.hcardT59_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_38_2 i) (Q2.hfix59_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨59, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T59_38 = colFn colCertDiv_59_38_15.D1 (m := 5) from colCertDiv_59_38_15.bind1,
    show colData2 (⟨59, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 15 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T59_38_2 = colFn colCertDiv_59_38_15.D2 (m := 5) from colCertDiv_59_38_15.bind2]
  rw [alnId_59 j hj]
  exact fastcode_of_div ⟨59, by decide⟩ _ _ _
    ((alnId_59 j hj) ▸ Q2.listedAt (⟨59, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨59, by decide⟩ : Fin 148) hj hq).1) colCertDiv_59_38_15_match


theorem leaf_59_38_20 (hp : 20 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 20 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨59, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp)) T59_38
      hfix59_38 hinj59_38 hcardT59_38
      (fun i => conj_mem_of_fixedPoints _ _ (T59_38 i) (hfix59_38 i) _)
      ⟨59, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 20 hp) Q2.T59_38_2 Q2.hfix59_38_2 Q2.hinj59_38_2
      Q2.hcardT59_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_38_2 i) (Q2.hfix59_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨59, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T59_38 = colFn colCertDiv_59_38_20.D1 (m := 5) from colCertDiv_59_38_20.bind1,
    show colData2 (⟨59, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 20 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T59_38_2 = colFn colCertDiv_59_38_20.D2 (m := 5) from colCertDiv_59_38_20.bind2]
  rw [alnId_59 j hj]
  exact fastcode_of_div ⟨59, by decide⟩ _ _ _
    ((alnId_59 j hj) ▸ Q2.listedAt (⟨59, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨59, by decide⟩ : Fin 148) hj hq).1) colCertDiv_59_38_20_match


theorem leaf_59_43_0 (hp : 0 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 0 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp)) T59_43
      hfix59_43 hinj59_43 hcardT59_43
      (fun i => conj_mem_of_fixedPoints _ _ (T59_43 i) (hfix59_43 i) _)
      ⟨59, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 0 hp) Q2.T59_43_2 Q2.hfix59_43_2 Q2.hinj59_43_2
      Q2.hcardT59_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_43_2 i) (Q2.hfix59_43_2 i) _)
      colCert_59_43_0.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_43_1 (hp : 1 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 1 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp)) T59_43
      hfix59_43 hinj59_43 hcardT59_43
      (fun i => conj_mem_of_fixedPoints _ _ (T59_43 i) (hfix59_43 i) _)
      ⟨59, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 1 hp) Q2.T59_43_2 Q2.hfix59_43_2 Q2.hinj59_43_2
      Q2.hcardT59_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_43_2 i) (Q2.hfix59_43_2 i) _)
      colCert_59_43_1.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_43_2 (hp : 2 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 2 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp)) T59_43
      hfix59_43 hinj59_43 hcardT59_43
      (fun i => conj_mem_of_fixedPoints _ _ (T59_43 i) (hfix59_43 i) _)
      ⟨59, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 2 hp) Q2.T59_43_2 Q2.hfix59_43_2 Q2.hinj59_43_2
      Q2.hcardT59_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_43_2 i) (Q2.hfix59_43_2 i) _)
      colCert_59_43_2.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_43_3 (hp : 3 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 3 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp)) T59_43
      hfix59_43 hinj59_43 hcardT59_43
      (fun i => conj_mem_of_fixedPoints _ _ (T59_43 i) (hfix59_43 i) _)
      ⟨59, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 3 hp) Q2.T59_43_2 Q2.hfix59_43_2 Q2.hinj59_43_2
      Q2.hcardT59_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_43_2 i) (Q2.hfix59_43_2 i) _)
      colCert_59_43_3.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_43_4 (hp : 4 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 4 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp)) T59_43
      hfix59_43 hinj59_43 hcardT59_43
      (fun i => conj_mem_of_fixedPoints _ _ (T59_43 i) (hfix59_43 i) _)
      ⟨59, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 4 hp) Q2.T59_43_2 Q2.hfix59_43_2 Q2.hinj59_43_2
      Q2.hcardT59_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_43_2 i) (Q2.hfix59_43_2 i) _)
      colCert_59_43_4.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_43_5 (hp : 5 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 5 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨59, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp)) T59_43
      hfix59_43 hinj59_43 hcardT59_43
      (fun i => conj_mem_of_fixedPoints _ _ (T59_43 i) (hfix59_43 i) _)
      ⟨59, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 5 hp) Q2.T59_43_2 Q2.hfix59_43_2 Q2.hinj59_43_2
      Q2.hcardT59_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_43_2 i) (Q2.hfix59_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨59, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T59_43 = colFn colCertDiv_59_43_5.D1 (m := 5) from colCertDiv_59_43_5.bind1,
    show colData2 (⟨59, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 5 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T59_43_2 = colFn colCertDiv_59_43_5.D2 (m := 5) from colCertDiv_59_43_5.bind2]
  rw [alnId_59 j hj]
  exact fastcode_of_div ⟨59, by decide⟩ _ _ _
    ((alnId_59 j hj) ▸ Q2.listedAt (⟨59, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨59, by decide⟩ : Fin 148) hj hq).1) colCertDiv_59_43_5_match


theorem leaf_59_43_10 (hp : 10 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 10 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨59, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp)) T59_43
      hfix59_43 hinj59_43 hcardT59_43
      (fun i => conj_mem_of_fixedPoints _ _ (T59_43 i) (hfix59_43 i) _)
      ⟨59, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 10 hp) Q2.T59_43_2 Q2.hfix59_43_2 Q2.hinj59_43_2
      Q2.hcardT59_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_43_2 i) (Q2.hfix59_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨59, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T59_43 = colFn colCertDiv_59_43_10.D1 (m := 5) from colCertDiv_59_43_10.bind1,
    show colData2 (⟨59, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 10 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T59_43_2 = colFn colCertDiv_59_43_10.D2 (m := 5) from colCertDiv_59_43_10.bind2]
  rw [alnId_59 j hj]
  exact fastcode_of_div ⟨59, by decide⟩ _ _ _
    ((alnId_59 j hj) ▸ Q2.listedAt (⟨59, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨59, by decide⟩ : Fin 148) hj hq).1) colCertDiv_59_43_10_match


theorem leaf_59_43_15 (hp : 15 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 15 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨59, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp)) T59_43
      hfix59_43 hinj59_43 hcardT59_43
      (fun i => conj_mem_of_fixedPoints _ _ (T59_43 i) (hfix59_43 i) _)
      ⟨59, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 15 hp) Q2.T59_43_2 Q2.hfix59_43_2 Q2.hinj59_43_2
      Q2.hcardT59_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_43_2 i) (Q2.hfix59_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨59, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T59_43 = colFn colCertDiv_59_43_15.D1 (m := 5) from colCertDiv_59_43_15.bind1,
    show colData2 (⟨59, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 15 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T59_43_2 = colFn colCertDiv_59_43_15.D2 (m := 5) from colCertDiv_59_43_15.bind2]
  rw [alnId_59 j hj]
  exact fastcode_of_div ⟨59, by decide⟩ _ _ _
    ((alnId_59 j hj) ▸ Q2.listedAt (⟨59, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨59, by decide⟩ : Fin 148) hj hq).1) colCertDiv_59_43_15_match


theorem leaf_59_43_20 (hp : 20 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 20 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨59, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp)) T59_43
      hfix59_43 hinj59_43 hcardT59_43
      (fun i => conj_mem_of_fixedPoints _ _ (T59_43 i) (hfix59_43 i) _)
      ⟨59, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 20 hp) Q2.T59_43_2 Q2.hfix59_43_2 Q2.hinj59_43_2
      Q2.hcardT59_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_43_2 i) (Q2.hfix59_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨59, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T59_43 = colFn colCertDiv_59_43_20.D1 (m := 5) from colCertDiv_59_43_20.bind1,
    show colData2 (⟨59, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 20 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T59_43_2 = colFn colCertDiv_59_43_20.D2 (m := 5) from colCertDiv_59_43_20.bind2]
  rw [alnId_59 j hj]
  exact fastcode_of_div ⟨59, by decide⟩ _ _ _
    ((alnId_59 j hj) ▸ Q2.listedAt (⟨59, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨59, by decide⟩ : Fin 148) hj hq).1) colCertDiv_59_43_20_match


theorem leaf_59_48_0 (hp : 0 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 0 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp)) T59_48
      hfix59_48 hinj59_48 hcardT59_48
      (fun i => conj_mem_of_fixedPoints _ _ (T59_48 i) (hfix59_48 i) _)
      ⟨59, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 0 hp) Q2.T59_48_2 Q2.hfix59_48_2 Q2.hinj59_48_2
      Q2.hcardT59_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_48_2 i) (Q2.hfix59_48_2 i) _)
      colCert_59_48_0.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_48_1 (hp : 1 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 1 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp)) T59_48
      hfix59_48 hinj59_48 hcardT59_48
      (fun i => conj_mem_of_fixedPoints _ _ (T59_48 i) (hfix59_48 i) _)
      ⟨59, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 1 hp) Q2.T59_48_2 Q2.hfix59_48_2 Q2.hinj59_48_2
      Q2.hcardT59_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_48_2 i) (Q2.hfix59_48_2 i) _)
      colCert_59_48_1.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_48_2 (hp : 2 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 2 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp)) T59_48
      hfix59_48 hinj59_48 hcardT59_48
      (fun i => conj_mem_of_fixedPoints _ _ (T59_48 i) (hfix59_48 i) _)
      ⟨59, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 2 hp) Q2.T59_48_2 Q2.hfix59_48_2 Q2.hinj59_48_2
      Q2.hcardT59_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_48_2 i) (Q2.hfix59_48_2 i) _)
      colCert_59_48_2.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_48_3 (hp : 3 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 3 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp)) T59_48
      hfix59_48 hinj59_48 hcardT59_48
      (fun i => conj_mem_of_fixedPoints _ _ (T59_48 i) (hfix59_48 i) _)
      ⟨59, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 3 hp) Q2.T59_48_2 Q2.hfix59_48_2 Q2.hinj59_48_2
      Q2.hcardT59_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_48_2 i) (Q2.hfix59_48_2 i) _)
      colCert_59_48_3.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_48_4 (hp : 4 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 4 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp)) T59_48
      hfix59_48 hinj59_48 hcardT59_48
      (fun i => conj_mem_of_fixedPoints _ _ (T59_48 i) (hfix59_48 i) _)
      ⟨59, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 4 hp) Q2.T59_48_2 Q2.hfix59_48_2 Q2.hinj59_48_2
      Q2.hcardT59_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_48_2 i) (Q2.hfix59_48_2 i) _)
      colCert_59_48_4.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_48_5 (hp : 5 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 5 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨59, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp)) T59_48
      hfix59_48 hinj59_48 hcardT59_48
      (fun i => conj_mem_of_fixedPoints _ _ (T59_48 i) (hfix59_48 i) _)
      ⟨59, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 5 hp) Q2.T59_48_2 Q2.hfix59_48_2 Q2.hinj59_48_2
      Q2.hcardT59_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_48_2 i) (Q2.hfix59_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨59, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T59_48 = colFn colCertDiv_59_48_5.D1 (m := 5) from colCertDiv_59_48_5.bind1,
    show colData2 (⟨59, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 5 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T59_48_2 = colFn colCertDiv_59_48_5.D2 (m := 5) from colCertDiv_59_48_5.bind2]
  rw [alnId_59 j hj]
  exact fastcode_of_div ⟨59, by decide⟩ _ _ _
    ((alnId_59 j hj) ▸ Q2.listedAt (⟨59, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨59, by decide⟩ : Fin 148) hj hq).1) colCertDiv_59_48_5_match


theorem leaf_59_48_10 (hp : 10 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 10 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨59, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp)) T59_48
      hfix59_48 hinj59_48 hcardT59_48
      (fun i => conj_mem_of_fixedPoints _ _ (T59_48 i) (hfix59_48 i) _)
      ⟨59, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 10 hp) Q2.T59_48_2 Q2.hfix59_48_2 Q2.hinj59_48_2
      Q2.hcardT59_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_48_2 i) (Q2.hfix59_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨59, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T59_48 = colFn colCertDiv_59_48_10.D1 (m := 5) from colCertDiv_59_48_10.bind1,
    show colData2 (⟨59, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 10 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T59_48_2 = colFn colCertDiv_59_48_10.D2 (m := 5) from colCertDiv_59_48_10.bind2]
  rw [alnId_59 j hj]
  exact fastcode_of_div ⟨59, by decide⟩ _ _ _
    ((alnId_59 j hj) ▸ Q2.listedAt (⟨59, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨59, by decide⟩ : Fin 148) hj hq).1) colCertDiv_59_48_10_match


theorem leaf_59_48_15 (hp : 15 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 15 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨59, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp)) T59_48
      hfix59_48 hinj59_48 hcardT59_48
      (fun i => conj_mem_of_fixedPoints _ _ (T59_48 i) (hfix59_48 i) _)
      ⟨59, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 15 hp) Q2.T59_48_2 Q2.hfix59_48_2 Q2.hinj59_48_2
      Q2.hcardT59_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_48_2 i) (Q2.hfix59_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨59, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T59_48 = colFn colCertDiv_59_48_15.D1 (m := 5) from colCertDiv_59_48_15.bind1,
    show colData2 (⟨59, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 15 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T59_48_2 = colFn colCertDiv_59_48_15.D2 (m := 5) from colCertDiv_59_48_15.bind2]
  rw [alnId_59 j hj]
  exact fastcode_of_div ⟨59, by decide⟩ _ _ _
    ((alnId_59 j hj) ▸ Q2.listedAt (⟨59, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨59, by decide⟩ : Fin 148) hj hq).1) colCertDiv_59_48_15_match


theorem leaf_59_48_20 (hp : 20 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 20 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨59, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp)) T59_48
      hfix59_48 hinj59_48 hcardT59_48
      (fun i => conj_mem_of_fixedPoints _ _ (T59_48 i) (hfix59_48 i) _)
      ⟨59, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 20 hp) Q2.T59_48_2 Q2.hfix59_48_2 Q2.hinj59_48_2
      Q2.hcardT59_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_48_2 i) (Q2.hfix59_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨59, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T59_48 = colFn colCertDiv_59_48_20.D1 (m := 5) from colCertDiv_59_48_20.bind1,
    show colData2 (⟨59, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 20 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T59_48_2 = colFn colCertDiv_59_48_20.D2 (m := 5) from colCertDiv_59_48_20.bind2]
  rw [alnId_59 j hj]
  exact fastcode_of_div ⟨59, by decide⟩ _ _ _
    ((alnId_59 j hj) ▸ Q2.listedAt (⟨59, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨59, by decide⟩ : Fin 148) hj hq).1) colCertDiv_59_48_20_match


theorem leaf_59_59_0 (hp : 0 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 0 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 0 (transLenTr ⟨59, by decide⟩ 0 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 0 (transLenTr ⟨59, by decide⟩ 0 hp)) T59_59
      hfix59_59 hinj59_59 hcardT59_59
      (fun i => conj_mem_of_fixedPoints _ _ (T59_59 i) (hfix59_59 i) _)
      ⟨59, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 0 hp) Q2.T59_59_2 Q2.hfix59_59_2 Q2.hinj59_59_2
      Q2.hcardT59_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_59_2 i) (Q2.hfix59_59_2 i) _)
      colCert_59_59_0.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_59_1 (hp : 1 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 1 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 1 (transLenTr ⟨59, by decide⟩ 1 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 1 (transLenTr ⟨59, by decide⟩ 1 hp)) T59_59
      hfix59_59 hinj59_59 hcardT59_59
      (fun i => conj_mem_of_fixedPoints _ _ (T59_59 i) (hfix59_59 i) _)
      ⟨59, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 1 hp) Q2.T59_59_2 Q2.hfix59_59_2 Q2.hinj59_59_2
      Q2.hcardT59_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_59_2 i) (Q2.hfix59_59_2 i) _)
      colCert_59_59_1.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_59_2 (hp : 2 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 2 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 2 (transLenTr ⟨59, by decide⟩ 2 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 2 (transLenTr ⟨59, by decide⟩ 2 hp)) T59_59
      hfix59_59 hinj59_59 hcardT59_59
      (fun i => conj_mem_of_fixedPoints _ _ (T59_59 i) (hfix59_59 i) _)
      ⟨59, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 2 hp) Q2.T59_59_2 Q2.hfix59_59_2 Q2.hinj59_59_2
      Q2.hcardT59_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_59_2 i) (Q2.hfix59_59_2 i) _)
      colCert_59_59_2.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_59_3 (hp : 3 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 3 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 3 (transLenTr ⟨59, by decide⟩ 3 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 3 (transLenTr ⟨59, by decide⟩ 3 hp)) T59_59
      hfix59_59 hinj59_59 hcardT59_59
      (fun i => conj_mem_of_fixedPoints _ _ (T59_59 i) (hfix59_59 i) _)
      ⟨59, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 3 hp) Q2.T59_59_2 Q2.hfix59_59_2 Q2.hinj59_59_2
      Q2.hcardT59_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_59_2 i) (Q2.hfix59_59_2 i) _)
      colCert_59_59_3.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_59_4 (hp : 4 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 4 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 4 (transLenTr ⟨59, by decide⟩ 4 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 4 (transLenTr ⟨59, by decide⟩ 4 hp)) T59_59
      hfix59_59 hinj59_59 hcardT59_59
      (fun i => conj_mem_of_fixedPoints _ _ (T59_59 i) (hfix59_59 i) _)
      ⟨59, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 4 hp) Q2.T59_59_2 Q2.hfix59_59_2 Q2.hinj59_59_2
      Q2.hcardT59_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_59_2 i) (Q2.hfix59_59_2 i) _)
      colCert_59_59_4.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_59_5 (hp : 5 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 5 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 5 (transLenTr ⟨59, by decide⟩ 5 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 5 (transLenTr ⟨59, by decide⟩ 5 hp)) T59_59
      hfix59_59 hinj59_59 hcardT59_59
      (fun i => conj_mem_of_fixedPoints _ _ (T59_59 i) (hfix59_59 i) _)
      ⟨59, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 5 hp) Q2.T59_59_2 Q2.hfix59_59_2 Q2.hinj59_59_2
      Q2.hcardT59_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_59_2 i) (Q2.hfix59_59_2 i) _)
      colCert_59_59_5.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_59_6 (hp : 6 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 6 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 6 (transLenTr ⟨59, by decide⟩ 6 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 6 (transLenTr ⟨59, by decide⟩ 6 hp)) T59_59
      hfix59_59 hinj59_59 hcardT59_59
      (fun i => conj_mem_of_fixedPoints _ _ (T59_59 i) (hfix59_59 i) _)
      ⟨59, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 6 hp) Q2.T59_59_2 Q2.hfix59_59_2 Q2.hinj59_59_2
      Q2.hcardT59_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_59_2 i) (Q2.hfix59_59_2 i) _)
      colCert_59_59_6.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_59_7 (hp : 7 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 7 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 7 (transLenTr ⟨59, by decide⟩ 7 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 7 (transLenTr ⟨59, by decide⟩ 7 hp)) T59_59
      hfix59_59 hinj59_59 hcardT59_59
      (fun i => conj_mem_of_fixedPoints _ _ (T59_59 i) (hfix59_59 i) _)
      ⟨59, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 7 hp) Q2.T59_59_2 Q2.hfix59_59_2 Q2.hinj59_59_2
      Q2.hcardT59_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_59_2 i) (Q2.hfix59_59_2 i) _)
      colCert_59_59_7.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_59_8 (hp : 8 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 8 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 8 (transLenTr ⟨59, by decide⟩ 8 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 8 (transLenTr ⟨59, by decide⟩ 8 hp)) T59_59
      hfix59_59 hinj59_59 hcardT59_59
      (fun i => conj_mem_of_fixedPoints _ _ (T59_59 i) (hfix59_59 i) _)
      ⟨59, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 8 hp) Q2.T59_59_2 Q2.hfix59_59_2 Q2.hinj59_59_2
      Q2.hcardT59_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_59_2 i) (Q2.hfix59_59_2 i) _)
      colCert_59_59_8.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_59_9 (hp : 9 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 9 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 9 (transLenTr ⟨59, by decide⟩ 9 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 9 (transLenTr ⟨59, by decide⟩ 9 hp)) T59_59
      hfix59_59 hinj59_59 hcardT59_59
      (fun i => conj_mem_of_fixedPoints _ _ (T59_59 i) (hfix59_59 i) _)
      ⟨59, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 9 hp) Q2.T59_59_2 Q2.hfix59_59_2 Q2.hinj59_59_2
      Q2.hcardT59_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_59_2 i) (Q2.hfix59_59_2 i) _)
      colCert_59_59_9.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_59_10 (hp : 10 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 10 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 10 (transLenTr ⟨59, by decide⟩ 10 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 10 (transLenTr ⟨59, by decide⟩ 10 hp)) T59_59
      hfix59_59 hinj59_59 hcardT59_59
      (fun i => conj_mem_of_fixedPoints _ _ (T59_59 i) (hfix59_59 i) _)
      ⟨59, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 10 hp) Q2.T59_59_2 Q2.hfix59_59_2 Q2.hinj59_59_2
      Q2.hcardT59_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_59_2 i) (Q2.hfix59_59_2 i) _)
      colCert_59_59_10.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_59_11 (hp : 11 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 11 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 11 (transLenTr ⟨59, by decide⟩ 11 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 11 (transLenTr ⟨59, by decide⟩ 11 hp)) T59_59
      hfix59_59 hinj59_59 hcardT59_59
      (fun i => conj_mem_of_fixedPoints _ _ (T59_59 i) (hfix59_59 i) _)
      ⟨59, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 11 hp) Q2.T59_59_2 Q2.hfix59_59_2 Q2.hinj59_59_2
      Q2.hcardT59_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_59_2 i) (Q2.hfix59_59_2 i) _)
      colCert_59_59_11.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_59_12 (hp : 12 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 12 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 12 (transLenTr ⟨59, by decide⟩ 12 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 12 (transLenTr ⟨59, by decide⟩ 12 hp)) T59_59
      hfix59_59 hinj59_59 hcardT59_59
      (fun i => conj_mem_of_fixedPoints _ _ (T59_59 i) (hfix59_59 i) _)
      ⟨59, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 12 hp) Q2.T59_59_2 Q2.hfix59_59_2 Q2.hinj59_59_2
      Q2.hcardT59_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_59_2 i) (Q2.hfix59_59_2 i) _)
      colCert_59_59_12.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_59_13 (hp : 13 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 13 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 13 (transLenTr ⟨59, by decide⟩ 13 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 13 (transLenTr ⟨59, by decide⟩ 13 hp)) T59_59
      hfix59_59 hinj59_59 hcardT59_59
      (fun i => conj_mem_of_fixedPoints _ _ (T59_59 i) (hfix59_59 i) _)
      ⟨59, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 13 hp) Q2.T59_59_2 Q2.hfix59_59_2 Q2.hinj59_59_2
      Q2.hcardT59_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_59_2 i) (Q2.hfix59_59_2 i) _)
      colCert_59_59_13.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_59_14 (hp : 14 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 14 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 14 (transLenTr ⟨59, by decide⟩ 14 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 14 (transLenTr ⟨59, by decide⟩ 14 hp)) T59_59
      hfix59_59 hinj59_59 hcardT59_59
      (fun i => conj_mem_of_fixedPoints _ _ (T59_59 i) (hfix59_59 i) _)
      ⟨59, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 14 hp) Q2.T59_59_2 Q2.hfix59_59_2 Q2.hinj59_59_2
      Q2.hcardT59_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_59_2 i) (Q2.hfix59_59_2 i) _)
      colCert_59_59_14.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_59_15 (hp : 15 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 15 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 15 (transLenTr ⟨59, by decide⟩ 15 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 15 (transLenTr ⟨59, by decide⟩ 15 hp)) T59_59
      hfix59_59 hinj59_59 hcardT59_59
      (fun i => conj_mem_of_fixedPoints _ _ (T59_59 i) (hfix59_59 i) _)
      ⟨59, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 15 hp) Q2.T59_59_2 Q2.hfix59_59_2 Q2.hinj59_59_2
      Q2.hcardT59_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_59_2 i) (Q2.hfix59_59_2 i) _)
      colCert_59_59_15.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_59_16 (hp : 16 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 16 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 16 (transLenTr ⟨59, by decide⟩ 16 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 16 (transLenTr ⟨59, by decide⟩ 16 hp)) T59_59
      hfix59_59 hinj59_59 hcardT59_59
      (fun i => conj_mem_of_fixedPoints _ _ (T59_59 i) (hfix59_59 i) _)
      ⟨59, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 16 hp) Q2.T59_59_2 Q2.hfix59_59_2 Q2.hinj59_59_2
      Q2.hcardT59_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_59_2 i) (Q2.hfix59_59_2 i) _)
      colCert_59_59_16.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_59_17 (hp : 17 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 17 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 17 (transLenTr ⟨59, by decide⟩ 17 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 17 (transLenTr ⟨59, by decide⟩ 17 hp)) T59_59
      hfix59_59 hinj59_59 hcardT59_59
      (fun i => conj_mem_of_fixedPoints _ _ (T59_59 i) (hfix59_59 i) _)
      ⟨59, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 17 hp) Q2.T59_59_2 Q2.hfix59_59_2 Q2.hinj59_59_2
      Q2.hcardT59_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_59_2 i) (Q2.hfix59_59_2 i) _)
      colCert_59_59_17.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_59_18 (hp : 18 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 18 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 18 (transLenTr ⟨59, by decide⟩ 18 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 18 (transLenTr ⟨59, by decide⟩ 18 hp)) T59_59
      hfix59_59 hinj59_59 hcardT59_59
      (fun i => conj_mem_of_fixedPoints _ _ (T59_59 i) (hfix59_59 i) _)
      ⟨59, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 18 hp) Q2.T59_59_2 Q2.hfix59_59_2 Q2.hinj59_59_2
      Q2.hcardT59_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_59_2 i) (Q2.hfix59_59_2 i) _)
      colCert_59_59_18.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_59_19 (hp : 19 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 19 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 19 (transLenTr ⟨59, by decide⟩ 19 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 19 (transLenTr ⟨59, by decide⟩ 19 hp)) T59_59
      hfix59_59 hinj59_59 hcardT59_59
      (fun i => conj_mem_of_fixedPoints _ _ (T59_59 i) (hfix59_59 i) _)
      ⟨59, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 19 hp) Q2.T59_59_2 Q2.hfix59_59_2 Q2.hinj59_59_2
      Q2.hcardT59_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_59_2 i) (Q2.hfix59_59_2 i) _)
      colCert_59_59_19.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_59_20 (hp : 20 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 20 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 20 (transLenTr ⟨59, by decide⟩ 20 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 20 (transLenTr ⟨59, by decide⟩ 20 hp)) T59_59
      hfix59_59 hinj59_59 hcardT59_59
      (fun i => conj_mem_of_fixedPoints _ _ (T59_59 i) (hfix59_59 i) _)
      ⟨59, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 20 hp) Q2.T59_59_2 Q2.hfix59_59_2 Q2.hinj59_59_2
      Q2.hcardT59_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_59_2 i) (Q2.hfix59_59_2 i) _)
      colCert_59_59_20.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_59_21 (hp : 21 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 21 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 21 (transLenTr ⟨59, by decide⟩ 21 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 21 (transLenTr ⟨59, by decide⟩ 21 hp)) T59_59
      hfix59_59 hinj59_59 hcardT59_59
      (fun i => conj_mem_of_fixedPoints _ _ (T59_59 i) (hfix59_59 i) _)
      ⟨59, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 21 hp) Q2.T59_59_2 Q2.hfix59_59_2 Q2.hinj59_59_2
      Q2.hcardT59_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_59_2 i) (Q2.hfix59_59_2 i) _)
      colCert_59_59_21.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_59_22 (hp : 22 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 22 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 22 (transLenTr ⟨59, by decide⟩ 22 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 22 (transLenTr ⟨59, by decide⟩ 22 hp)) T59_59
      hfix59_59 hinj59_59 hcardT59_59
      (fun i => conj_mem_of_fixedPoints _ _ (T59_59 i) (hfix59_59 i) _)
      ⟨59, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 22 hp) Q2.T59_59_2 Q2.hfix59_59_2 Q2.hinj59_59_2
      Q2.hcardT59_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_59_2 i) (Q2.hfix59_59_2 i) _)
      colCert_59_59_22.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_59_23 (hp : 23 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 23 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 23 (transLenTr ⟨59, by decide⟩ 23 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 23 (transLenTr ⟨59, by decide⟩ 23 hp)) T59_59
      hfix59_59 hinj59_59 hcardT59_59
      (fun i => conj_mem_of_fixedPoints _ _ (T59_59 i) (hfix59_59 i) _)
      ⟨59, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 23 hp) Q2.T59_59_2 Q2.hfix59_59_2 Q2.hinj59_59_2
      Q2.hcardT59_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_59_2 i) (Q2.hfix59_59_2 i) _)
      colCert_59_59_23.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_59_59_24 (hp : 24 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 59 []).length)
    (hq : (normIsRep.getD 59 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 24 hp)
        (rowE2 (⟨59, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 24 (transLenTr ⟨59, by decide⟩ 24 hp))
        (rowE1 (⟨59, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨59, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨59, by decide⟩ (listedAt ⟨59, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 24 (transLenTr ⟨59, by decide⟩ 24 hp)) T59_59
      hfix59_59 hinj59_59 hcardT59_59
      (fun i => conj_mem_of_fixedPoints _ _ (T59_59 i) (hfix59_59 i) _)
      ⟨59, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨59, by decide⟩ (Q2.listedAt ⟨59, by decide⟩
        (alnCheck_rep ⟨59, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 24 hp) Q2.T59_59_2 Q2.hfix59_59_2 Q2.hinj59_59_2
      Q2.hcardT59_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T59_59_2 i) (Q2.hfix59_59_2 i) _)
      colCert_59_59_24.hD ?_).symm
  rw [alnId_59 j hj]


theorem leaf_60_9_0 (hp : 0 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 0 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp)) T60_9
      hfix60_9 hinj60_9 hcardT60_9
      (fun i => conj_mem_of_fixedPoints _ _ (T60_9 i) (hfix60_9 i) _)
      ⟨60, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 0 hp) Q2.T60_9_2 Q2.hfix60_9_2 Q2.hinj60_9_2
      Q2.hcardT60_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_9_2 i) (Q2.hfix60_9_2 i) _)
      colCert_60_9_0.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_9_1 (hp : 1 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 1 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp)) T60_9
      hfix60_9 hinj60_9 hcardT60_9
      (fun i => conj_mem_of_fixedPoints _ _ (T60_9 i) (hfix60_9 i) _)
      ⟨60, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 1 hp) Q2.T60_9_2 Q2.hfix60_9_2 Q2.hinj60_9_2
      Q2.hcardT60_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_9_2 i) (Q2.hfix60_9_2 i) _)
      colCert_60_9_1.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_9_2 (hp : 2 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 2 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp)) T60_9
      hfix60_9 hinj60_9 hcardT60_9
      (fun i => conj_mem_of_fixedPoints _ _ (T60_9 i) (hfix60_9 i) _)
      ⟨60, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 2 hp) Q2.T60_9_2 Q2.hfix60_9_2 Q2.hinj60_9_2
      Q2.hcardT60_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_9_2 i) (Q2.hfix60_9_2 i) _)
      colCert_60_9_2.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_9_3 (hp : 3 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 3 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp)) T60_9
      hfix60_9 hinj60_9 hcardT60_9
      (fun i => conj_mem_of_fixedPoints _ _ (T60_9 i) (hfix60_9 i) _)
      ⟨60, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 3 hp) Q2.T60_9_2 Q2.hfix60_9_2 Q2.hinj60_9_2
      Q2.hcardT60_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_9_2 i) (Q2.hfix60_9_2 i) _)
      colCert_60_9_3.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_9_4 (hp : 4 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 4 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp)) T60_9
      hfix60_9 hinj60_9 hcardT60_9
      (fun i => conj_mem_of_fixedPoints _ _ (T60_9 i) (hfix60_9 i) _)
      ⟨60, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 4 hp) Q2.T60_9_2 Q2.hfix60_9_2 Q2.hinj60_9_2
      Q2.hcardT60_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_9_2 i) (Q2.hfix60_9_2 i) _)
      colCert_60_9_4.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T60_12
      hfix60_12 hinj60_12 hcardT60_12
      (fun i => conj_mem_of_fixedPoints _ _ (T60_12 i) (hfix60_12 i) _)
      ⟨60, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T60_12_2 Q2.hfix60_12_2 Q2.hinj60_12_2
      Q2.hcardT60_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_12_2 i) (Q2.hfix60_12_2 i) _)
      colCert_60_12_0.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T60_12
      hfix60_12 hinj60_12 hcardT60_12
      (fun i => conj_mem_of_fixedPoints _ _ (T60_12 i) (hfix60_12 i) _)
      ⟨60, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T60_12_2 Q2.hfix60_12_2 Q2.hinj60_12_2
      Q2.hcardT60_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_12_2 i) (Q2.hfix60_12_2 i) _)
      colCert_60_12_1.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T60_12
      hfix60_12 hinj60_12 hcardT60_12
      (fun i => conj_mem_of_fixedPoints _ _ (T60_12 i) (hfix60_12 i) _)
      ⟨60, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T60_12_2 Q2.hfix60_12_2 Q2.hinj60_12_2
      Q2.hcardT60_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_12_2 i) (Q2.hfix60_12_2 i) _)
      colCert_60_12_2.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T60_12
      hfix60_12 hinj60_12 hcardT60_12
      (fun i => conj_mem_of_fixedPoints _ _ (T60_12 i) (hfix60_12 i) _)
      ⟨60, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T60_12_2 Q2.hfix60_12_2 Q2.hinj60_12_2
      Q2.hcardT60_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_12_2 i) (Q2.hfix60_12_2 i) _)
      colCert_60_12_3.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T60_12
      hfix60_12 hinj60_12 hcardT60_12
      (fun i => conj_mem_of_fixedPoints _ _ (T60_12 i) (hfix60_12 i) _)
      ⟨60, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T60_12_2 Q2.hfix60_12_2 Q2.hinj60_12_2
      Q2.hcardT60_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_12_2 i) (Q2.hfix60_12_2 i) _)
      colCert_60_12_4.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_27_0 (hp : 0 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 0 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp)) T60_27
      hfix60_27 hinj60_27 hcardT60_27
      (fun i => conj_mem_of_fixedPoints _ _ (T60_27 i) (hfix60_27 i) _)
      ⟨60, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 0 hp) Q2.T60_27_2 Q2.hfix60_27_2 Q2.hinj60_27_2
      Q2.hcardT60_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_27_2 i) (Q2.hfix60_27_2 i) _)
      colCert_60_27_0.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_27_1 (hp : 1 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 1 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp)) T60_27
      hfix60_27 hinj60_27 hcardT60_27
      (fun i => conj_mem_of_fixedPoints _ _ (T60_27 i) (hfix60_27 i) _)
      ⟨60, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 1 hp) Q2.T60_27_2 Q2.hfix60_27_2 Q2.hinj60_27_2
      Q2.hcardT60_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_27_2 i) (Q2.hfix60_27_2 i) _)
      colCert_60_27_1.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_27_2 (hp : 2 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 2 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp)) T60_27
      hfix60_27 hinj60_27 hcardT60_27
      (fun i => conj_mem_of_fixedPoints _ _ (T60_27 i) (hfix60_27 i) _)
      ⟨60, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 2 hp) Q2.T60_27_2 Q2.hfix60_27_2 Q2.hinj60_27_2
      Q2.hcardT60_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_27_2 i) (Q2.hfix60_27_2 i) _)
      colCert_60_27_2.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_27_3 (hp : 3 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 3 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp)) T60_27
      hfix60_27 hinj60_27 hcardT60_27
      (fun i => conj_mem_of_fixedPoints _ _ (T60_27 i) (hfix60_27 i) _)
      ⟨60, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 3 hp) Q2.T60_27_2 Q2.hfix60_27_2 Q2.hinj60_27_2
      Q2.hcardT60_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_27_2 i) (Q2.hfix60_27_2 i) _)
      colCert_60_27_3.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_27_4 (hp : 4 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 4 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp)) T60_27
      hfix60_27 hinj60_27 hcardT60_27
      (fun i => conj_mem_of_fixedPoints _ _ (T60_27 i) (hfix60_27 i) _)
      ⟨60, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 4 hp) Q2.T60_27_2 Q2.hfix60_27_2 Q2.hinj60_27_2
      Q2.hcardT60_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_27_2 i) (Q2.hfix60_27_2 i) _)
      colCert_60_27_4.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_27_5 (hp : 5 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 5 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp)) T60_27
      hfix60_27 hinj60_27 hcardT60_27
      (fun i => conj_mem_of_fixedPoints _ _ (T60_27 i) (hfix60_27 i) _)
      ⟨60, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 5 hp) Q2.T60_27_2 Q2.hfix60_27_2 Q2.hinj60_27_2
      Q2.hcardT60_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_27_2 i) (Q2.hfix60_27_2 i) _)
      colCert_60_27_5.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_27_10 (hp : 10 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 10 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp)) T60_27
      hfix60_27 hinj60_27 hcardT60_27
      (fun i => conj_mem_of_fixedPoints _ _ (T60_27 i) (hfix60_27 i) _)
      ⟨60, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 10 hp) Q2.T60_27_2 Q2.hfix60_27_2 Q2.hinj60_27_2
      Q2.hcardT60_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_27_2 i) (Q2.hfix60_27_2 i) _)
      colCert_60_27_10.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_27_15 (hp : 15 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 15 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp)) T60_27
      hfix60_27 hinj60_27 hcardT60_27
      (fun i => conj_mem_of_fixedPoints _ _ (T60_27 i) (hfix60_27 i) _)
      ⟨60, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 15 hp) Q2.T60_27_2 Q2.hfix60_27_2 Q2.hinj60_27_2
      Q2.hcardT60_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_27_2 i) (Q2.hfix60_27_2 i) _)
      colCert_60_27_15.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_27_20 (hp : 20 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 20 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp)) T60_27
      hfix60_27 hinj60_27 hcardT60_27
      (fun i => conj_mem_of_fixedPoints _ _ (T60_27 i) (hfix60_27 i) _)
      ⟨60, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 20 hp) Q2.T60_27_2 Q2.hfix60_27_2 Q2.hinj60_27_2
      Q2.hcardT60_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_27_2 i) (Q2.hfix60_27_2 i) _)
      colCert_60_27_20.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_29_0 (hp : 0 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 0 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp)) T60_29
      hfix60_29 hinj60_29 hcardT60_29
      (fun i => conj_mem_of_fixedPoints _ _ (T60_29 i) (hfix60_29 i) _)
      ⟨60, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 0 hp) Q2.T60_29_2 Q2.hfix60_29_2 Q2.hinj60_29_2
      Q2.hcardT60_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_29_2 i) (Q2.hfix60_29_2 i) _)
      colCert_60_29_0.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_29_1 (hp : 1 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 1 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp)) T60_29
      hfix60_29 hinj60_29 hcardT60_29
      (fun i => conj_mem_of_fixedPoints _ _ (T60_29 i) (hfix60_29 i) _)
      ⟨60, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 1 hp) Q2.T60_29_2 Q2.hfix60_29_2 Q2.hinj60_29_2
      Q2.hcardT60_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_29_2 i) (Q2.hfix60_29_2 i) _)
      colCert_60_29_1.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_29_2 (hp : 2 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 2 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp)) T60_29
      hfix60_29 hinj60_29 hcardT60_29
      (fun i => conj_mem_of_fixedPoints _ _ (T60_29 i) (hfix60_29 i) _)
      ⟨60, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 2 hp) Q2.T60_29_2 Q2.hfix60_29_2 Q2.hinj60_29_2
      Q2.hcardT60_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_29_2 i) (Q2.hfix60_29_2 i) _)
      colCert_60_29_2.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_29_3 (hp : 3 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 3 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp)) T60_29
      hfix60_29 hinj60_29 hcardT60_29
      (fun i => conj_mem_of_fixedPoints _ _ (T60_29 i) (hfix60_29 i) _)
      ⟨60, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 3 hp) Q2.T60_29_2 Q2.hfix60_29_2 Q2.hinj60_29_2
      Q2.hcardT60_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_29_2 i) (Q2.hfix60_29_2 i) _)
      colCert_60_29_3.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_29_4 (hp : 4 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 4 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp)) T60_29
      hfix60_29 hinj60_29 hcardT60_29
      (fun i => conj_mem_of_fixedPoints _ _ (T60_29 i) (hfix60_29 i) _)
      ⟨60, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 4 hp) Q2.T60_29_2 Q2.hfix60_29_2 Q2.hinj60_29_2
      Q2.hcardT60_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_29_2 i) (Q2.hfix60_29_2 i) _)
      colCert_60_29_4.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_29_5 (hp : 5 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 5 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp)) T60_29
      hfix60_29 hinj60_29 hcardT60_29
      (fun i => conj_mem_of_fixedPoints _ _ (T60_29 i) (hfix60_29 i) _)
      ⟨60, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 5 hp) Q2.T60_29_2 Q2.hfix60_29_2 Q2.hinj60_29_2
      Q2.hcardT60_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_29_2 i) (Q2.hfix60_29_2 i) _)
      colCert_60_29_5.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_29_10 (hp : 10 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 10 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp)) T60_29
      hfix60_29 hinj60_29 hcardT60_29
      (fun i => conj_mem_of_fixedPoints _ _ (T60_29 i) (hfix60_29 i) _)
      ⟨60, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 10 hp) Q2.T60_29_2 Q2.hfix60_29_2 Q2.hinj60_29_2
      Q2.hcardT60_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_29_2 i) (Q2.hfix60_29_2 i) _)
      colCert_60_29_10.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_29_15 (hp : 15 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 15 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp)) T60_29
      hfix60_29 hinj60_29 hcardT60_29
      (fun i => conj_mem_of_fixedPoints _ _ (T60_29 i) (hfix60_29 i) _)
      ⟨60, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 15 hp) Q2.T60_29_2 Q2.hfix60_29_2 Q2.hinj60_29_2
      Q2.hcardT60_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_29_2 i) (Q2.hfix60_29_2 i) _)
      colCert_60_29_15.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_29_20 (hp : 20 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 20 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp)) T60_29
      hfix60_29 hinj60_29 hcardT60_29
      (fun i => conj_mem_of_fixedPoints _ _ (T60_29 i) (hfix60_29 i) _)
      ⟨60, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 20 hp) Q2.T60_29_2 Q2.hfix60_29_2 Q2.hinj60_29_2
      Q2.hcardT60_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_29_2 i) (Q2.hfix60_29_2 i) _)
      colCert_60_29_20.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_34_0 (hp : 0 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 0 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp)) T60_34
      hfix60_34 hinj60_34 hcardT60_34
      (fun i => conj_mem_of_fixedPoints _ _ (T60_34 i) (hfix60_34 i) _)
      ⟨60, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 0 hp) Q2.T60_34_2 Q2.hfix60_34_2 Q2.hinj60_34_2
      Q2.hcardT60_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_34_2 i) (Q2.hfix60_34_2 i) _)
      colCert_60_34_0.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_34_1 (hp : 1 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 1 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp)) T60_34
      hfix60_34 hinj60_34 hcardT60_34
      (fun i => conj_mem_of_fixedPoints _ _ (T60_34 i) (hfix60_34 i) _)
      ⟨60, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 1 hp) Q2.T60_34_2 Q2.hfix60_34_2 Q2.hinj60_34_2
      Q2.hcardT60_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_34_2 i) (Q2.hfix60_34_2 i) _)
      colCert_60_34_1.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_34_2 (hp : 2 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 2 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp)) T60_34
      hfix60_34 hinj60_34 hcardT60_34
      (fun i => conj_mem_of_fixedPoints _ _ (T60_34 i) (hfix60_34 i) _)
      ⟨60, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 2 hp) Q2.T60_34_2 Q2.hfix60_34_2 Q2.hinj60_34_2
      Q2.hcardT60_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_34_2 i) (Q2.hfix60_34_2 i) _)
      colCert_60_34_2.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_34_3 (hp : 3 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 3 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp)) T60_34
      hfix60_34 hinj60_34 hcardT60_34
      (fun i => conj_mem_of_fixedPoints _ _ (T60_34 i) (hfix60_34 i) _)
      ⟨60, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 3 hp) Q2.T60_34_2 Q2.hfix60_34_2 Q2.hinj60_34_2
      Q2.hcardT60_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_34_2 i) (Q2.hfix60_34_2 i) _)
      colCert_60_34_3.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_34_4 (hp : 4 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 4 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp)) T60_34
      hfix60_34 hinj60_34 hcardT60_34
      (fun i => conj_mem_of_fixedPoints _ _ (T60_34 i) (hfix60_34 i) _)
      ⟨60, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 4 hp) Q2.T60_34_2 Q2.hfix60_34_2 Q2.hinj60_34_2
      Q2.hcardT60_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_34_2 i) (Q2.hfix60_34_2 i) _)
      colCert_60_34_4.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_34_5 (hp : 5 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 5 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp)) T60_34
      hfix60_34 hinj60_34 hcardT60_34
      (fun i => conj_mem_of_fixedPoints _ _ (T60_34 i) (hfix60_34 i) _)
      ⟨60, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 5 hp) Q2.T60_34_2 Q2.hfix60_34_2 Q2.hinj60_34_2
      Q2.hcardT60_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_34_2 i) (Q2.hfix60_34_2 i) _)
      colCert_60_34_5.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_34_10 (hp : 10 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 10 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp)) T60_34
      hfix60_34 hinj60_34 hcardT60_34
      (fun i => conj_mem_of_fixedPoints _ _ (T60_34 i) (hfix60_34 i) _)
      ⟨60, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 10 hp) Q2.T60_34_2 Q2.hfix60_34_2 Q2.hinj60_34_2
      Q2.hcardT60_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_34_2 i) (Q2.hfix60_34_2 i) _)
      colCert_60_34_10.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_34_15 (hp : 15 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 15 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp)) T60_34
      hfix60_34 hinj60_34 hcardT60_34
      (fun i => conj_mem_of_fixedPoints _ _ (T60_34 i) (hfix60_34 i) _)
      ⟨60, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 15 hp) Q2.T60_34_2 Q2.hfix60_34_2 Q2.hinj60_34_2
      Q2.hcardT60_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_34_2 i) (Q2.hfix60_34_2 i) _)
      colCert_60_34_15.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_34_20 (hp : 20 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 20 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp)) T60_34
      hfix60_34 hinj60_34 hcardT60_34
      (fun i => conj_mem_of_fixedPoints _ _ (T60_34 i) (hfix60_34 i) _)
      ⟨60, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 20 hp) Q2.T60_34_2 Q2.hfix60_34_2 Q2.hinj60_34_2
      Q2.hcardT60_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_34_2 i) (Q2.hfix60_34_2 i) _)
      colCert_60_34_20.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_39_0 (hp : 0 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 0 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp)) T60_39
      hfix60_39 hinj60_39 hcardT60_39
      (fun i => conj_mem_of_fixedPoints _ _ (T60_39 i) (hfix60_39 i) _)
      ⟨60, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 0 hp) Q2.T60_39_2 Q2.hfix60_39_2 Q2.hinj60_39_2
      Q2.hcardT60_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_39_2 i) (Q2.hfix60_39_2 i) _)
      colCert_60_39_0.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_39_1 (hp : 1 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 1 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp)) T60_39
      hfix60_39 hinj60_39 hcardT60_39
      (fun i => conj_mem_of_fixedPoints _ _ (T60_39 i) (hfix60_39 i) _)
      ⟨60, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 1 hp) Q2.T60_39_2 Q2.hfix60_39_2 Q2.hinj60_39_2
      Q2.hcardT60_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_39_2 i) (Q2.hfix60_39_2 i) _)
      colCert_60_39_1.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_39_2 (hp : 2 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 2 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp)) T60_39
      hfix60_39 hinj60_39 hcardT60_39
      (fun i => conj_mem_of_fixedPoints _ _ (T60_39 i) (hfix60_39 i) _)
      ⟨60, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 2 hp) Q2.T60_39_2 Q2.hfix60_39_2 Q2.hinj60_39_2
      Q2.hcardT60_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_39_2 i) (Q2.hfix60_39_2 i) _)
      colCert_60_39_2.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_39_3 (hp : 3 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 3 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp)) T60_39
      hfix60_39 hinj60_39 hcardT60_39
      (fun i => conj_mem_of_fixedPoints _ _ (T60_39 i) (hfix60_39 i) _)
      ⟨60, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 3 hp) Q2.T60_39_2 Q2.hfix60_39_2 Q2.hinj60_39_2
      Q2.hcardT60_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_39_2 i) (Q2.hfix60_39_2 i) _)
      colCert_60_39_3.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_39_4 (hp : 4 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 4 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp)) T60_39
      hfix60_39 hinj60_39 hcardT60_39
      (fun i => conj_mem_of_fixedPoints _ _ (T60_39 i) (hfix60_39 i) _)
      ⟨60, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 4 hp) Q2.T60_39_2 Q2.hfix60_39_2 Q2.hinj60_39_2
      Q2.hcardT60_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_39_2 i) (Q2.hfix60_39_2 i) _)
      colCert_60_39_4.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_39_5 (hp : 5 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 5 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp)) T60_39
      hfix60_39 hinj60_39 hcardT60_39
      (fun i => conj_mem_of_fixedPoints _ _ (T60_39 i) (hfix60_39 i) _)
      ⟨60, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 5 hp) Q2.T60_39_2 Q2.hfix60_39_2 Q2.hinj60_39_2
      Q2.hcardT60_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_39_2 i) (Q2.hfix60_39_2 i) _)
      colCert_60_39_5.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_39_10 (hp : 10 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 10 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp)) T60_39
      hfix60_39 hinj60_39 hcardT60_39
      (fun i => conj_mem_of_fixedPoints _ _ (T60_39 i) (hfix60_39 i) _)
      ⟨60, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 10 hp) Q2.T60_39_2 Q2.hfix60_39_2 Q2.hinj60_39_2
      Q2.hcardT60_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_39_2 i) (Q2.hfix60_39_2 i) _)
      colCert_60_39_10.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_39_15 (hp : 15 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 15 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp)) T60_39
      hfix60_39 hinj60_39 hcardT60_39
      (fun i => conj_mem_of_fixedPoints _ _ (T60_39 i) (hfix60_39 i) _)
      ⟨60, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 15 hp) Q2.T60_39_2 Q2.hfix60_39_2 Q2.hinj60_39_2
      Q2.hcardT60_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_39_2 i) (Q2.hfix60_39_2 i) _)
      colCert_60_39_15.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_39_20 (hp : 20 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 20 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp)) T60_39
      hfix60_39 hinj60_39 hcardT60_39
      (fun i => conj_mem_of_fixedPoints _ _ (T60_39 i) (hfix60_39 i) _)
      ⟨60, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 20 hp) Q2.T60_39_2 Q2.hfix60_39_2 Q2.hinj60_39_2
      Q2.hcardT60_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_39_2 i) (Q2.hfix60_39_2 i) _)
      colCert_60_39_20.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_44_0 (hp : 0 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 0 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp)) T60_44
      hfix60_44 hinj60_44 hcardT60_44
      (fun i => conj_mem_of_fixedPoints _ _ (T60_44 i) (hfix60_44 i) _)
      ⟨60, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 0 hp) Q2.T60_44_2 Q2.hfix60_44_2 Q2.hinj60_44_2
      Q2.hcardT60_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_44_2 i) (Q2.hfix60_44_2 i) _)
      colCert_60_44_0.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_44_1 (hp : 1 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 1 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp)) T60_44
      hfix60_44 hinj60_44 hcardT60_44
      (fun i => conj_mem_of_fixedPoints _ _ (T60_44 i) (hfix60_44 i) _)
      ⟨60, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 1 hp) Q2.T60_44_2 Q2.hfix60_44_2 Q2.hinj60_44_2
      Q2.hcardT60_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_44_2 i) (Q2.hfix60_44_2 i) _)
      colCert_60_44_1.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_44_2 (hp : 2 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 2 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp)) T60_44
      hfix60_44 hinj60_44 hcardT60_44
      (fun i => conj_mem_of_fixedPoints _ _ (T60_44 i) (hfix60_44 i) _)
      ⟨60, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 2 hp) Q2.T60_44_2 Q2.hfix60_44_2 Q2.hinj60_44_2
      Q2.hcardT60_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_44_2 i) (Q2.hfix60_44_2 i) _)
      colCert_60_44_2.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_44_3 (hp : 3 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 3 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp)) T60_44
      hfix60_44 hinj60_44 hcardT60_44
      (fun i => conj_mem_of_fixedPoints _ _ (T60_44 i) (hfix60_44 i) _)
      ⟨60, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 3 hp) Q2.T60_44_2 Q2.hfix60_44_2 Q2.hinj60_44_2
      Q2.hcardT60_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_44_2 i) (Q2.hfix60_44_2 i) _)
      colCert_60_44_3.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_44_4 (hp : 4 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 4 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp)) T60_44
      hfix60_44 hinj60_44 hcardT60_44
      (fun i => conj_mem_of_fixedPoints _ _ (T60_44 i) (hfix60_44 i) _)
      ⟨60, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 4 hp) Q2.T60_44_2 Q2.hfix60_44_2 Q2.hinj60_44_2
      Q2.hcardT60_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_44_2 i) (Q2.hfix60_44_2 i) _)
      colCert_60_44_4.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_44_5 (hp : 5 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 5 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp)) T60_44
      hfix60_44 hinj60_44 hcardT60_44
      (fun i => conj_mem_of_fixedPoints _ _ (T60_44 i) (hfix60_44 i) _)
      ⟨60, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 5 hp) Q2.T60_44_2 Q2.hfix60_44_2 Q2.hinj60_44_2
      Q2.hcardT60_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_44_2 i) (Q2.hfix60_44_2 i) _)
      colCert_60_44_5.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_44_10 (hp : 10 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 10 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp)) T60_44
      hfix60_44 hinj60_44 hcardT60_44
      (fun i => conj_mem_of_fixedPoints _ _ (T60_44 i) (hfix60_44 i) _)
      ⟨60, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 10 hp) Q2.T60_44_2 Q2.hfix60_44_2 Q2.hinj60_44_2
      Q2.hcardT60_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_44_2 i) (Q2.hfix60_44_2 i) _)
      colCert_60_44_10.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_44_15 (hp : 15 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 15 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp)) T60_44
      hfix60_44 hinj60_44 hcardT60_44
      (fun i => conj_mem_of_fixedPoints _ _ (T60_44 i) (hfix60_44 i) _)
      ⟨60, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 15 hp) Q2.T60_44_2 Q2.hfix60_44_2 Q2.hinj60_44_2
      Q2.hcardT60_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_44_2 i) (Q2.hfix60_44_2 i) _)
      colCert_60_44_15.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_44_20 (hp : 20 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 20 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp)) T60_44
      hfix60_44 hinj60_44 hcardT60_44
      (fun i => conj_mem_of_fixedPoints _ _ (T60_44 i) (hfix60_44 i) _)
      ⟨60, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 20 hp) Q2.T60_44_2 Q2.hfix60_44_2 Q2.hinj60_44_2
      Q2.hcardT60_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_44_2 i) (Q2.hfix60_44_2 i) _)
      colCert_60_44_20.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_49_0 (hp : 0 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 0 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp)) T60_49
      hfix60_49 hinj60_49 hcardT60_49
      (fun i => conj_mem_of_fixedPoints _ _ (T60_49 i) (hfix60_49 i) _)
      ⟨60, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 0 hp) Q2.T60_49_2 Q2.hfix60_49_2 Q2.hinj60_49_2
      Q2.hcardT60_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_49_2 i) (Q2.hfix60_49_2 i) _)
      colCert_60_49_0.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_49_1 (hp : 1 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 1 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp)) T60_49
      hfix60_49 hinj60_49 hcardT60_49
      (fun i => conj_mem_of_fixedPoints _ _ (T60_49 i) (hfix60_49 i) _)
      ⟨60, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 1 hp) Q2.T60_49_2 Q2.hfix60_49_2 Q2.hinj60_49_2
      Q2.hcardT60_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_49_2 i) (Q2.hfix60_49_2 i) _)
      colCert_60_49_1.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_49_2 (hp : 2 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 2 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp)) T60_49
      hfix60_49 hinj60_49 hcardT60_49
      (fun i => conj_mem_of_fixedPoints _ _ (T60_49 i) (hfix60_49 i) _)
      ⟨60, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 2 hp) Q2.T60_49_2 Q2.hfix60_49_2 Q2.hinj60_49_2
      Q2.hcardT60_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_49_2 i) (Q2.hfix60_49_2 i) _)
      colCert_60_49_2.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_49_3 (hp : 3 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 3 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp)) T60_49
      hfix60_49 hinj60_49 hcardT60_49
      (fun i => conj_mem_of_fixedPoints _ _ (T60_49 i) (hfix60_49 i) _)
      ⟨60, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 3 hp) Q2.T60_49_2 Q2.hfix60_49_2 Q2.hinj60_49_2
      Q2.hcardT60_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_49_2 i) (Q2.hfix60_49_2 i) _)
      colCert_60_49_3.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_49_4 (hp : 4 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 4 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp)) T60_49
      hfix60_49 hinj60_49 hcardT60_49
      (fun i => conj_mem_of_fixedPoints _ _ (T60_49 i) (hfix60_49 i) _)
      ⟨60, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 4 hp) Q2.T60_49_2 Q2.hfix60_49_2 Q2.hinj60_49_2
      Q2.hcardT60_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_49_2 i) (Q2.hfix60_49_2 i) _)
      colCert_60_49_4.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_49_5 (hp : 5 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 5 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp)) T60_49
      hfix60_49 hinj60_49 hcardT60_49
      (fun i => conj_mem_of_fixedPoints _ _ (T60_49 i) (hfix60_49 i) _)
      ⟨60, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 5 hp) Q2.T60_49_2 Q2.hfix60_49_2 Q2.hinj60_49_2
      Q2.hcardT60_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_49_2 i) (Q2.hfix60_49_2 i) _)
      colCert_60_49_5.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_49_10 (hp : 10 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 10 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp)) T60_49
      hfix60_49 hinj60_49 hcardT60_49
      (fun i => conj_mem_of_fixedPoints _ _ (T60_49 i) (hfix60_49 i) _)
      ⟨60, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 10 hp) Q2.T60_49_2 Q2.hfix60_49_2 Q2.hinj60_49_2
      Q2.hcardT60_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_49_2 i) (Q2.hfix60_49_2 i) _)
      colCert_60_49_10.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_49_15 (hp : 15 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 15 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp)) T60_49
      hfix60_49 hinj60_49 hcardT60_49
      (fun i => conj_mem_of_fixedPoints _ _ (T60_49 i) (hfix60_49 i) _)
      ⟨60, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 15 hp) Q2.T60_49_2 Q2.hfix60_49_2 Q2.hinj60_49_2
      Q2.hcardT60_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_49_2 i) (Q2.hfix60_49_2 i) _)
      colCert_60_49_15.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_49_20 (hp : 20 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 20 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp)) T60_49
      hfix60_49 hinj60_49 hcardT60_49
      (fun i => conj_mem_of_fixedPoints _ _ (T60_49 i) (hfix60_49 i) _)
      ⟨60, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 20 hp) Q2.T60_49_2 Q2.hfix60_49_2 Q2.hinj60_49_2
      Q2.hcardT60_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_49_2 i) (Q2.hfix60_49_2 i) _)
      colCert_60_49_20.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_60_0 (hp : 0 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 0 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 0 (transLenTr ⟨60, by decide⟩ 0 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 0 (transLenTr ⟨60, by decide⟩ 0 hp)) T60_60
      hfix60_60 hinj60_60 hcardT60_60
      (fun i => conj_mem_of_fixedPoints _ _ (T60_60 i) (hfix60_60 i) _)
      ⟨60, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 0 hp) Q2.T60_60_2 Q2.hfix60_60_2 Q2.hinj60_60_2
      Q2.hcardT60_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_60_2 i) (Q2.hfix60_60_2 i) _)
      colCert_60_60_0.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_60_1 (hp : 1 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 1 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 1 (transLenTr ⟨60, by decide⟩ 1 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 1 (transLenTr ⟨60, by decide⟩ 1 hp)) T60_60
      hfix60_60 hinj60_60 hcardT60_60
      (fun i => conj_mem_of_fixedPoints _ _ (T60_60 i) (hfix60_60 i) _)
      ⟨60, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 1 hp) Q2.T60_60_2 Q2.hfix60_60_2 Q2.hinj60_60_2
      Q2.hcardT60_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_60_2 i) (Q2.hfix60_60_2 i) _)
      colCert_60_60_1.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_60_2 (hp : 2 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 2 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 2 (transLenTr ⟨60, by decide⟩ 2 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 2 (transLenTr ⟨60, by decide⟩ 2 hp)) T60_60
      hfix60_60 hinj60_60 hcardT60_60
      (fun i => conj_mem_of_fixedPoints _ _ (T60_60 i) (hfix60_60 i) _)
      ⟨60, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 2 hp) Q2.T60_60_2 Q2.hfix60_60_2 Q2.hinj60_60_2
      Q2.hcardT60_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_60_2 i) (Q2.hfix60_60_2 i) _)
      colCert_60_60_2.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_60_3 (hp : 3 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 3 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 3 (transLenTr ⟨60, by decide⟩ 3 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 3 (transLenTr ⟨60, by decide⟩ 3 hp)) T60_60
      hfix60_60 hinj60_60 hcardT60_60
      (fun i => conj_mem_of_fixedPoints _ _ (T60_60 i) (hfix60_60 i) _)
      ⟨60, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 3 hp) Q2.T60_60_2 Q2.hfix60_60_2 Q2.hinj60_60_2
      Q2.hcardT60_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_60_2 i) (Q2.hfix60_60_2 i) _)
      colCert_60_60_3.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_60_4 (hp : 4 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 4 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 4 (transLenTr ⟨60, by decide⟩ 4 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 4 (transLenTr ⟨60, by decide⟩ 4 hp)) T60_60
      hfix60_60 hinj60_60 hcardT60_60
      (fun i => conj_mem_of_fixedPoints _ _ (T60_60 i) (hfix60_60 i) _)
      ⟨60, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 4 hp) Q2.T60_60_2 Q2.hfix60_60_2 Q2.hinj60_60_2
      Q2.hcardT60_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_60_2 i) (Q2.hfix60_60_2 i) _)
      colCert_60_60_4.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_60_5 (hp : 5 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 5 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 5 (transLenTr ⟨60, by decide⟩ 5 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 5 (transLenTr ⟨60, by decide⟩ 5 hp)) T60_60
      hfix60_60 hinj60_60 hcardT60_60
      (fun i => conj_mem_of_fixedPoints _ _ (T60_60 i) (hfix60_60 i) _)
      ⟨60, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 5 hp) Q2.T60_60_2 Q2.hfix60_60_2 Q2.hinj60_60_2
      Q2.hcardT60_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_60_2 i) (Q2.hfix60_60_2 i) _)
      colCert_60_60_5.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_60_6 (hp : 6 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 6 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 6 (transLenTr ⟨60, by decide⟩ 6 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 6 (transLenTr ⟨60, by decide⟩ 6 hp)) T60_60
      hfix60_60 hinj60_60 hcardT60_60
      (fun i => conj_mem_of_fixedPoints _ _ (T60_60 i) (hfix60_60 i) _)
      ⟨60, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 6 hp) Q2.T60_60_2 Q2.hfix60_60_2 Q2.hinj60_60_2
      Q2.hcardT60_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_60_2 i) (Q2.hfix60_60_2 i) _)
      colCert_60_60_6.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_60_7 (hp : 7 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 7 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 7 (transLenTr ⟨60, by decide⟩ 7 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 7 (transLenTr ⟨60, by decide⟩ 7 hp)) T60_60
      hfix60_60 hinj60_60 hcardT60_60
      (fun i => conj_mem_of_fixedPoints _ _ (T60_60 i) (hfix60_60 i) _)
      ⟨60, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 7 hp) Q2.T60_60_2 Q2.hfix60_60_2 Q2.hinj60_60_2
      Q2.hcardT60_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_60_2 i) (Q2.hfix60_60_2 i) _)
      colCert_60_60_7.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_60_8 (hp : 8 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 8 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 8 (transLenTr ⟨60, by decide⟩ 8 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 8 (transLenTr ⟨60, by decide⟩ 8 hp)) T60_60
      hfix60_60 hinj60_60 hcardT60_60
      (fun i => conj_mem_of_fixedPoints _ _ (T60_60 i) (hfix60_60 i) _)
      ⟨60, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 8 hp) Q2.T60_60_2 Q2.hfix60_60_2 Q2.hinj60_60_2
      Q2.hcardT60_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_60_2 i) (Q2.hfix60_60_2 i) _)
      colCert_60_60_8.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_60_9 (hp : 9 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 9 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 9 (transLenTr ⟨60, by decide⟩ 9 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 9 (transLenTr ⟨60, by decide⟩ 9 hp)) T60_60
      hfix60_60 hinj60_60 hcardT60_60
      (fun i => conj_mem_of_fixedPoints _ _ (T60_60 i) (hfix60_60 i) _)
      ⟨60, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 9 hp) Q2.T60_60_2 Q2.hfix60_60_2 Q2.hinj60_60_2
      Q2.hcardT60_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_60_2 i) (Q2.hfix60_60_2 i) _)
      colCert_60_60_9.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_60_10 (hp : 10 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 10 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 10 (transLenTr ⟨60, by decide⟩ 10 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 10 (transLenTr ⟨60, by decide⟩ 10 hp)) T60_60
      hfix60_60 hinj60_60 hcardT60_60
      (fun i => conj_mem_of_fixedPoints _ _ (T60_60 i) (hfix60_60 i) _)
      ⟨60, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 10 hp) Q2.T60_60_2 Q2.hfix60_60_2 Q2.hinj60_60_2
      Q2.hcardT60_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_60_2 i) (Q2.hfix60_60_2 i) _)
      colCert_60_60_10.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_60_11 (hp : 11 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 11 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 11 (transLenTr ⟨60, by decide⟩ 11 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 11 (transLenTr ⟨60, by decide⟩ 11 hp)) T60_60
      hfix60_60 hinj60_60 hcardT60_60
      (fun i => conj_mem_of_fixedPoints _ _ (T60_60 i) (hfix60_60 i) _)
      ⟨60, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 11 hp) Q2.T60_60_2 Q2.hfix60_60_2 Q2.hinj60_60_2
      Q2.hcardT60_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_60_2 i) (Q2.hfix60_60_2 i) _)
      colCert_60_60_11.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_60_12 (hp : 12 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 12 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 12 (transLenTr ⟨60, by decide⟩ 12 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 12 (transLenTr ⟨60, by decide⟩ 12 hp)) T60_60
      hfix60_60 hinj60_60 hcardT60_60
      (fun i => conj_mem_of_fixedPoints _ _ (T60_60 i) (hfix60_60 i) _)
      ⟨60, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 12 hp) Q2.T60_60_2 Q2.hfix60_60_2 Q2.hinj60_60_2
      Q2.hcardT60_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_60_2 i) (Q2.hfix60_60_2 i) _)
      colCert_60_60_12.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_60_13 (hp : 13 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 13 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 13 (transLenTr ⟨60, by decide⟩ 13 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 13 (transLenTr ⟨60, by decide⟩ 13 hp)) T60_60
      hfix60_60 hinj60_60 hcardT60_60
      (fun i => conj_mem_of_fixedPoints _ _ (T60_60 i) (hfix60_60 i) _)
      ⟨60, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 13 hp) Q2.T60_60_2 Q2.hfix60_60_2 Q2.hinj60_60_2
      Q2.hcardT60_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_60_2 i) (Q2.hfix60_60_2 i) _)
      colCert_60_60_13.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_60_14 (hp : 14 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 14 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 14 (transLenTr ⟨60, by decide⟩ 14 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 14 (transLenTr ⟨60, by decide⟩ 14 hp)) T60_60
      hfix60_60 hinj60_60 hcardT60_60
      (fun i => conj_mem_of_fixedPoints _ _ (T60_60 i) (hfix60_60 i) _)
      ⟨60, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 14 hp) Q2.T60_60_2 Q2.hfix60_60_2 Q2.hinj60_60_2
      Q2.hcardT60_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_60_2 i) (Q2.hfix60_60_2 i) _)
      colCert_60_60_14.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_60_15 (hp : 15 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 15 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 15 (transLenTr ⟨60, by decide⟩ 15 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 15 (transLenTr ⟨60, by decide⟩ 15 hp)) T60_60
      hfix60_60 hinj60_60 hcardT60_60
      (fun i => conj_mem_of_fixedPoints _ _ (T60_60 i) (hfix60_60 i) _)
      ⟨60, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 15 hp) Q2.T60_60_2 Q2.hfix60_60_2 Q2.hinj60_60_2
      Q2.hcardT60_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_60_2 i) (Q2.hfix60_60_2 i) _)
      colCert_60_60_15.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_60_16 (hp : 16 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 16 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 16 (transLenTr ⟨60, by decide⟩ 16 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 16 (transLenTr ⟨60, by decide⟩ 16 hp)) T60_60
      hfix60_60 hinj60_60 hcardT60_60
      (fun i => conj_mem_of_fixedPoints _ _ (T60_60 i) (hfix60_60 i) _)
      ⟨60, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 16 hp) Q2.T60_60_2 Q2.hfix60_60_2 Q2.hinj60_60_2
      Q2.hcardT60_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_60_2 i) (Q2.hfix60_60_2 i) _)
      colCert_60_60_16.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_60_17 (hp : 17 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 17 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 17 (transLenTr ⟨60, by decide⟩ 17 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 17 (transLenTr ⟨60, by decide⟩ 17 hp)) T60_60
      hfix60_60 hinj60_60 hcardT60_60
      (fun i => conj_mem_of_fixedPoints _ _ (T60_60 i) (hfix60_60 i) _)
      ⟨60, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 17 hp) Q2.T60_60_2 Q2.hfix60_60_2 Q2.hinj60_60_2
      Q2.hcardT60_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_60_2 i) (Q2.hfix60_60_2 i) _)
      colCert_60_60_17.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_60_18 (hp : 18 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 18 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 18 (transLenTr ⟨60, by decide⟩ 18 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 18 (transLenTr ⟨60, by decide⟩ 18 hp)) T60_60
      hfix60_60 hinj60_60 hcardT60_60
      (fun i => conj_mem_of_fixedPoints _ _ (T60_60 i) (hfix60_60 i) _)
      ⟨60, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 18 hp) Q2.T60_60_2 Q2.hfix60_60_2 Q2.hinj60_60_2
      Q2.hcardT60_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_60_2 i) (Q2.hfix60_60_2 i) _)
      colCert_60_60_18.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_60_19 (hp : 19 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 19 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 19 (transLenTr ⟨60, by decide⟩ 19 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 19 (transLenTr ⟨60, by decide⟩ 19 hp)) T60_60
      hfix60_60 hinj60_60 hcardT60_60
      (fun i => conj_mem_of_fixedPoints _ _ (T60_60 i) (hfix60_60 i) _)
      ⟨60, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 19 hp) Q2.T60_60_2 Q2.hfix60_60_2 Q2.hinj60_60_2
      Q2.hcardT60_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_60_2 i) (Q2.hfix60_60_2 i) _)
      colCert_60_60_19.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_60_20 (hp : 20 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 20 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 20 (transLenTr ⟨60, by decide⟩ 20 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 20 (transLenTr ⟨60, by decide⟩ 20 hp)) T60_60
      hfix60_60 hinj60_60 hcardT60_60
      (fun i => conj_mem_of_fixedPoints _ _ (T60_60 i) (hfix60_60 i) _)
      ⟨60, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 20 hp) Q2.T60_60_2 Q2.hfix60_60_2 Q2.hinj60_60_2
      Q2.hcardT60_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_60_2 i) (Q2.hfix60_60_2 i) _)
      colCert_60_60_20.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_60_21 (hp : 21 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 21 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 21 (transLenTr ⟨60, by decide⟩ 21 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 21 (transLenTr ⟨60, by decide⟩ 21 hp)) T60_60
      hfix60_60 hinj60_60 hcardT60_60
      (fun i => conj_mem_of_fixedPoints _ _ (T60_60 i) (hfix60_60 i) _)
      ⟨60, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 21 hp) Q2.T60_60_2 Q2.hfix60_60_2 Q2.hinj60_60_2
      Q2.hcardT60_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_60_2 i) (Q2.hfix60_60_2 i) _)
      colCert_60_60_21.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_60_22 (hp : 22 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 22 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 22 (transLenTr ⟨60, by decide⟩ 22 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 22 (transLenTr ⟨60, by decide⟩ 22 hp)) T60_60
      hfix60_60 hinj60_60 hcardT60_60
      (fun i => conj_mem_of_fixedPoints _ _ (T60_60 i) (hfix60_60 i) _)
      ⟨60, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 22 hp) Q2.T60_60_2 Q2.hfix60_60_2 Q2.hinj60_60_2
      Q2.hcardT60_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_60_2 i) (Q2.hfix60_60_2 i) _)
      colCert_60_60_22.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_60_23 (hp : 23 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 23 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 23 (transLenTr ⟨60, by decide⟩ 23 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 23 (transLenTr ⟨60, by decide⟩ 23 hp)) T60_60
      hfix60_60 hinj60_60 hcardT60_60
      (fun i => conj_mem_of_fixedPoints _ _ (T60_60 i) (hfix60_60 i) _)
      ⟨60, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 23 hp) Q2.T60_60_2 Q2.hfix60_60_2 Q2.hinj60_60_2
      Q2.hcardT60_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_60_2 i) (Q2.hfix60_60_2 i) _)
      colCert_60_60_23.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_60_60_24 (hp : 24 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 60 []).length)
    (hq : (normIsRep.getD 60 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 24 hp)
        (rowE2 (⟨60, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 24 (transLenTr ⟨60, by decide⟩ 24 hp))
        (rowE1 (⟨60, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨60, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨60, by decide⟩ (listedAt ⟨60, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 24 (transLenTr ⟨60, by decide⟩ 24 hp)) T60_60
      hfix60_60 hinj60_60 hcardT60_60
      (fun i => conj_mem_of_fixedPoints _ _ (T60_60 i) (hfix60_60 i) _)
      ⟨60, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨60, by decide⟩ (Q2.listedAt ⟨60, by decide⟩
        (alnCheck_rep ⟨60, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 24 hp) Q2.T60_60_2 Q2.hfix60_60_2 Q2.hinj60_60_2
      Q2.hcardT60_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T60_60_2 i) (Q2.hfix60_60_2 i) _)
      colCert_60_60_24.hD ?_).symm
  rw [alnId_60 j hj]


theorem leaf_61_1_0 (hp : 0 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 0 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp)) T61_1
      hfix61_1 hinj61_1 hcardT61_1
      (fun i => conj_mem_of_fixedPoints _ _ (T61_1 i) (hfix61_1 i) _)
      ⟨61, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 0 hp) Q2.T61_1_2 Q2.hfix61_1_2 Q2.hinj61_1_2
      Q2.hcardT61_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_1_2 i) (Q2.hfix61_1_2 i) _)
      colCert_61_1_0.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_1_1 (hp : 1 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 1 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp)) T61_1
      hfix61_1 hinj61_1 hcardT61_1
      (fun i => conj_mem_of_fixedPoints _ _ (T61_1 i) (hfix61_1 i) _)
      ⟨61, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 1 hp) Q2.T61_1_2 Q2.hfix61_1_2 Q2.hinj61_1_2
      Q2.hcardT61_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_1_2 i) (Q2.hfix61_1_2 i) _)
      colCert_61_1_1.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_1_2 (hp : 2 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 2 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp)) T61_1
      hfix61_1 hinj61_1 hcardT61_1
      (fun i => conj_mem_of_fixedPoints _ _ (T61_1 i) (hfix61_1 i) _)
      ⟨61, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 2 hp) Q2.T61_1_2 Q2.hfix61_1_2 Q2.hinj61_1_2
      Q2.hcardT61_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_1_2 i) (Q2.hfix61_1_2 i) _)
      colCert_61_1_2.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_1_3 (hp : 3 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 3 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp)) T61_1
      hfix61_1 hinj61_1 hcardT61_1
      (fun i => conj_mem_of_fixedPoints _ _ (T61_1 i) (hfix61_1 i) _)
      ⟨61, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 3 hp) Q2.T61_1_2 Q2.hfix61_1_2 Q2.hinj61_1_2
      Q2.hcardT61_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_1_2 i) (Q2.hfix61_1_2 i) _)
      colCert_61_1_3.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_1_4 (hp : 4 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 4 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp)) T61_1
      hfix61_1 hinj61_1 hcardT61_1
      (fun i => conj_mem_of_fixedPoints _ _ (T61_1 i) (hfix61_1 i) _)
      ⟨61, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 4 hp) Q2.T61_1_2 Q2.hfix61_1_2 Q2.hinj61_1_2
      Q2.hcardT61_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_1_2 i) (Q2.hfix61_1_2 i) _)
      colCert_61_1_4.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T61_12
      hfix61_12 hinj61_12 hcardT61_12
      (fun i => conj_mem_of_fixedPoints _ _ (T61_12 i) (hfix61_12 i) _)
      ⟨61, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T61_12_2 Q2.hfix61_12_2 Q2.hinj61_12_2
      Q2.hcardT61_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_12_2 i) (Q2.hfix61_12_2 i) _)
      colCert_61_12_0.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T61_12
      hfix61_12 hinj61_12 hcardT61_12
      (fun i => conj_mem_of_fixedPoints _ _ (T61_12 i) (hfix61_12 i) _)
      ⟨61, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T61_12_2 Q2.hfix61_12_2 Q2.hinj61_12_2
      Q2.hcardT61_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_12_2 i) (Q2.hfix61_12_2 i) _)
      colCert_61_12_1.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T61_12
      hfix61_12 hinj61_12 hcardT61_12
      (fun i => conj_mem_of_fixedPoints _ _ (T61_12 i) (hfix61_12 i) _)
      ⟨61, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T61_12_2 Q2.hfix61_12_2 Q2.hinj61_12_2
      Q2.hcardT61_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_12_2 i) (Q2.hfix61_12_2 i) _)
      colCert_61_12_2.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T61_12
      hfix61_12 hinj61_12 hcardT61_12
      (fun i => conj_mem_of_fixedPoints _ _ (T61_12 i) (hfix61_12 i) _)
      ⟨61, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T61_12_2 Q2.hfix61_12_2 Q2.hinj61_12_2
      Q2.hcardT61_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_12_2 i) (Q2.hfix61_12_2 i) _)
      colCert_61_12_3.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T61_12
      hfix61_12 hinj61_12 hcardT61_12
      (fun i => conj_mem_of_fixedPoints _ _ (T61_12 i) (hfix61_12 i) _)
      ⟨61, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T61_12_2 Q2.hfix61_12_2 Q2.hinj61_12_2
      Q2.hcardT61_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_12_2 i) (Q2.hfix61_12_2 i) _)
      colCert_61_12_4.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_19_0 (hp : 0 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 0 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp)) T61_19
      hfix61_19 hinj61_19 hcardT61_19
      (fun i => conj_mem_of_fixedPoints _ _ (T61_19 i) (hfix61_19 i) _)
      ⟨61, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 0 hp) Q2.T61_19_2 Q2.hfix61_19_2 Q2.hinj61_19_2
      Q2.hcardT61_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_19_2 i) (Q2.hfix61_19_2 i) _)
      colCert_61_19_0.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_19_1 (hp : 1 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 1 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp)) T61_19
      hfix61_19 hinj61_19 hcardT61_19
      (fun i => conj_mem_of_fixedPoints _ _ (T61_19 i) (hfix61_19 i) _)
      ⟨61, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 1 hp) Q2.T61_19_2 Q2.hfix61_19_2 Q2.hinj61_19_2
      Q2.hcardT61_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_19_2 i) (Q2.hfix61_19_2 i) _)
      colCert_61_19_1.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_19_2 (hp : 2 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 2 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp)) T61_19
      hfix61_19 hinj61_19 hcardT61_19
      (fun i => conj_mem_of_fixedPoints _ _ (T61_19 i) (hfix61_19 i) _)
      ⟨61, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 2 hp) Q2.T61_19_2 Q2.hfix61_19_2 Q2.hinj61_19_2
      Q2.hcardT61_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_19_2 i) (Q2.hfix61_19_2 i) _)
      colCert_61_19_2.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_19_3 (hp : 3 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 3 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp)) T61_19
      hfix61_19 hinj61_19 hcardT61_19
      (fun i => conj_mem_of_fixedPoints _ _ (T61_19 i) (hfix61_19 i) _)
      ⟨61, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 3 hp) Q2.T61_19_2 Q2.hfix61_19_2 Q2.hinj61_19_2
      Q2.hcardT61_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_19_2 i) (Q2.hfix61_19_2 i) _)
      colCert_61_19_3.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_19_4 (hp : 4 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 4 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp)) T61_19
      hfix61_19 hinj61_19 hcardT61_19
      (fun i => conj_mem_of_fixedPoints _ _ (T61_19 i) (hfix61_19 i) _)
      ⟨61, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 4 hp) Q2.T61_19_2 Q2.hfix61_19_2 Q2.hinj61_19_2
      Q2.hcardT61_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_19_2 i) (Q2.hfix61_19_2 i) _)
      colCert_61_19_4.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_19_5 (hp : 5 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 5 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp)) T61_19
      hfix61_19 hinj61_19 hcardT61_19
      (fun i => conj_mem_of_fixedPoints _ _ (T61_19 i) (hfix61_19 i) _)
      ⟨61, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 5 hp) Q2.T61_19_2 Q2.hfix61_19_2 Q2.hinj61_19_2
      Q2.hcardT61_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_19_2 i) (Q2.hfix61_19_2 i) _)
      colCert_61_19_5.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_19_10 (hp : 10 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 10 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp)) T61_19
      hfix61_19 hinj61_19 hcardT61_19
      (fun i => conj_mem_of_fixedPoints _ _ (T61_19 i) (hfix61_19 i) _)
      ⟨61, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 10 hp) Q2.T61_19_2 Q2.hfix61_19_2 Q2.hinj61_19_2
      Q2.hcardT61_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_19_2 i) (Q2.hfix61_19_2 i) _)
      colCert_61_19_10.hD ?_).symm
  rw [alnId_61 j hj]


end LeanDring.P5Presentation
