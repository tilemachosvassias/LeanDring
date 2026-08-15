/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C015
import LeanDring.P5.Data.ColCdd.C016
import LeanDring.P5.Data.ColRestCheap.C070
import LeanDring.P5.Data.ColRestCheap.C071
import LeanDring.P5.Data.ColRestCheap.C072
import LeanDring.P5.Data.ColRestCheap.C073
import LeanDring.P5.Data.ColRestCheap.C074
import LeanDring.P5.Data.EntryK.C035
import LeanDring.P5.Data.EntryK.C036
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C019
import LeanDring.P5.Data.SpeciesDiv.C020

/-! # Stage-5 leaves, chunk 37 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_132_97_1 (hp : 1 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 1 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 1 (transLenTr ⟨97, by decide⟩ 1 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 1 (transLenTr ⟨97, by decide⟩ 1 hp)) T132_97
      hfix132_97 hinj132_97 hcardT132_97
      (fun i => conj_mem_of_fixedPoints _ _ (T132_97 i) (hfix132_97 i) _)
      ⟨132, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 1 hp) Q2.T132_97_2 Q2.hfix132_97_2 Q2.hinj132_97_2
      Q2.hcardT132_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_97_2 i) (Q2.hfix132_97_2 i) _)
      colCert_132_97_1.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_97_2 (hp : 2 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 2 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 2 (transLenTr ⟨97, by decide⟩ 2 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 2 (transLenTr ⟨97, by decide⟩ 2 hp)) T132_97
      hfix132_97 hinj132_97 hcardT132_97
      (fun i => conj_mem_of_fixedPoints _ _ (T132_97 i) (hfix132_97 i) _)
      ⟨132, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 2 hp) Q2.T132_97_2 Q2.hfix132_97_2 Q2.hinj132_97_2
      Q2.hcardT132_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_97_2 i) (Q2.hfix132_97_2 i) _)
      colCert_132_97_2.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_97_3 (hp : 3 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 3 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 3 (transLenTr ⟨97, by decide⟩ 3 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 3 (transLenTr ⟨97, by decide⟩ 3 hp)) T132_97
      hfix132_97 hinj132_97 hcardT132_97
      (fun i => conj_mem_of_fixedPoints _ _ (T132_97 i) (hfix132_97 i) _)
      ⟨132, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 3 hp) Q2.T132_97_2 Q2.hfix132_97_2 Q2.hinj132_97_2
      Q2.hcardT132_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_97_2 i) (Q2.hfix132_97_2 i) _)
      colCert_132_97_3.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_97_4 (hp : 4 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 4 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 4 (transLenTr ⟨97, by decide⟩ 4 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 4 (transLenTr ⟨97, by decide⟩ 4 hp)) T132_97
      hfix132_97 hinj132_97 hcardT132_97
      (fun i => conj_mem_of_fixedPoints _ _ (T132_97 i) (hfix132_97 i) _)
      ⟨132, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 4 hp) Q2.T132_97_2 Q2.hfix132_97_2 Q2.hinj132_97_2
      Q2.hcardT132_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_97_2 i) (Q2.hfix132_97_2 i) _)
      colCert_132_97_4.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_97_5 (hp : 5 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 5 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 5 (transLenTr ⟨97, by decide⟩ 5 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 5 (transLenTr ⟨97, by decide⟩ 5 hp)) T132_97
      hfix132_97 hinj132_97 hcardT132_97
      (fun i => conj_mem_of_fixedPoints _ _ (T132_97 i) (hfix132_97 i) _)
      ⟨132, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 5 hp) Q2.T132_97_2 Q2.hfix132_97_2 Q2.hinj132_97_2
      Q2.hcardT132_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_97_2 i) (Q2.hfix132_97_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨97, by decide⟩ 5 (transLenTr ⟨97, by decide⟩ 5 hp) : ↥(reps ⟨97, by decide⟩)) : Coordinate 1)
        T132_97 = colFn colCertDiv_132_97_5.D1 (m := 5) from colCertDiv_132_97_5.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨97, by decide⟩ 5 hp : ↥(Q2.reps ⟨97, by decide⟩)) : Coordinate 2)
        Q2.T132_97_2 = colFn colCertDiv_132_97_5.D2 (m := 5) from colCertDiv_132_97_5.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_97_5_match


theorem leaf_132_97_10 (hp : 10 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 10 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 10 (transLenTr ⟨97, by decide⟩ 10 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 10 (transLenTr ⟨97, by decide⟩ 10 hp)) T132_97
      hfix132_97 hinj132_97 hcardT132_97
      (fun i => conj_mem_of_fixedPoints _ _ (T132_97 i) (hfix132_97 i) _)
      ⟨132, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 10 hp) Q2.T132_97_2 Q2.hfix132_97_2 Q2.hinj132_97_2
      Q2.hcardT132_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_97_2 i) (Q2.hfix132_97_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨97, by decide⟩ 10 (transLenTr ⟨97, by decide⟩ 10 hp) : ↥(reps ⟨97, by decide⟩)) : Coordinate 1)
        T132_97 = colFn colCertDiv_132_97_10.D1 (m := 5) from colCertDiv_132_97_10.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨97, by decide⟩ 10 hp : ↥(Q2.reps ⟨97, by decide⟩)) : Coordinate 2)
        Q2.T132_97_2 = colFn colCertDiv_132_97_10.D2 (m := 5) from colCertDiv_132_97_10.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_97_10_match


theorem leaf_132_97_15 (hp : 15 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 15 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 15 (transLenTr ⟨97, by decide⟩ 15 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 15 (transLenTr ⟨97, by decide⟩ 15 hp)) T132_97
      hfix132_97 hinj132_97 hcardT132_97
      (fun i => conj_mem_of_fixedPoints _ _ (T132_97 i) (hfix132_97 i) _)
      ⟨132, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 15 hp) Q2.T132_97_2 Q2.hfix132_97_2 Q2.hinj132_97_2
      Q2.hcardT132_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_97_2 i) (Q2.hfix132_97_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨97, by decide⟩ 15 (transLenTr ⟨97, by decide⟩ 15 hp) : ↥(reps ⟨97, by decide⟩)) : Coordinate 1)
        T132_97 = colFn colCertDiv_132_97_15.D1 (m := 5) from colCertDiv_132_97_15.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨97, by decide⟩ 15 hp : ↥(Q2.reps ⟨97, by decide⟩)) : Coordinate 2)
        Q2.T132_97_2 = colFn colCertDiv_132_97_15.D2 (m := 5) from colCertDiv_132_97_15.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_97_15_match


theorem leaf_132_97_20 (hp : 20 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 20 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 20 (transLenTr ⟨97, by decide⟩ 20 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 20 (transLenTr ⟨97, by decide⟩ 20 hp)) T132_97
      hfix132_97 hinj132_97 hcardT132_97
      (fun i => conj_mem_of_fixedPoints _ _ (T132_97 i) (hfix132_97 i) _)
      ⟨132, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 20 hp) Q2.T132_97_2 Q2.hfix132_97_2 Q2.hinj132_97_2
      Q2.hcardT132_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_97_2 i) (Q2.hfix132_97_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨97, by decide⟩ 20 (transLenTr ⟨97, by decide⟩ 20 hp) : ↥(reps ⟨97, by decide⟩)) : Coordinate 1)
        T132_97 = colFn colCertDiv_132_97_20.D1 (m := 5) from colCertDiv_132_97_20.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨97, by decide⟩ 20 hp : ↥(Q2.reps ⟨97, by decide⟩)) : Coordinate 2)
        Q2.T132_97_2 = colFn colCertDiv_132_97_20.D2 (m := 5) from colCertDiv_132_97_20.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_97_20_match


theorem leaf_132_100_0 (hp : 0 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 0 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 0 (transLenTr ⟨100, by decide⟩ 0 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 0 (transLenTr ⟨100, by decide⟩ 0 hp)) T132_100
      hfix132_100 hinj132_100 hcardT132_100
      (fun i => conj_mem_of_fixedPoints _ _ (T132_100 i) (hfix132_100 i) _)
      ⟨132, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 0 hp) Q2.T132_100_2 Q2.hfix132_100_2 Q2.hinj132_100_2
      Q2.hcardT132_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_100_2 i) (Q2.hfix132_100_2 i) _)
      colCert_132_100_0.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_100_1 (hp : 1 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 1 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 1 (transLenTr ⟨100, by decide⟩ 1 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 1 (transLenTr ⟨100, by decide⟩ 1 hp)) T132_100
      hfix132_100 hinj132_100 hcardT132_100
      (fun i => conj_mem_of_fixedPoints _ _ (T132_100 i) (hfix132_100 i) _)
      ⟨132, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 1 hp) Q2.T132_100_2 Q2.hfix132_100_2 Q2.hinj132_100_2
      Q2.hcardT132_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_100_2 i) (Q2.hfix132_100_2 i) _)
      colCert_132_100_1.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_100_2 (hp : 2 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 2 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 2 (transLenTr ⟨100, by decide⟩ 2 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 2 (transLenTr ⟨100, by decide⟩ 2 hp)) T132_100
      hfix132_100 hinj132_100 hcardT132_100
      (fun i => conj_mem_of_fixedPoints _ _ (T132_100 i) (hfix132_100 i) _)
      ⟨132, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 2 hp) Q2.T132_100_2 Q2.hfix132_100_2 Q2.hinj132_100_2
      Q2.hcardT132_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_100_2 i) (Q2.hfix132_100_2 i) _)
      colCert_132_100_2.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_100_3 (hp : 3 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 3 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 3 (transLenTr ⟨100, by decide⟩ 3 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 3 (transLenTr ⟨100, by decide⟩ 3 hp)) T132_100
      hfix132_100 hinj132_100 hcardT132_100
      (fun i => conj_mem_of_fixedPoints _ _ (T132_100 i) (hfix132_100 i) _)
      ⟨132, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 3 hp) Q2.T132_100_2 Q2.hfix132_100_2 Q2.hinj132_100_2
      Q2.hcardT132_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_100_2 i) (Q2.hfix132_100_2 i) _)
      colCert_132_100_3.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_100_4 (hp : 4 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 4 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 4 (transLenTr ⟨100, by decide⟩ 4 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 4 (transLenTr ⟨100, by decide⟩ 4 hp)) T132_100
      hfix132_100 hinj132_100 hcardT132_100
      (fun i => conj_mem_of_fixedPoints _ _ (T132_100 i) (hfix132_100 i) _)
      ⟨132, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 4 hp) Q2.T132_100_2 Q2.hfix132_100_2 Q2.hinj132_100_2
      Q2.hcardT132_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_100_2 i) (Q2.hfix132_100_2 i) _)
      colCert_132_100_4.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_100_5 (hp : 5 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 5 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 5 (transLenTr ⟨100, by decide⟩ 5 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 5 (transLenTr ⟨100, by decide⟩ 5 hp)) T132_100
      hfix132_100 hinj132_100 hcardT132_100
      (fun i => conj_mem_of_fixedPoints _ _ (T132_100 i) (hfix132_100 i) _)
      ⟨132, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 5 hp) Q2.T132_100_2 Q2.hfix132_100_2 Q2.hinj132_100_2
      Q2.hcardT132_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_100_2 i) (Q2.hfix132_100_2 i) _)
      colCert_132_100_5.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_100_10 (hp : 10 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 10 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 10 (transLenTr ⟨100, by decide⟩ 10 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 10 (transLenTr ⟨100, by decide⟩ 10 hp)) T132_100
      hfix132_100 hinj132_100 hcardT132_100
      (fun i => conj_mem_of_fixedPoints _ _ (T132_100 i) (hfix132_100 i) _)
      ⟨132, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 10 hp) Q2.T132_100_2 Q2.hfix132_100_2 Q2.hinj132_100_2
      Q2.hcardT132_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_100_2 i) (Q2.hfix132_100_2 i) _)
      colCert_132_100_10.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_100_15 (hp : 15 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 15 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 15 (transLenTr ⟨100, by decide⟩ 15 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 15 (transLenTr ⟨100, by decide⟩ 15 hp)) T132_100
      hfix132_100 hinj132_100 hcardT132_100
      (fun i => conj_mem_of_fixedPoints _ _ (T132_100 i) (hfix132_100 i) _)
      ⟨132, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 15 hp) Q2.T132_100_2 Q2.hfix132_100_2 Q2.hinj132_100_2
      Q2.hcardT132_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_100_2 i) (Q2.hfix132_100_2 i) _)
      colCert_132_100_15.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_100_20 (hp : 20 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 20 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 20 (transLenTr ⟨100, by decide⟩ 20 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 20 (transLenTr ⟨100, by decide⟩ 20 hp)) T132_100
      hfix132_100 hinj132_100 hcardT132_100
      (fun i => conj_mem_of_fixedPoints _ _ (T132_100 i) (hfix132_100 i) _)
      ⟨132, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 20 hp) Q2.T132_100_2 Q2.hfix132_100_2 Q2.hinj132_100_2
      Q2.hcardT132_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_100_2 i) (Q2.hfix132_100_2 i) _)
      colCert_132_100_20.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_100_25 (hp : 25 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 25 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 25 (transLenTr ⟨100, by decide⟩ 25 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 25 (transLenTr ⟨100, by decide⟩ 25 hp)) T132_100
      hfix132_100 hinj132_100 hcardT132_100
      (fun i => conj_mem_of_fixedPoints _ _ (T132_100 i) (hfix132_100 i) _)
      ⟨132, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 25 hp) Q2.T132_100_2 Q2.hfix132_100_2 Q2.hinj132_100_2
      Q2.hcardT132_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_100_2 i) (Q2.hfix132_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 25 (transLenTr ⟨100, by decide⟩ 25 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T132_100 = colFn colCertDiv_132_100_25.D1 (m := 5) from colCertDiv_132_100_25.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 25 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T132_100_2 = colFn colCertDiv_132_100_25.D2 (m := 5) from colCertDiv_132_100_25.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_100_25_match


theorem leaf_132_100_50 (hp : 50 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 50 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 50 (transLenTr ⟨100, by decide⟩ 50 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 50 (transLenTr ⟨100, by decide⟩ 50 hp)) T132_100
      hfix132_100 hinj132_100 hcardT132_100
      (fun i => conj_mem_of_fixedPoints _ _ (T132_100 i) (hfix132_100 i) _)
      ⟨132, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 50 hp) Q2.T132_100_2 Q2.hfix132_100_2 Q2.hinj132_100_2
      Q2.hcardT132_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_100_2 i) (Q2.hfix132_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 50 (transLenTr ⟨100, by decide⟩ 50 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T132_100 = colFn colCertDiv_132_100_50.D1 (m := 5) from colCertDiv_132_100_50.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 50 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T132_100_2 = colFn colCertDiv_132_100_50.D2 (m := 5) from colCertDiv_132_100_50.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_100_50_match


theorem leaf_132_100_75 (hp : 75 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 75 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 75 (transLenTr ⟨100, by decide⟩ 75 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 75 (transLenTr ⟨100, by decide⟩ 75 hp)) T132_100
      hfix132_100 hinj132_100 hcardT132_100
      (fun i => conj_mem_of_fixedPoints _ _ (T132_100 i) (hfix132_100 i) _)
      ⟨132, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 75 hp) Q2.T132_100_2 Q2.hfix132_100_2 Q2.hinj132_100_2
      Q2.hcardT132_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_100_2 i) (Q2.hfix132_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 75 (transLenTr ⟨100, by decide⟩ 75 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T132_100 = colFn colCertDiv_132_100_75.D1 (m := 5) from colCertDiv_132_100_75.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 75 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T132_100_2 = colFn colCertDiv_132_100_75.D2 (m := 5) from colCertDiv_132_100_75.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_100_75_match


theorem leaf_132_100_100 (hp : 100 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 100 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 100 (transLenTr ⟨100, by decide⟩ 100 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 100 (transLenTr ⟨100, by decide⟩ 100 hp)) T132_100
      hfix132_100 hinj132_100 hcardT132_100
      (fun i => conj_mem_of_fixedPoints _ _ (T132_100 i) (hfix132_100 i) _)
      ⟨132, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 100 hp) Q2.T132_100_2 Q2.hfix132_100_2 Q2.hinj132_100_2
      Q2.hcardT132_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_100_2 i) (Q2.hfix132_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 100 (transLenTr ⟨100, by decide⟩ 100 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T132_100 = colFn colCertDiv_132_100_100.D1 (m := 5) from colCertDiv_132_100_100.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 100 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T132_100_2 = colFn colCertDiv_132_100_100.D2 (m := 5) from colCertDiv_132_100_100.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_100_100_match


theorem leaf_132_109_0 (hp : 0 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 0 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 0 (transLenTr ⟨109, by decide⟩ 0 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 0 (transLenTr ⟨109, by decide⟩ 0 hp)) T132_109
      hfix132_109 hinj132_109 hcardT132_109
      (fun i => conj_mem_of_fixedPoints _ _ (T132_109 i) (hfix132_109 i) _)
      ⟨132, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 0 hp) Q2.T132_109_2 Q2.hfix132_109_2 Q2.hinj132_109_2
      Q2.hcardT132_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_109_2 i) (Q2.hfix132_109_2 i) _)
      colCert_132_109_0.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_109_1 (hp : 1 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 1 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 1 (transLenTr ⟨109, by decide⟩ 1 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 1 (transLenTr ⟨109, by decide⟩ 1 hp)) T132_109
      hfix132_109 hinj132_109 hcardT132_109
      (fun i => conj_mem_of_fixedPoints _ _ (T132_109 i) (hfix132_109 i) _)
      ⟨132, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 1 hp) Q2.T132_109_2 Q2.hfix132_109_2 Q2.hinj132_109_2
      Q2.hcardT132_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_109_2 i) (Q2.hfix132_109_2 i) _)
      colCert_132_109_1.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_109_2 (hp : 2 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 2 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 2 (transLenTr ⟨109, by decide⟩ 2 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 2 (transLenTr ⟨109, by decide⟩ 2 hp)) T132_109
      hfix132_109 hinj132_109 hcardT132_109
      (fun i => conj_mem_of_fixedPoints _ _ (T132_109 i) (hfix132_109 i) _)
      ⟨132, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 2 hp) Q2.T132_109_2 Q2.hfix132_109_2 Q2.hinj132_109_2
      Q2.hcardT132_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_109_2 i) (Q2.hfix132_109_2 i) _)
      colCert_132_109_2.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_109_3 (hp : 3 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 3 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 3 (transLenTr ⟨109, by decide⟩ 3 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 3 (transLenTr ⟨109, by decide⟩ 3 hp)) T132_109
      hfix132_109 hinj132_109 hcardT132_109
      (fun i => conj_mem_of_fixedPoints _ _ (T132_109 i) (hfix132_109 i) _)
      ⟨132, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 3 hp) Q2.T132_109_2 Q2.hfix132_109_2 Q2.hinj132_109_2
      Q2.hcardT132_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_109_2 i) (Q2.hfix132_109_2 i) _)
      colCert_132_109_3.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_109_4 (hp : 4 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 4 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 4 (transLenTr ⟨109, by decide⟩ 4 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 4 (transLenTr ⟨109, by decide⟩ 4 hp)) T132_109
      hfix132_109 hinj132_109 hcardT132_109
      (fun i => conj_mem_of_fixedPoints _ _ (T132_109 i) (hfix132_109 i) _)
      ⟨132, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 4 hp) Q2.T132_109_2 Q2.hfix132_109_2 Q2.hinj132_109_2
      Q2.hcardT132_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_109_2 i) (Q2.hfix132_109_2 i) _)
      colCert_132_109_4.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_109_5 (hp : 5 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 5 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 5 (transLenTr ⟨109, by decide⟩ 5 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 5 (transLenTr ⟨109, by decide⟩ 5 hp)) T132_109
      hfix132_109 hinj132_109 hcardT132_109
      (fun i => conj_mem_of_fixedPoints _ _ (T132_109 i) (hfix132_109 i) _)
      ⟨132, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 5 hp) Q2.T132_109_2 Q2.hfix132_109_2 Q2.hinj132_109_2
      Q2.hcardT132_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_109_2 i) (Q2.hfix132_109_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨109, by decide⟩ 5 (transLenTr ⟨109, by decide⟩ 5 hp) : ↥(reps ⟨109, by decide⟩)) : Coordinate 1)
        T132_109 = colFn colCertDiv_132_109_5.D1 (m := 5) from colCertDiv_132_109_5.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨109, by decide⟩ 5 hp : ↥(Q2.reps ⟨109, by decide⟩)) : Coordinate 2)
        Q2.T132_109_2 = colFn colCertDiv_132_109_5.D2 (m := 5) from colCertDiv_132_109_5.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_109_5_match


theorem leaf_132_109_10 (hp : 10 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 10 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 10 (transLenTr ⟨109, by decide⟩ 10 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 10 (transLenTr ⟨109, by decide⟩ 10 hp)) T132_109
      hfix132_109 hinj132_109 hcardT132_109
      (fun i => conj_mem_of_fixedPoints _ _ (T132_109 i) (hfix132_109 i) _)
      ⟨132, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 10 hp) Q2.T132_109_2 Q2.hfix132_109_2 Q2.hinj132_109_2
      Q2.hcardT132_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_109_2 i) (Q2.hfix132_109_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨109, by decide⟩ 10 (transLenTr ⟨109, by decide⟩ 10 hp) : ↥(reps ⟨109, by decide⟩)) : Coordinate 1)
        T132_109 = colFn colCertDiv_132_109_10.D1 (m := 5) from colCertDiv_132_109_10.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨109, by decide⟩ 10 hp : ↥(Q2.reps ⟨109, by decide⟩)) : Coordinate 2)
        Q2.T132_109_2 = colFn colCertDiv_132_109_10.D2 (m := 5) from colCertDiv_132_109_10.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_109_10_match


theorem leaf_132_109_15 (hp : 15 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 15 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 15 (transLenTr ⟨109, by decide⟩ 15 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 15 (transLenTr ⟨109, by decide⟩ 15 hp)) T132_109
      hfix132_109 hinj132_109 hcardT132_109
      (fun i => conj_mem_of_fixedPoints _ _ (T132_109 i) (hfix132_109 i) _)
      ⟨132, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 15 hp) Q2.T132_109_2 Q2.hfix132_109_2 Q2.hinj132_109_2
      Q2.hcardT132_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_109_2 i) (Q2.hfix132_109_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨109, by decide⟩ 15 (transLenTr ⟨109, by decide⟩ 15 hp) : ↥(reps ⟨109, by decide⟩)) : Coordinate 1)
        T132_109 = colFn colCertDiv_132_109_15.D1 (m := 5) from colCertDiv_132_109_15.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨109, by decide⟩ 15 hp : ↥(Q2.reps ⟨109, by decide⟩)) : Coordinate 2)
        Q2.T132_109_2 = colFn colCertDiv_132_109_15.D2 (m := 5) from colCertDiv_132_109_15.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_109_15_match


theorem leaf_132_109_20 (hp : 20 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 20 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 20 (transLenTr ⟨109, by decide⟩ 20 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 20 (transLenTr ⟨109, by decide⟩ 20 hp)) T132_109
      hfix132_109 hinj132_109 hcardT132_109
      (fun i => conj_mem_of_fixedPoints _ _ (T132_109 i) (hfix132_109 i) _)
      ⟨132, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 20 hp) Q2.T132_109_2 Q2.hfix132_109_2 Q2.hinj132_109_2
      Q2.hcardT132_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_109_2 i) (Q2.hfix132_109_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨109, by decide⟩ 20 (transLenTr ⟨109, by decide⟩ 20 hp) : ↥(reps ⟨109, by decide⟩)) : Coordinate 1)
        T132_109 = colFn colCertDiv_132_109_20.D1 (m := 5) from colCertDiv_132_109_20.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨109, by decide⟩ 20 hp : ↥(Q2.reps ⟨109, by decide⟩)) : Coordinate 2)
        Q2.T132_109_2 = colFn colCertDiv_132_109_20.D2 (m := 5) from colCertDiv_132_109_20.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_109_20_match


theorem leaf_132_111_0 (hp : 0 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 0 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 0 (transLenTr ⟨111, by decide⟩ 0 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 0 (transLenTr ⟨111, by decide⟩ 0 hp)) T132_111
      hfix132_111 hinj132_111 hcardT132_111
      (fun i => conj_mem_of_fixedPoints _ _ (T132_111 i) (hfix132_111 i) _)
      ⟨132, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 0 hp) Q2.T132_111_2 Q2.hfix132_111_2 Q2.hinj132_111_2
      Q2.hcardT132_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_111_2 i) (Q2.hfix132_111_2 i) _)
      colCert_132_111_0.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_111_1 (hp : 1 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 1 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 1 (transLenTr ⟨111, by decide⟩ 1 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 1 (transLenTr ⟨111, by decide⟩ 1 hp)) T132_111
      hfix132_111 hinj132_111 hcardT132_111
      (fun i => conj_mem_of_fixedPoints _ _ (T132_111 i) (hfix132_111 i) _)
      ⟨132, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 1 hp) Q2.T132_111_2 Q2.hfix132_111_2 Q2.hinj132_111_2
      Q2.hcardT132_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_111_2 i) (Q2.hfix132_111_2 i) _)
      colCert_132_111_1.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_111_2 (hp : 2 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 2 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 2 (transLenTr ⟨111, by decide⟩ 2 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 2 (transLenTr ⟨111, by decide⟩ 2 hp)) T132_111
      hfix132_111 hinj132_111 hcardT132_111
      (fun i => conj_mem_of_fixedPoints _ _ (T132_111 i) (hfix132_111 i) _)
      ⟨132, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 2 hp) Q2.T132_111_2 Q2.hfix132_111_2 Q2.hinj132_111_2
      Q2.hcardT132_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_111_2 i) (Q2.hfix132_111_2 i) _)
      colCert_132_111_2.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_111_3 (hp : 3 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 3 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 3 (transLenTr ⟨111, by decide⟩ 3 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 3 (transLenTr ⟨111, by decide⟩ 3 hp)) T132_111
      hfix132_111 hinj132_111 hcardT132_111
      (fun i => conj_mem_of_fixedPoints _ _ (T132_111 i) (hfix132_111 i) _)
      ⟨132, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 3 hp) Q2.T132_111_2 Q2.hfix132_111_2 Q2.hinj132_111_2
      Q2.hcardT132_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_111_2 i) (Q2.hfix132_111_2 i) _)
      colCert_132_111_3.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_111_4 (hp : 4 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 4 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 4 (transLenTr ⟨111, by decide⟩ 4 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 4 (transLenTr ⟨111, by decide⟩ 4 hp)) T132_111
      hfix132_111 hinj132_111 hcardT132_111
      (fun i => conj_mem_of_fixedPoints _ _ (T132_111 i) (hfix132_111 i) _)
      ⟨132, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 4 hp) Q2.T132_111_2 Q2.hfix132_111_2 Q2.hinj132_111_2
      Q2.hcardT132_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_111_2 i) (Q2.hfix132_111_2 i) _)
      colCert_132_111_4.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_111_5 (hp : 5 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 5 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 5 (transLenTr ⟨111, by decide⟩ 5 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 5 (transLenTr ⟨111, by decide⟩ 5 hp)) T132_111
      hfix132_111 hinj132_111 hcardT132_111
      (fun i => conj_mem_of_fixedPoints _ _ (T132_111 i) (hfix132_111 i) _)
      ⟨132, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 5 hp) Q2.T132_111_2 Q2.hfix132_111_2 Q2.hinj132_111_2
      Q2.hcardT132_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_111_2 i) (Q2.hfix132_111_2 i) _)
      colCert_132_111_5.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_111_10 (hp : 10 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 10 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 10 (transLenTr ⟨111, by decide⟩ 10 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 10 (transLenTr ⟨111, by decide⟩ 10 hp)) T132_111
      hfix132_111 hinj132_111 hcardT132_111
      (fun i => conj_mem_of_fixedPoints _ _ (T132_111 i) (hfix132_111 i) _)
      ⟨132, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 10 hp) Q2.T132_111_2 Q2.hfix132_111_2 Q2.hinj132_111_2
      Q2.hcardT132_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_111_2 i) (Q2.hfix132_111_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨111, by decide⟩ 10 (transLenTr ⟨111, by decide⟩ 10 hp) : ↥(reps ⟨111, by decide⟩)) : Coordinate 1)
        T132_111 = colFn colCertDiv_132_111_10.D1 (m := 5) from colCertDiv_132_111_10.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨111, by decide⟩ 10 hp : ↥(Q2.reps ⟨111, by decide⟩)) : Coordinate 2)
        Q2.T132_111_2 = colFn colCertDiv_132_111_10.D2 (m := 5) from colCertDiv_132_111_10.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_111_10_match


theorem leaf_132_111_15 (hp : 15 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 15 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 15 (transLenTr ⟨111, by decide⟩ 15 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 15 (transLenTr ⟨111, by decide⟩ 15 hp)) T132_111
      hfix132_111 hinj132_111 hcardT132_111
      (fun i => conj_mem_of_fixedPoints _ _ (T132_111 i) (hfix132_111 i) _)
      ⟨132, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 15 hp) Q2.T132_111_2 Q2.hfix132_111_2 Q2.hinj132_111_2
      Q2.hcardT132_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_111_2 i) (Q2.hfix132_111_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨111, by decide⟩ 15 (transLenTr ⟨111, by decide⟩ 15 hp) : ↥(reps ⟨111, by decide⟩)) : Coordinate 1)
        T132_111 = colFn colCertDiv_132_111_15.D1 (m := 5) from colCertDiv_132_111_15.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨111, by decide⟩ 15 hp : ↥(Q2.reps ⟨111, by decide⟩)) : Coordinate 2)
        Q2.T132_111_2 = colFn colCertDiv_132_111_15.D2 (m := 5) from colCertDiv_132_111_15.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_111_15_match


theorem leaf_132_111_20 (hp : 20 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 20 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 20 (transLenTr ⟨111, by decide⟩ 20 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 20 (transLenTr ⟨111, by decide⟩ 20 hp)) T132_111
      hfix132_111 hinj132_111 hcardT132_111
      (fun i => conj_mem_of_fixedPoints _ _ (T132_111 i) (hfix132_111 i) _)
      ⟨132, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 20 hp) Q2.T132_111_2 Q2.hfix132_111_2 Q2.hinj132_111_2
      Q2.hcardT132_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_111_2 i) (Q2.hfix132_111_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨111, by decide⟩ 20 (transLenTr ⟨111, by decide⟩ 20 hp) : ↥(reps ⟨111, by decide⟩)) : Coordinate 1)
        T132_111 = colFn colCertDiv_132_111_20.D1 (m := 5) from colCertDiv_132_111_20.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨111, by decide⟩ 20 hp : ↥(Q2.reps ⟨111, by decide⟩)) : Coordinate 2)
        Q2.T132_111_2 = colFn colCertDiv_132_111_20.D2 (m := 5) from colCertDiv_132_111_20.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_111_20_match


theorem leaf_132_132_0 (hp : 0 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 0 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 0 (transLenTr ⟨132, by decide⟩ 0 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 0 (transLenTr ⟨132, by decide⟩ 0 hp)) T132_132
      hfix132_132 hinj132_132 hcardT132_132
      (fun i => conj_mem_of_fixedPoints _ _ (T132_132 i) (hfix132_132 i) _)
      ⟨132, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 0 hp) Q2.T132_132_2 Q2.hfix132_132_2 Q2.hinj132_132_2
      Q2.hcardT132_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_132_2 i) (Q2.hfix132_132_2 i) _)
      colCert_132_132_0.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_132_1 (hp : 1 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 1 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 1 (transLenTr ⟨132, by decide⟩ 1 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 1 (transLenTr ⟨132, by decide⟩ 1 hp)) T132_132
      hfix132_132 hinj132_132 hcardT132_132
      (fun i => conj_mem_of_fixedPoints _ _ (T132_132 i) (hfix132_132 i) _)
      ⟨132, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 1 hp) Q2.T132_132_2 Q2.hfix132_132_2 Q2.hinj132_132_2
      Q2.hcardT132_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_132_2 i) (Q2.hfix132_132_2 i) _)
      colCert_132_132_1.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_132_2 (hp : 2 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 2 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 2 (transLenTr ⟨132, by decide⟩ 2 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 2 (transLenTr ⟨132, by decide⟩ 2 hp)) T132_132
      hfix132_132 hinj132_132 hcardT132_132
      (fun i => conj_mem_of_fixedPoints _ _ (T132_132 i) (hfix132_132 i) _)
      ⟨132, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 2 hp) Q2.T132_132_2 Q2.hfix132_132_2 Q2.hinj132_132_2
      Q2.hcardT132_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_132_2 i) (Q2.hfix132_132_2 i) _)
      colCert_132_132_2.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_132_3 (hp : 3 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 3 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 3 (transLenTr ⟨132, by decide⟩ 3 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 3 (transLenTr ⟨132, by decide⟩ 3 hp)) T132_132
      hfix132_132 hinj132_132 hcardT132_132
      (fun i => conj_mem_of_fixedPoints _ _ (T132_132 i) (hfix132_132 i) _)
      ⟨132, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 3 hp) Q2.T132_132_2 Q2.hfix132_132_2 Q2.hinj132_132_2
      Q2.hcardT132_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_132_2 i) (Q2.hfix132_132_2 i) _)
      colCert_132_132_3.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_132_4 (hp : 4 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 4 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 4 (transLenTr ⟨132, by decide⟩ 4 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 4 (transLenTr ⟨132, by decide⟩ 4 hp)) T132_132
      hfix132_132 hinj132_132 hcardT132_132
      (fun i => conj_mem_of_fixedPoints _ _ (T132_132 i) (hfix132_132 i) _)
      ⟨132, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 4 hp) Q2.T132_132_2 Q2.hfix132_132_2 Q2.hinj132_132_2
      Q2.hcardT132_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_132_2 i) (Q2.hfix132_132_2 i) _)
      colCert_132_132_4.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_132_5 (hp : 5 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 5 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 5 (transLenTr ⟨132, by decide⟩ 5 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 5 (transLenTr ⟨132, by decide⟩ 5 hp)) T132_132
      hfix132_132 hinj132_132 hcardT132_132
      (fun i => conj_mem_of_fixedPoints _ _ (T132_132 i) (hfix132_132 i) _)
      ⟨132, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 5 hp) Q2.T132_132_2 Q2.hfix132_132_2 Q2.hinj132_132_2
      Q2.hcardT132_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_132_2 i) (Q2.hfix132_132_2 i) _)
      colCert_132_132_5.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_132_6 (hp : 6 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 6 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 6 (transLenTr ⟨132, by decide⟩ 6 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 6 (transLenTr ⟨132, by decide⟩ 6 hp)) T132_132
      hfix132_132 hinj132_132 hcardT132_132
      (fun i => conj_mem_of_fixedPoints _ _ (T132_132 i) (hfix132_132 i) _)
      ⟨132, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 6 hp) Q2.T132_132_2 Q2.hfix132_132_2 Q2.hinj132_132_2
      Q2.hcardT132_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_132_2 i) (Q2.hfix132_132_2 i) _)
      colCert_132_132_6.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_132_7 (hp : 7 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 7 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 7 (transLenTr ⟨132, by decide⟩ 7 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 7 (transLenTr ⟨132, by decide⟩ 7 hp)) T132_132
      hfix132_132 hinj132_132 hcardT132_132
      (fun i => conj_mem_of_fixedPoints _ _ (T132_132 i) (hfix132_132 i) _)
      ⟨132, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 7 hp) Q2.T132_132_2 Q2.hfix132_132_2 Q2.hinj132_132_2
      Q2.hcardT132_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_132_2 i) (Q2.hfix132_132_2 i) _)
      colCert_132_132_7.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_132_8 (hp : 8 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 8 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 8 (transLenTr ⟨132, by decide⟩ 8 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 8 (transLenTr ⟨132, by decide⟩ 8 hp)) T132_132
      hfix132_132 hinj132_132 hcardT132_132
      (fun i => conj_mem_of_fixedPoints _ _ (T132_132 i) (hfix132_132 i) _)
      ⟨132, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 8 hp) Q2.T132_132_2 Q2.hfix132_132_2 Q2.hinj132_132_2
      Q2.hcardT132_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_132_2 i) (Q2.hfix132_132_2 i) _)
      colCert_132_132_8.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_132_9 (hp : 9 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 9 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 9 (transLenTr ⟨132, by decide⟩ 9 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 9 (transLenTr ⟨132, by decide⟩ 9 hp)) T132_132
      hfix132_132 hinj132_132 hcardT132_132
      (fun i => conj_mem_of_fixedPoints _ _ (T132_132 i) (hfix132_132 i) _)
      ⟨132, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 9 hp) Q2.T132_132_2 Q2.hfix132_132_2 Q2.hinj132_132_2
      Q2.hcardT132_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_132_2 i) (Q2.hfix132_132_2 i) _)
      colCert_132_132_9.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_132_10 (hp : 10 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 10 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 10 (transLenTr ⟨132, by decide⟩ 10 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 10 (transLenTr ⟨132, by decide⟩ 10 hp)) T132_132
      hfix132_132 hinj132_132 hcardT132_132
      (fun i => conj_mem_of_fixedPoints _ _ (T132_132 i) (hfix132_132 i) _)
      ⟨132, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 10 hp) Q2.T132_132_2 Q2.hfix132_132_2 Q2.hinj132_132_2
      Q2.hcardT132_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_132_2 i) (Q2.hfix132_132_2 i) _)
      colCert_132_132_10.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_132_11 (hp : 11 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 11 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 11 (transLenTr ⟨132, by decide⟩ 11 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 11 (transLenTr ⟨132, by decide⟩ 11 hp)) T132_132
      hfix132_132 hinj132_132 hcardT132_132
      (fun i => conj_mem_of_fixedPoints _ _ (T132_132 i) (hfix132_132 i) _)
      ⟨132, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 11 hp) Q2.T132_132_2 Q2.hfix132_132_2 Q2.hinj132_132_2
      Q2.hcardT132_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_132_2 i) (Q2.hfix132_132_2 i) _)
      colCert_132_132_11.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_132_12 (hp : 12 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 12 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 12 (transLenTr ⟨132, by decide⟩ 12 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 12 (transLenTr ⟨132, by decide⟩ 12 hp)) T132_132
      hfix132_132 hinj132_132 hcardT132_132
      (fun i => conj_mem_of_fixedPoints _ _ (T132_132 i) (hfix132_132 i) _)
      ⟨132, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 12 hp) Q2.T132_132_2 Q2.hfix132_132_2 Q2.hinj132_132_2
      Q2.hcardT132_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_132_2 i) (Q2.hfix132_132_2 i) _)
      colCert_132_132_12.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_132_13 (hp : 13 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 13 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 13 (transLenTr ⟨132, by decide⟩ 13 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 13 (transLenTr ⟨132, by decide⟩ 13 hp)) T132_132
      hfix132_132 hinj132_132 hcardT132_132
      (fun i => conj_mem_of_fixedPoints _ _ (T132_132 i) (hfix132_132 i) _)
      ⟨132, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 13 hp) Q2.T132_132_2 Q2.hfix132_132_2 Q2.hinj132_132_2
      Q2.hcardT132_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_132_2 i) (Q2.hfix132_132_2 i) _)
      colCert_132_132_13.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_132_14 (hp : 14 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 14 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 14 (transLenTr ⟨132, by decide⟩ 14 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 14 (transLenTr ⟨132, by decide⟩ 14 hp)) T132_132
      hfix132_132 hinj132_132 hcardT132_132
      (fun i => conj_mem_of_fixedPoints _ _ (T132_132 i) (hfix132_132 i) _)
      ⟨132, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 14 hp) Q2.T132_132_2 Q2.hfix132_132_2 Q2.hinj132_132_2
      Q2.hcardT132_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_132_2 i) (Q2.hfix132_132_2 i) _)
      colCert_132_132_14.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_132_15 (hp : 15 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 15 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 15 (transLenTr ⟨132, by decide⟩ 15 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 15 (transLenTr ⟨132, by decide⟩ 15 hp)) T132_132
      hfix132_132 hinj132_132 hcardT132_132
      (fun i => conj_mem_of_fixedPoints _ _ (T132_132 i) (hfix132_132 i) _)
      ⟨132, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 15 hp) Q2.T132_132_2 Q2.hfix132_132_2 Q2.hinj132_132_2
      Q2.hcardT132_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_132_2 i) (Q2.hfix132_132_2 i) _)
      colCert_132_132_15.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_132_16 (hp : 16 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 16 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 16 (transLenTr ⟨132, by decide⟩ 16 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 16 (transLenTr ⟨132, by decide⟩ 16 hp)) T132_132
      hfix132_132 hinj132_132 hcardT132_132
      (fun i => conj_mem_of_fixedPoints _ _ (T132_132 i) (hfix132_132 i) _)
      ⟨132, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 16 hp) Q2.T132_132_2 Q2.hfix132_132_2 Q2.hinj132_132_2
      Q2.hcardT132_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_132_2 i) (Q2.hfix132_132_2 i) _)
      colCert_132_132_16.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_132_17 (hp : 17 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 17 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 17 (transLenTr ⟨132, by decide⟩ 17 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 17 (transLenTr ⟨132, by decide⟩ 17 hp)) T132_132
      hfix132_132 hinj132_132 hcardT132_132
      (fun i => conj_mem_of_fixedPoints _ _ (T132_132 i) (hfix132_132 i) _)
      ⟨132, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 17 hp) Q2.T132_132_2 Q2.hfix132_132_2 Q2.hinj132_132_2
      Q2.hcardT132_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_132_2 i) (Q2.hfix132_132_2 i) _)
      colCert_132_132_17.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_132_18 (hp : 18 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 18 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 18 (transLenTr ⟨132, by decide⟩ 18 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 18 (transLenTr ⟨132, by decide⟩ 18 hp)) T132_132
      hfix132_132 hinj132_132 hcardT132_132
      (fun i => conj_mem_of_fixedPoints _ _ (T132_132 i) (hfix132_132 i) _)
      ⟨132, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 18 hp) Q2.T132_132_2 Q2.hfix132_132_2 Q2.hinj132_132_2
      Q2.hcardT132_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_132_2 i) (Q2.hfix132_132_2 i) _)
      colCert_132_132_18.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_132_19 (hp : 19 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 19 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 19 (transLenTr ⟨132, by decide⟩ 19 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 19 (transLenTr ⟨132, by decide⟩ 19 hp)) T132_132
      hfix132_132 hinj132_132 hcardT132_132
      (fun i => conj_mem_of_fixedPoints _ _ (T132_132 i) (hfix132_132 i) _)
      ⟨132, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 19 hp) Q2.T132_132_2 Q2.hfix132_132_2 Q2.hinj132_132_2
      Q2.hcardT132_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_132_2 i) (Q2.hfix132_132_2 i) _)
      colCert_132_132_19.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_132_20 (hp : 20 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 20 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 20 (transLenTr ⟨132, by decide⟩ 20 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 20 (transLenTr ⟨132, by decide⟩ 20 hp)) T132_132
      hfix132_132 hinj132_132 hcardT132_132
      (fun i => conj_mem_of_fixedPoints _ _ (T132_132 i) (hfix132_132 i) _)
      ⟨132, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 20 hp) Q2.T132_132_2 Q2.hfix132_132_2 Q2.hinj132_132_2
      Q2.hcardT132_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_132_2 i) (Q2.hfix132_132_2 i) _)
      colCert_132_132_20.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_132_21 (hp : 21 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 21 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 21 (transLenTr ⟨132, by decide⟩ 21 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 21 (transLenTr ⟨132, by decide⟩ 21 hp)) T132_132
      hfix132_132 hinj132_132 hcardT132_132
      (fun i => conj_mem_of_fixedPoints _ _ (T132_132 i) (hfix132_132 i) _)
      ⟨132, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 21 hp) Q2.T132_132_2 Q2.hfix132_132_2 Q2.hinj132_132_2
      Q2.hcardT132_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_132_2 i) (Q2.hfix132_132_2 i) _)
      colCert_132_132_21.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_132_22 (hp : 22 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 22 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 22 (transLenTr ⟨132, by decide⟩ 22 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 22 (transLenTr ⟨132, by decide⟩ 22 hp)) T132_132
      hfix132_132 hinj132_132 hcardT132_132
      (fun i => conj_mem_of_fixedPoints _ _ (T132_132 i) (hfix132_132 i) _)
      ⟨132, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 22 hp) Q2.T132_132_2 Q2.hfix132_132_2 Q2.hinj132_132_2
      Q2.hcardT132_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_132_2 i) (Q2.hfix132_132_2 i) _)
      colCert_132_132_22.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_132_23 (hp : 23 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 23 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 23 (transLenTr ⟨132, by decide⟩ 23 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 23 (transLenTr ⟨132, by decide⟩ 23 hp)) T132_132
      hfix132_132 hinj132_132 hcardT132_132
      (fun i => conj_mem_of_fixedPoints _ _ (T132_132 i) (hfix132_132 i) _)
      ⟨132, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 23 hp) Q2.T132_132_2 Q2.hfix132_132_2 Q2.hinj132_132_2
      Q2.hcardT132_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_132_2 i) (Q2.hfix132_132_2 i) _)
      colCert_132_132_23.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_132_24 (hp : 24 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 24 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 24 (transLenTr ⟨132, by decide⟩ 24 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 24 (transLenTr ⟨132, by decide⟩ 24 hp)) T132_132
      hfix132_132 hinj132_132 hcardT132_132
      (fun i => conj_mem_of_fixedPoints _ _ (T132_132 i) (hfix132_132 i) _)
      ⟨132, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 24 hp) Q2.T132_132_2 Q2.hfix132_132_2 Q2.hinj132_132_2
      Q2.hcardT132_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_132_2 i) (Q2.hfix132_132_2 i) _)
      colCert_132_132_24.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_133_4_0 (hp : 0 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 0 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp)) T133_4
      hfix133_4 hinj133_4 hcardT133_4
      (fun i => conj_mem_of_fixedPoints _ _ (T133_4 i) (hfix133_4 i) _)
      ⟨133, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 0 hp) Q2.T133_4_2 Q2.hfix133_4_2 Q2.hinj133_4_2
      Q2.hcardT133_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_4_2 i) (Q2.hfix133_4_2 i) _)
      colCert_133_4_0.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_4_1 (hp : 1 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 1 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp)) T133_4
      hfix133_4 hinj133_4 hcardT133_4
      (fun i => conj_mem_of_fixedPoints _ _ (T133_4 i) (hfix133_4 i) _)
      ⟨133, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 1 hp) Q2.T133_4_2 Q2.hfix133_4_2 Q2.hinj133_4_2
      Q2.hcardT133_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_4_2 i) (Q2.hfix133_4_2 i) _)
      colCert_133_4_1.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_4_2 (hp : 2 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 2 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp)) T133_4
      hfix133_4 hinj133_4 hcardT133_4
      (fun i => conj_mem_of_fixedPoints _ _ (T133_4 i) (hfix133_4 i) _)
      ⟨133, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 2 hp) Q2.T133_4_2 Q2.hfix133_4_2 Q2.hinj133_4_2
      Q2.hcardT133_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_4_2 i) (Q2.hfix133_4_2 i) _)
      colCert_133_4_2.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_4_3 (hp : 3 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 3 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp)) T133_4
      hfix133_4 hinj133_4 hcardT133_4
      (fun i => conj_mem_of_fixedPoints _ _ (T133_4 i) (hfix133_4 i) _)
      ⟨133, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 3 hp) Q2.T133_4_2 Q2.hfix133_4_2 Q2.hinj133_4_2
      Q2.hcardT133_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_4_2 i) (Q2.hfix133_4_2 i) _)
      colCert_133_4_3.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_4_4 (hp : 4 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 4 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp)) T133_4
      hfix133_4 hinj133_4 hcardT133_4
      (fun i => conj_mem_of_fixedPoints _ _ (T133_4 i) (hfix133_4 i) _)
      ⟨133, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 4 hp) Q2.T133_4_2 Q2.hfix133_4_2 Q2.hinj133_4_2
      Q2.hcardT133_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_4_2 i) (Q2.hfix133_4_2 i) _)
      colCert_133_4_4.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T133_10
      hfix133_10 hinj133_10 hcardT133_10
      (fun i => conj_mem_of_fixedPoints _ _ (T133_10 i) (hfix133_10 i) _)
      ⟨133, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T133_10_2 Q2.hfix133_10_2 Q2.hinj133_10_2
      Q2.hcardT133_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_10_2 i) (Q2.hfix133_10_2 i) _)
      colCert_133_10_0.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T133_10
      hfix133_10 hinj133_10 hcardT133_10
      (fun i => conj_mem_of_fixedPoints _ _ (T133_10 i) (hfix133_10 i) _)
      ⟨133, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T133_10_2 Q2.hfix133_10_2 Q2.hinj133_10_2
      Q2.hcardT133_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_10_2 i) (Q2.hfix133_10_2 i) _)
      colCert_133_10_1.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T133_10
      hfix133_10 hinj133_10 hcardT133_10
      (fun i => conj_mem_of_fixedPoints _ _ (T133_10 i) (hfix133_10 i) _)
      ⟨133, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T133_10_2 Q2.hfix133_10_2 Q2.hinj133_10_2
      Q2.hcardT133_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_10_2 i) (Q2.hfix133_10_2 i) _)
      colCert_133_10_2.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T133_10
      hfix133_10 hinj133_10 hcardT133_10
      (fun i => conj_mem_of_fixedPoints _ _ (T133_10 i) (hfix133_10 i) _)
      ⟨133, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T133_10_2 Q2.hfix133_10_2 Q2.hinj133_10_2
      Q2.hcardT133_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_10_2 i) (Q2.hfix133_10_2 i) _)
      colCert_133_10_3.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T133_10
      hfix133_10 hinj133_10 hcardT133_10
      (fun i => conj_mem_of_fixedPoints _ _ (T133_10 i) (hfix133_10 i) _)
      ⟨133, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T133_10_2 Q2.hfix133_10_2 Q2.hinj133_10_2
      Q2.hcardT133_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_10_2 i) (Q2.hfix133_10_2 i) _)
      colCert_133_10_4.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T133_12
      hfix133_12 hinj133_12 hcardT133_12
      (fun i => conj_mem_of_fixedPoints _ _ (T133_12 i) (hfix133_12 i) _)
      ⟨133, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T133_12_2 Q2.hfix133_12_2 Q2.hinj133_12_2
      Q2.hcardT133_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_12_2 i) (Q2.hfix133_12_2 i) _)
      colCert_133_12_0.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T133_12
      hfix133_12 hinj133_12 hcardT133_12
      (fun i => conj_mem_of_fixedPoints _ _ (T133_12 i) (hfix133_12 i) _)
      ⟨133, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T133_12_2 Q2.hfix133_12_2 Q2.hinj133_12_2
      Q2.hcardT133_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_12_2 i) (Q2.hfix133_12_2 i) _)
      colCert_133_12_1.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T133_12
      hfix133_12 hinj133_12 hcardT133_12
      (fun i => conj_mem_of_fixedPoints _ _ (T133_12 i) (hfix133_12 i) _)
      ⟨133, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T133_12_2 Q2.hfix133_12_2 Q2.hinj133_12_2
      Q2.hcardT133_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_12_2 i) (Q2.hfix133_12_2 i) _)
      colCert_133_12_2.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T133_12
      hfix133_12 hinj133_12 hcardT133_12
      (fun i => conj_mem_of_fixedPoints _ _ (T133_12 i) (hfix133_12 i) _)
      ⟨133, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T133_12_2 Q2.hfix133_12_2 Q2.hinj133_12_2
      Q2.hcardT133_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_12_2 i) (Q2.hfix133_12_2 i) _)
      colCert_133_12_3.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T133_12
      hfix133_12 hinj133_12 hcardT133_12
      (fun i => conj_mem_of_fixedPoints _ _ (T133_12 i) (hfix133_12 i) _)
      ⟨133, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T133_12_2 Q2.hfix133_12_2 Q2.hinj133_12_2
      Q2.hcardT133_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_12_2 i) (Q2.hfix133_12_2 i) _)
      colCert_133_12_4.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_22_0 (hp : 0 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 0 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 0 (transLenTr ⟨22, by decide⟩ 0 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 0 (transLenTr ⟨22, by decide⟩ 0 hp)) T133_22
      hfix133_22 hinj133_22 hcardT133_22
      (fun i => conj_mem_of_fixedPoints _ _ (T133_22 i) (hfix133_22 i) _)
      ⟨133, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 0 hp) Q2.T133_22_2 Q2.hfix133_22_2 Q2.hinj133_22_2
      Q2.hcardT133_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_22_2 i) (Q2.hfix133_22_2 i) _)
      colCert_133_22_0.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_22_1 (hp : 1 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 1 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 1 (transLenTr ⟨22, by decide⟩ 1 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 1 (transLenTr ⟨22, by decide⟩ 1 hp)) T133_22
      hfix133_22 hinj133_22 hcardT133_22
      (fun i => conj_mem_of_fixedPoints _ _ (T133_22 i) (hfix133_22 i) _)
      ⟨133, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 1 hp) Q2.T133_22_2 Q2.hfix133_22_2 Q2.hinj133_22_2
      Q2.hcardT133_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_22_2 i) (Q2.hfix133_22_2 i) _)
      colCert_133_22_1.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_22_2 (hp : 2 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 2 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 2 (transLenTr ⟨22, by decide⟩ 2 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 2 (transLenTr ⟨22, by decide⟩ 2 hp)) T133_22
      hfix133_22 hinj133_22 hcardT133_22
      (fun i => conj_mem_of_fixedPoints _ _ (T133_22 i) (hfix133_22 i) _)
      ⟨133, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 2 hp) Q2.T133_22_2 Q2.hfix133_22_2 Q2.hinj133_22_2
      Q2.hcardT133_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_22_2 i) (Q2.hfix133_22_2 i) _)
      colCert_133_22_2.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_22_3 (hp : 3 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 3 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 3 (transLenTr ⟨22, by decide⟩ 3 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 3 (transLenTr ⟨22, by decide⟩ 3 hp)) T133_22
      hfix133_22 hinj133_22 hcardT133_22
      (fun i => conj_mem_of_fixedPoints _ _ (T133_22 i) (hfix133_22 i) _)
      ⟨133, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 3 hp) Q2.T133_22_2 Q2.hfix133_22_2 Q2.hinj133_22_2
      Q2.hcardT133_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_22_2 i) (Q2.hfix133_22_2 i) _)
      colCert_133_22_3.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_22_4 (hp : 4 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 4 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 4 (transLenTr ⟨22, by decide⟩ 4 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 4 (transLenTr ⟨22, by decide⟩ 4 hp)) T133_22
      hfix133_22 hinj133_22 hcardT133_22
      (fun i => conj_mem_of_fixedPoints _ _ (T133_22 i) (hfix133_22 i) _)
      ⟨133, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 4 hp) Q2.T133_22_2 Q2.hfix133_22_2 Q2.hinj133_22_2
      Q2.hcardT133_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_22_2 i) (Q2.hfix133_22_2 i) _)
      colCert_133_22_4.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_22_5 (hp : 5 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 5 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp)) T133_22
      hfix133_22 hinj133_22 hcardT133_22
      (fun i => conj_mem_of_fixedPoints _ _ (T133_22 i) (hfix133_22 i) _)
      ⟨133, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 5 hp) Q2.T133_22_2 Q2.hfix133_22_2 Q2.hinj133_22_2
      Q2.hcardT133_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_22_2 i) (Q2.hfix133_22_2 i) _)
      colCert_133_22_5.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_22_10 (hp : 10 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 10 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp)) T133_22
      hfix133_22 hinj133_22 hcardT133_22
      (fun i => conj_mem_of_fixedPoints _ _ (T133_22 i) (hfix133_22 i) _)
      ⟨133, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 10 hp) Q2.T133_22_2 Q2.hfix133_22_2 Q2.hinj133_22_2
      Q2.hcardT133_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_22_2 i) (Q2.hfix133_22_2 i) _)
      colCert_133_22_10.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_22_15 (hp : 15 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 15 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp)) T133_22
      hfix133_22 hinj133_22 hcardT133_22
      (fun i => conj_mem_of_fixedPoints _ _ (T133_22 i) (hfix133_22 i) _)
      ⟨133, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 15 hp) Q2.T133_22_2 Q2.hfix133_22_2 Q2.hinj133_22_2
      Q2.hcardT133_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_22_2 i) (Q2.hfix133_22_2 i) _)
      colCert_133_22_15.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_22_20 (hp : 20 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 20 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp)) T133_22
      hfix133_22 hinj133_22 hcardT133_22
      (fun i => conj_mem_of_fixedPoints _ _ (T133_22 i) (hfix133_22 i) _)
      ⟨133, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 20 hp) Q2.T133_22_2 Q2.hfix133_22_2 Q2.hinj133_22_2
      Q2.hcardT133_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_22_2 i) (Q2.hfix133_22_2 i) _)
      colCert_133_22_20.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_32_0 (hp : 0 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 0 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp)) T133_32
      hfix133_32 hinj133_32 hcardT133_32
      (fun i => conj_mem_of_fixedPoints _ _ (T133_32 i) (hfix133_32 i) _)
      ⟨133, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 0 hp) Q2.T133_32_2 Q2.hfix133_32_2 Q2.hinj133_32_2
      Q2.hcardT133_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_32_2 i) (Q2.hfix133_32_2 i) _)
      colCert_133_32_0.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_32_1 (hp : 1 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 1 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp)) T133_32
      hfix133_32 hinj133_32 hcardT133_32
      (fun i => conj_mem_of_fixedPoints _ _ (T133_32 i) (hfix133_32 i) _)
      ⟨133, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 1 hp) Q2.T133_32_2 Q2.hfix133_32_2 Q2.hinj133_32_2
      Q2.hcardT133_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_32_2 i) (Q2.hfix133_32_2 i) _)
      colCert_133_32_1.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_32_2 (hp : 2 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 2 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp)) T133_32
      hfix133_32 hinj133_32 hcardT133_32
      (fun i => conj_mem_of_fixedPoints _ _ (T133_32 i) (hfix133_32 i) _)
      ⟨133, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 2 hp) Q2.T133_32_2 Q2.hfix133_32_2 Q2.hinj133_32_2
      Q2.hcardT133_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_32_2 i) (Q2.hfix133_32_2 i) _)
      colCert_133_32_2.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_32_3 (hp : 3 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 3 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp)) T133_32
      hfix133_32 hinj133_32 hcardT133_32
      (fun i => conj_mem_of_fixedPoints _ _ (T133_32 i) (hfix133_32 i) _)
      ⟨133, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 3 hp) Q2.T133_32_2 Q2.hfix133_32_2 Q2.hinj133_32_2
      Q2.hcardT133_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_32_2 i) (Q2.hfix133_32_2 i) _)
      colCert_133_32_3.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_32_4 (hp : 4 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 4 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp)) T133_32
      hfix133_32 hinj133_32 hcardT133_32
      (fun i => conj_mem_of_fixedPoints _ _ (T133_32 i) (hfix133_32 i) _)
      ⟨133, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 4 hp) Q2.T133_32_2 Q2.hfix133_32_2 Q2.hinj133_32_2
      Q2.hcardT133_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_32_2 i) (Q2.hfix133_32_2 i) _)
      colCert_133_32_4.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_32_5 (hp : 5 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 5 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨133, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp)) T133_32
      hfix133_32 hinj133_32 hcardT133_32
      (fun i => conj_mem_of_fixedPoints _ _ (T133_32 i) (hfix133_32 i) _)
      ⟨133, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 5 hp) Q2.T133_32_2 Q2.hfix133_32_2 Q2.hinj133_32_2
      Q2.hcardT133_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_32_2 i) (Q2.hfix133_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨133, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T133_32 = colFn colCertDiv_133_32_5.D1 (m := 5) from colCertDiv_133_32_5.bind1,
    show colData2 (⟨133, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 5 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T133_32_2 = colFn colCertDiv_133_32_5.D2 (m := 5) from colCertDiv_133_32_5.bind2]
  rw [alnId_133 j hj]
  exact fastcode_of_div ⟨133, by decide⟩ _ _ _
    ((alnId_133 j hj) ▸ Q2.listedAt (⟨133, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨133, by decide⟩ : Fin 148) hj hq).1) colCertDiv_133_32_5_match


theorem leaf_133_32_10 (hp : 10 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 10 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨133, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp)) T133_32
      hfix133_32 hinj133_32 hcardT133_32
      (fun i => conj_mem_of_fixedPoints _ _ (T133_32 i) (hfix133_32 i) _)
      ⟨133, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 10 hp) Q2.T133_32_2 Q2.hfix133_32_2 Q2.hinj133_32_2
      Q2.hcardT133_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_32_2 i) (Q2.hfix133_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨133, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T133_32 = colFn colCertDiv_133_32_10.D1 (m := 5) from colCertDiv_133_32_10.bind1,
    show colData2 (⟨133, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 10 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T133_32_2 = colFn colCertDiv_133_32_10.D2 (m := 5) from colCertDiv_133_32_10.bind2]
  rw [alnId_133 j hj]
  exact fastcode_of_div ⟨133, by decide⟩ _ _ _
    ((alnId_133 j hj) ▸ Q2.listedAt (⟨133, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨133, by decide⟩ : Fin 148) hj hq).1) colCertDiv_133_32_10_match


theorem leaf_133_32_15 (hp : 15 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 15 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨133, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp)) T133_32
      hfix133_32 hinj133_32 hcardT133_32
      (fun i => conj_mem_of_fixedPoints _ _ (T133_32 i) (hfix133_32 i) _)
      ⟨133, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 15 hp) Q2.T133_32_2 Q2.hfix133_32_2 Q2.hinj133_32_2
      Q2.hcardT133_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_32_2 i) (Q2.hfix133_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨133, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T133_32 = colFn colCertDiv_133_32_15.D1 (m := 5) from colCertDiv_133_32_15.bind1,
    show colData2 (⟨133, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 15 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T133_32_2 = colFn colCertDiv_133_32_15.D2 (m := 5) from colCertDiv_133_32_15.bind2]
  rw [alnId_133 j hj]
  exact fastcode_of_div ⟨133, by decide⟩ _ _ _
    ((alnId_133 j hj) ▸ Q2.listedAt (⟨133, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨133, by decide⟩ : Fin 148) hj hq).1) colCertDiv_133_32_15_match


theorem leaf_133_32_20 (hp : 20 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 20 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨133, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp)) T133_32
      hfix133_32 hinj133_32 hcardT133_32
      (fun i => conj_mem_of_fixedPoints _ _ (T133_32 i) (hfix133_32 i) _)
      ⟨133, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 20 hp) Q2.T133_32_2 Q2.hfix133_32_2 Q2.hinj133_32_2
      Q2.hcardT133_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_32_2 i) (Q2.hfix133_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨133, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T133_32 = colFn colCertDiv_133_32_20.D1 (m := 5) from colCertDiv_133_32_20.bind1,
    show colData2 (⟨133, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 20 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T133_32_2 = colFn colCertDiv_133_32_20.D2 (m := 5) from colCertDiv_133_32_20.bind2]
  rw [alnId_133 j hj]
  exact fastcode_of_div ⟨133, by decide⟩ _ _ _
    ((alnId_133 j hj) ▸ Q2.listedAt (⟨133, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨133, by decide⟩ : Fin 148) hj hq).1) colCertDiv_133_32_20_match


theorem leaf_133_36_0 (hp : 0 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 0 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp)) T133_36
      hfix133_36 hinj133_36 hcardT133_36
      (fun i => conj_mem_of_fixedPoints _ _ (T133_36 i) (hfix133_36 i) _)
      ⟨133, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 0 hp) Q2.T133_36_2 Q2.hfix133_36_2 Q2.hinj133_36_2
      Q2.hcardT133_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_36_2 i) (Q2.hfix133_36_2 i) _)
      colCert_133_36_0.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_36_1 (hp : 1 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 1 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp)) T133_36
      hfix133_36 hinj133_36 hcardT133_36
      (fun i => conj_mem_of_fixedPoints _ _ (T133_36 i) (hfix133_36 i) _)
      ⟨133, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 1 hp) Q2.T133_36_2 Q2.hfix133_36_2 Q2.hinj133_36_2
      Q2.hcardT133_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_36_2 i) (Q2.hfix133_36_2 i) _)
      colCert_133_36_1.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_36_2 (hp : 2 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 2 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp)) T133_36
      hfix133_36 hinj133_36 hcardT133_36
      (fun i => conj_mem_of_fixedPoints _ _ (T133_36 i) (hfix133_36 i) _)
      ⟨133, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 2 hp) Q2.T133_36_2 Q2.hfix133_36_2 Q2.hinj133_36_2
      Q2.hcardT133_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_36_2 i) (Q2.hfix133_36_2 i) _)
      colCert_133_36_2.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_36_3 (hp : 3 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 3 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp)) T133_36
      hfix133_36 hinj133_36 hcardT133_36
      (fun i => conj_mem_of_fixedPoints _ _ (T133_36 i) (hfix133_36 i) _)
      ⟨133, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 3 hp) Q2.T133_36_2 Q2.hfix133_36_2 Q2.hinj133_36_2
      Q2.hcardT133_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_36_2 i) (Q2.hfix133_36_2 i) _)
      colCert_133_36_3.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_36_4 (hp : 4 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 4 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp)) T133_36
      hfix133_36 hinj133_36 hcardT133_36
      (fun i => conj_mem_of_fixedPoints _ _ (T133_36 i) (hfix133_36 i) _)
      ⟨133, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 4 hp) Q2.T133_36_2 Q2.hfix133_36_2 Q2.hinj133_36_2
      Q2.hcardT133_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_36_2 i) (Q2.hfix133_36_2 i) _)
      colCert_133_36_4.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_36_5 (hp : 5 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 5 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨133, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp)) T133_36
      hfix133_36 hinj133_36 hcardT133_36
      (fun i => conj_mem_of_fixedPoints _ _ (T133_36 i) (hfix133_36 i) _)
      ⟨133, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 5 hp) Q2.T133_36_2 Q2.hfix133_36_2 Q2.hinj133_36_2
      Q2.hcardT133_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_36_2 i) (Q2.hfix133_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨133, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T133_36 = colFn colCertDiv_133_36_5.D1 (m := 5) from colCertDiv_133_36_5.bind1,
    show colData2 (⟨133, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 5 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T133_36_2 = colFn colCertDiv_133_36_5.D2 (m := 5) from colCertDiv_133_36_5.bind2]
  rw [alnId_133 j hj]
  exact fastcode_of_div ⟨133, by decide⟩ _ _ _
    ((alnId_133 j hj) ▸ Q2.listedAt (⟨133, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨133, by decide⟩ : Fin 148) hj hq).1) colCertDiv_133_36_5_match


theorem leaf_133_36_10 (hp : 10 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 10 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨133, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp)) T133_36
      hfix133_36 hinj133_36 hcardT133_36
      (fun i => conj_mem_of_fixedPoints _ _ (T133_36 i) (hfix133_36 i) _)
      ⟨133, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 10 hp) Q2.T133_36_2 Q2.hfix133_36_2 Q2.hinj133_36_2
      Q2.hcardT133_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_36_2 i) (Q2.hfix133_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨133, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T133_36 = colFn colCertDiv_133_36_10.D1 (m := 5) from colCertDiv_133_36_10.bind1,
    show colData2 (⟨133, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 10 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T133_36_2 = colFn colCertDiv_133_36_10.D2 (m := 5) from colCertDiv_133_36_10.bind2]
  rw [alnId_133 j hj]
  exact fastcode_of_div ⟨133, by decide⟩ _ _ _
    ((alnId_133 j hj) ▸ Q2.listedAt (⟨133, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨133, by decide⟩ : Fin 148) hj hq).1) colCertDiv_133_36_10_match


theorem leaf_133_36_15 (hp : 15 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 15 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨133, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp)) T133_36
      hfix133_36 hinj133_36 hcardT133_36
      (fun i => conj_mem_of_fixedPoints _ _ (T133_36 i) (hfix133_36 i) _)
      ⟨133, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 15 hp) Q2.T133_36_2 Q2.hfix133_36_2 Q2.hinj133_36_2
      Q2.hcardT133_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_36_2 i) (Q2.hfix133_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨133, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T133_36 = colFn colCertDiv_133_36_15.D1 (m := 5) from colCertDiv_133_36_15.bind1,
    show colData2 (⟨133, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 15 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T133_36_2 = colFn colCertDiv_133_36_15.D2 (m := 5) from colCertDiv_133_36_15.bind2]
  rw [alnId_133 j hj]
  exact fastcode_of_div ⟨133, by decide⟩ _ _ _
    ((alnId_133 j hj) ▸ Q2.listedAt (⟨133, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨133, by decide⟩ : Fin 148) hj hq).1) colCertDiv_133_36_15_match


theorem leaf_133_36_20 (hp : 20 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 20 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨133, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp)) T133_36
      hfix133_36 hinj133_36 hcardT133_36
      (fun i => conj_mem_of_fixedPoints _ _ (T133_36 i) (hfix133_36 i) _)
      ⟨133, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 20 hp) Q2.T133_36_2 Q2.hfix133_36_2 Q2.hinj133_36_2
      Q2.hcardT133_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_36_2 i) (Q2.hfix133_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨133, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T133_36 = colFn colCertDiv_133_36_20.D1 (m := 5) from colCertDiv_133_36_20.bind1,
    show colData2 (⟨133, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 20 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T133_36_2 = colFn colCertDiv_133_36_20.D2 (m := 5) from colCertDiv_133_36_20.bind2]
  rw [alnId_133 j hj]
  exact fastcode_of_div ⟨133, by decide⟩ _ _ _
    ((alnId_133 j hj) ▸ Q2.listedAt (⟨133, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨133, by decide⟩ : Fin 148) hj hq).1) colCertDiv_133_36_20_match


theorem leaf_133_39_0 (hp : 0 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 0 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp)) T133_39
      hfix133_39 hinj133_39 hcardT133_39
      (fun i => conj_mem_of_fixedPoints _ _ (T133_39 i) (hfix133_39 i) _)
      ⟨133, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 0 hp) Q2.T133_39_2 Q2.hfix133_39_2 Q2.hinj133_39_2
      Q2.hcardT133_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_39_2 i) (Q2.hfix133_39_2 i) _)
      colCert_133_39_0.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_39_1 (hp : 1 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 1 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp)) T133_39
      hfix133_39 hinj133_39 hcardT133_39
      (fun i => conj_mem_of_fixedPoints _ _ (T133_39 i) (hfix133_39 i) _)
      ⟨133, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 1 hp) Q2.T133_39_2 Q2.hfix133_39_2 Q2.hinj133_39_2
      Q2.hcardT133_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_39_2 i) (Q2.hfix133_39_2 i) _)
      colCert_133_39_1.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_39_2 (hp : 2 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 2 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp)) T133_39
      hfix133_39 hinj133_39 hcardT133_39
      (fun i => conj_mem_of_fixedPoints _ _ (T133_39 i) (hfix133_39 i) _)
      ⟨133, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 2 hp) Q2.T133_39_2 Q2.hfix133_39_2 Q2.hinj133_39_2
      Q2.hcardT133_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_39_2 i) (Q2.hfix133_39_2 i) _)
      colCert_133_39_2.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_39_3 (hp : 3 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 3 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp)) T133_39
      hfix133_39 hinj133_39 hcardT133_39
      (fun i => conj_mem_of_fixedPoints _ _ (T133_39 i) (hfix133_39 i) _)
      ⟨133, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 3 hp) Q2.T133_39_2 Q2.hfix133_39_2 Q2.hinj133_39_2
      Q2.hcardT133_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_39_2 i) (Q2.hfix133_39_2 i) _)
      colCert_133_39_3.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_39_4 (hp : 4 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 4 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp)) T133_39
      hfix133_39 hinj133_39 hcardT133_39
      (fun i => conj_mem_of_fixedPoints _ _ (T133_39 i) (hfix133_39 i) _)
      ⟨133, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 4 hp) Q2.T133_39_2 Q2.hfix133_39_2 Q2.hinj133_39_2
      Q2.hcardT133_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_39_2 i) (Q2.hfix133_39_2 i) _)
      colCert_133_39_4.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_39_5 (hp : 5 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 5 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp)) T133_39
      hfix133_39 hinj133_39 hcardT133_39
      (fun i => conj_mem_of_fixedPoints _ _ (T133_39 i) (hfix133_39 i) _)
      ⟨133, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 5 hp) Q2.T133_39_2 Q2.hfix133_39_2 Q2.hinj133_39_2
      Q2.hcardT133_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_39_2 i) (Q2.hfix133_39_2 i) _)
      colCert_133_39_5.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_39_10 (hp : 10 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 10 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨133, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp)) T133_39
      hfix133_39 hinj133_39 hcardT133_39
      (fun i => conj_mem_of_fixedPoints _ _ (T133_39 i) (hfix133_39 i) _)
      ⟨133, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 10 hp) Q2.T133_39_2 Q2.hfix133_39_2 Q2.hinj133_39_2
      Q2.hcardT133_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_39_2 i) (Q2.hfix133_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨133, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T133_39 = colFn colCertDiv_133_39_10.D1 (m := 5) from colCertDiv_133_39_10.bind1,
    show colData2 (⟨133, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 10 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T133_39_2 = colFn colCertDiv_133_39_10.D2 (m := 5) from colCertDiv_133_39_10.bind2]
  rw [alnId_133 j hj]
  exact fastcode_of_div ⟨133, by decide⟩ _ _ _
    ((alnId_133 j hj) ▸ Q2.listedAt (⟨133, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨133, by decide⟩ : Fin 148) hj hq).1) colCertDiv_133_39_10_match


theorem leaf_133_39_15 (hp : 15 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 15 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨133, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp)) T133_39
      hfix133_39 hinj133_39 hcardT133_39
      (fun i => conj_mem_of_fixedPoints _ _ (T133_39 i) (hfix133_39 i) _)
      ⟨133, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 15 hp) Q2.T133_39_2 Q2.hfix133_39_2 Q2.hinj133_39_2
      Q2.hcardT133_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_39_2 i) (Q2.hfix133_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨133, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T133_39 = colFn colCertDiv_133_39_15.D1 (m := 5) from colCertDiv_133_39_15.bind1,
    show colData2 (⟨133, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 15 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T133_39_2 = colFn colCertDiv_133_39_15.D2 (m := 5) from colCertDiv_133_39_15.bind2]
  rw [alnId_133 j hj]
  exact fastcode_of_div ⟨133, by decide⟩ _ _ _
    ((alnId_133 j hj) ▸ Q2.listedAt (⟨133, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨133, by decide⟩ : Fin 148) hj hq).1) colCertDiv_133_39_15_match


theorem leaf_133_39_20 (hp : 20 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 20 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨133, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp)) T133_39
      hfix133_39 hinj133_39 hcardT133_39
      (fun i => conj_mem_of_fixedPoints _ _ (T133_39 i) (hfix133_39 i) _)
      ⟨133, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 20 hp) Q2.T133_39_2 Q2.hfix133_39_2 Q2.hinj133_39_2
      Q2.hcardT133_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_39_2 i) (Q2.hfix133_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨133, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T133_39 = colFn colCertDiv_133_39_20.D1 (m := 5) from colCertDiv_133_39_20.bind1,
    show colData2 (⟨133, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 20 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T133_39_2 = colFn colCertDiv_133_39_20.D2 (m := 5) from colCertDiv_133_39_20.bind2]
  rw [alnId_133 j hj]
  exact fastcode_of_div ⟨133, by decide⟩ _ _ _
    ((alnId_133 j hj) ▸ Q2.listedAt (⟨133, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨133, by decide⟩ : Fin 148) hj hq).1) colCertDiv_133_39_20_match


theorem leaf_133_43_0 (hp : 0 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 0 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp)) T133_43
      hfix133_43 hinj133_43 hcardT133_43
      (fun i => conj_mem_of_fixedPoints _ _ (T133_43 i) (hfix133_43 i) _)
      ⟨133, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 0 hp) Q2.T133_43_2 Q2.hfix133_43_2 Q2.hinj133_43_2
      Q2.hcardT133_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_43_2 i) (Q2.hfix133_43_2 i) _)
      colCert_133_43_0.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_43_1 (hp : 1 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 1 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp)) T133_43
      hfix133_43 hinj133_43 hcardT133_43
      (fun i => conj_mem_of_fixedPoints _ _ (T133_43 i) (hfix133_43 i) _)
      ⟨133, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 1 hp) Q2.T133_43_2 Q2.hfix133_43_2 Q2.hinj133_43_2
      Q2.hcardT133_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_43_2 i) (Q2.hfix133_43_2 i) _)
      colCert_133_43_1.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_43_2 (hp : 2 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 2 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp)) T133_43
      hfix133_43 hinj133_43 hcardT133_43
      (fun i => conj_mem_of_fixedPoints _ _ (T133_43 i) (hfix133_43 i) _)
      ⟨133, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 2 hp) Q2.T133_43_2 Q2.hfix133_43_2 Q2.hinj133_43_2
      Q2.hcardT133_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_43_2 i) (Q2.hfix133_43_2 i) _)
      colCert_133_43_2.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_43_3 (hp : 3 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 3 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp)) T133_43
      hfix133_43 hinj133_43 hcardT133_43
      (fun i => conj_mem_of_fixedPoints _ _ (T133_43 i) (hfix133_43 i) _)
      ⟨133, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 3 hp) Q2.T133_43_2 Q2.hfix133_43_2 Q2.hinj133_43_2
      Q2.hcardT133_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_43_2 i) (Q2.hfix133_43_2 i) _)
      colCert_133_43_3.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_43_4 (hp : 4 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 4 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp)) T133_43
      hfix133_43 hinj133_43 hcardT133_43
      (fun i => conj_mem_of_fixedPoints _ _ (T133_43 i) (hfix133_43 i) _)
      ⟨133, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 4 hp) Q2.T133_43_2 Q2.hfix133_43_2 Q2.hinj133_43_2
      Q2.hcardT133_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_43_2 i) (Q2.hfix133_43_2 i) _)
      colCert_133_43_4.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_43_5 (hp : 5 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 5 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨133, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp)) T133_43
      hfix133_43 hinj133_43 hcardT133_43
      (fun i => conj_mem_of_fixedPoints _ _ (T133_43 i) (hfix133_43 i) _)
      ⟨133, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 5 hp) Q2.T133_43_2 Q2.hfix133_43_2 Q2.hinj133_43_2
      Q2.hcardT133_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_43_2 i) (Q2.hfix133_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨133, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T133_43 = colFn colCertDiv_133_43_5.D1 (m := 5) from colCertDiv_133_43_5.bind1,
    show colData2 (⟨133, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 5 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T133_43_2 = colFn colCertDiv_133_43_5.D2 (m := 5) from colCertDiv_133_43_5.bind2]
  rw [alnId_133 j hj]
  exact fastcode_of_div ⟨133, by decide⟩ _ _ _
    ((alnId_133 j hj) ▸ Q2.listedAt (⟨133, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨133, by decide⟩ : Fin 148) hj hq).1) colCertDiv_133_43_5_match


theorem leaf_133_43_10 (hp : 10 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 10 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨133, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp)) T133_43
      hfix133_43 hinj133_43 hcardT133_43
      (fun i => conj_mem_of_fixedPoints _ _ (T133_43 i) (hfix133_43 i) _)
      ⟨133, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 10 hp) Q2.T133_43_2 Q2.hfix133_43_2 Q2.hinj133_43_2
      Q2.hcardT133_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_43_2 i) (Q2.hfix133_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨133, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T133_43 = colFn colCertDiv_133_43_10.D1 (m := 5) from colCertDiv_133_43_10.bind1,
    show colData2 (⟨133, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 10 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T133_43_2 = colFn colCertDiv_133_43_10.D2 (m := 5) from colCertDiv_133_43_10.bind2]
  rw [alnId_133 j hj]
  exact fastcode_of_div ⟨133, by decide⟩ _ _ _
    ((alnId_133 j hj) ▸ Q2.listedAt (⟨133, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨133, by decide⟩ : Fin 148) hj hq).1) colCertDiv_133_43_10_match


theorem leaf_133_43_15 (hp : 15 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 15 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨133, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp)) T133_43
      hfix133_43 hinj133_43 hcardT133_43
      (fun i => conj_mem_of_fixedPoints _ _ (T133_43 i) (hfix133_43 i) _)
      ⟨133, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 15 hp) Q2.T133_43_2 Q2.hfix133_43_2 Q2.hinj133_43_2
      Q2.hcardT133_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_43_2 i) (Q2.hfix133_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨133, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T133_43 = colFn colCertDiv_133_43_15.D1 (m := 5) from colCertDiv_133_43_15.bind1,
    show colData2 (⟨133, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 15 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T133_43_2 = colFn colCertDiv_133_43_15.D2 (m := 5) from colCertDiv_133_43_15.bind2]
  rw [alnId_133 j hj]
  exact fastcode_of_div ⟨133, by decide⟩ _ _ _
    ((alnId_133 j hj) ▸ Q2.listedAt (⟨133, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨133, by decide⟩ : Fin 148) hj hq).1) colCertDiv_133_43_15_match


theorem leaf_133_43_20 (hp : 20 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 20 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨133, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp)) T133_43
      hfix133_43 hinj133_43 hcardT133_43
      (fun i => conj_mem_of_fixedPoints _ _ (T133_43 i) (hfix133_43 i) _)
      ⟨133, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 20 hp) Q2.T133_43_2 Q2.hfix133_43_2 Q2.hinj133_43_2
      Q2.hcardT133_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_43_2 i) (Q2.hfix133_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨133, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T133_43 = colFn colCertDiv_133_43_20.D1 (m := 5) from colCertDiv_133_43_20.bind1,
    show colData2 (⟨133, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 20 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T133_43_2 = colFn colCertDiv_133_43_20.D2 (m := 5) from colCertDiv_133_43_20.bind2]
  rw [alnId_133 j hj]
  exact fastcode_of_div ⟨133, by decide⟩ _ _ _
    ((alnId_133 j hj) ▸ Q2.listedAt (⟨133, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨133, by decide⟩ : Fin 148) hj hq).1) colCertDiv_133_43_20_match


theorem leaf_133_50_0 (hp : 0 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 0 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp)) T133_50
      hfix133_50 hinj133_50 hcardT133_50
      (fun i => conj_mem_of_fixedPoints _ _ (T133_50 i) (hfix133_50 i) _)
      ⟨133, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 0 hp) Q2.T133_50_2 Q2.hfix133_50_2 Q2.hinj133_50_2
      Q2.hcardT133_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_50_2 i) (Q2.hfix133_50_2 i) _)
      colCert_133_50_0.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_50_1 (hp : 1 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 1 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp)) T133_50
      hfix133_50 hinj133_50 hcardT133_50
      (fun i => conj_mem_of_fixedPoints _ _ (T133_50 i) (hfix133_50 i) _)
      ⟨133, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 1 hp) Q2.T133_50_2 Q2.hfix133_50_2 Q2.hinj133_50_2
      Q2.hcardT133_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_50_2 i) (Q2.hfix133_50_2 i) _)
      colCert_133_50_1.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_50_2 (hp : 2 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 2 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp)) T133_50
      hfix133_50 hinj133_50 hcardT133_50
      (fun i => conj_mem_of_fixedPoints _ _ (T133_50 i) (hfix133_50 i) _)
      ⟨133, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 2 hp) Q2.T133_50_2 Q2.hfix133_50_2 Q2.hinj133_50_2
      Q2.hcardT133_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_50_2 i) (Q2.hfix133_50_2 i) _)
      colCert_133_50_2.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_50_3 (hp : 3 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 3 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp)) T133_50
      hfix133_50 hinj133_50 hcardT133_50
      (fun i => conj_mem_of_fixedPoints _ _ (T133_50 i) (hfix133_50 i) _)
      ⟨133, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 3 hp) Q2.T133_50_2 Q2.hfix133_50_2 Q2.hinj133_50_2
      Q2.hcardT133_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_50_2 i) (Q2.hfix133_50_2 i) _)
      colCert_133_50_3.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_50_4 (hp : 4 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 4 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp)) T133_50
      hfix133_50 hinj133_50 hcardT133_50
      (fun i => conj_mem_of_fixedPoints _ _ (T133_50 i) (hfix133_50 i) _)
      ⟨133, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 4 hp) Q2.T133_50_2 Q2.hfix133_50_2 Q2.hinj133_50_2
      Q2.hcardT133_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_50_2 i) (Q2.hfix133_50_2 i) _)
      colCert_133_50_4.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_50_5 (hp : 5 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 5 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨133, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp)) T133_50
      hfix133_50 hinj133_50 hcardT133_50
      (fun i => conj_mem_of_fixedPoints _ _ (T133_50 i) (hfix133_50 i) _)
      ⟨133, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 5 hp) Q2.T133_50_2 Q2.hfix133_50_2 Q2.hinj133_50_2
      Q2.hcardT133_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_50_2 i) (Q2.hfix133_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨133, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T133_50 = colFn colCertDiv_133_50_5.D1 (m := 5) from colCertDiv_133_50_5.bind1,
    show colData2 (⟨133, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 5 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T133_50_2 = colFn colCertDiv_133_50_5.D2 (m := 5) from colCertDiv_133_50_5.bind2]
  rw [alnId_133 j hj]
  exact fastcode_of_div ⟨133, by decide⟩ _ _ _
    ((alnId_133 j hj) ▸ Q2.listedAt (⟨133, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨133, by decide⟩ : Fin 148) hj hq).1) colCertDiv_133_50_5_match


theorem leaf_133_50_10 (hp : 10 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 10 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨133, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp)) T133_50
      hfix133_50 hinj133_50 hcardT133_50
      (fun i => conj_mem_of_fixedPoints _ _ (T133_50 i) (hfix133_50 i) _)
      ⟨133, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 10 hp) Q2.T133_50_2 Q2.hfix133_50_2 Q2.hinj133_50_2
      Q2.hcardT133_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_50_2 i) (Q2.hfix133_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨133, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T133_50 = colFn colCertDiv_133_50_10.D1 (m := 5) from colCertDiv_133_50_10.bind1,
    show colData2 (⟨133, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 10 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T133_50_2 = colFn colCertDiv_133_50_10.D2 (m := 5) from colCertDiv_133_50_10.bind2]
  rw [alnId_133 j hj]
  exact fastcode_of_div ⟨133, by decide⟩ _ _ _
    ((alnId_133 j hj) ▸ Q2.listedAt (⟨133, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨133, by decide⟩ : Fin 148) hj hq).1) colCertDiv_133_50_10_match


theorem leaf_133_50_15 (hp : 15 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 15 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨133, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp)) T133_50
      hfix133_50 hinj133_50 hcardT133_50
      (fun i => conj_mem_of_fixedPoints _ _ (T133_50 i) (hfix133_50 i) _)
      ⟨133, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 15 hp) Q2.T133_50_2 Q2.hfix133_50_2 Q2.hinj133_50_2
      Q2.hcardT133_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_50_2 i) (Q2.hfix133_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨133, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T133_50 = colFn colCertDiv_133_50_15.D1 (m := 5) from colCertDiv_133_50_15.bind1,
    show colData2 (⟨133, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 15 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T133_50_2 = colFn colCertDiv_133_50_15.D2 (m := 5) from colCertDiv_133_50_15.bind2]
  rw [alnId_133 j hj]
  exact fastcode_of_div ⟨133, by decide⟩ _ _ _
    ((alnId_133 j hj) ▸ Q2.listedAt (⟨133, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨133, by decide⟩ : Fin 148) hj hq).1) colCertDiv_133_50_15_match


theorem leaf_133_50_20 (hp : 20 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 20 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨133, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp)) T133_50
      hfix133_50 hinj133_50 hcardT133_50
      (fun i => conj_mem_of_fixedPoints _ _ (T133_50 i) (hfix133_50 i) _)
      ⟨133, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 20 hp) Q2.T133_50_2 Q2.hfix133_50_2 Q2.hinj133_50_2
      Q2.hcardT133_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_50_2 i) (Q2.hfix133_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨133, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T133_50 = colFn colCertDiv_133_50_20.D1 (m := 5) from colCertDiv_133_50_20.bind1,
    show colData2 (⟨133, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 20 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T133_50_2 = colFn colCertDiv_133_50_20.D2 (m := 5) from colCertDiv_133_50_20.bind2]
  rw [alnId_133 j hj]
  exact fastcode_of_div ⟨133, by decide⟩ _ _ _
    ((alnId_133 j hj) ▸ Q2.listedAt (⟨133, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨133, by decide⟩ : Fin 148) hj hq).1) colCertDiv_133_50_20_match


theorem leaf_133_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T133_53
      hfix133_53 hinj133_53 hcardT133_53
      (fun i => conj_mem_of_fixedPoints _ _ (T133_53 i) (hfix133_53 i) _)
      ⟨133, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T133_53_2 Q2.hfix133_53_2 Q2.hinj133_53_2
      Q2.hcardT133_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_53_2 i) (Q2.hfix133_53_2 i) _)
      colCert_133_53_0.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T133_53
      hfix133_53 hinj133_53 hcardT133_53
      (fun i => conj_mem_of_fixedPoints _ _ (T133_53 i) (hfix133_53 i) _)
      ⟨133, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T133_53_2 Q2.hfix133_53_2 Q2.hinj133_53_2
      Q2.hcardT133_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_53_2 i) (Q2.hfix133_53_2 i) _)
      colCert_133_53_1.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T133_53
      hfix133_53 hinj133_53 hcardT133_53
      (fun i => conj_mem_of_fixedPoints _ _ (T133_53 i) (hfix133_53 i) _)
      ⟨133, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T133_53_2 Q2.hfix133_53_2 Q2.hinj133_53_2
      Q2.hcardT133_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_53_2 i) (Q2.hfix133_53_2 i) _)
      colCert_133_53_2.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T133_53
      hfix133_53 hinj133_53 hcardT133_53
      (fun i => conj_mem_of_fixedPoints _ _ (T133_53 i) (hfix133_53 i) _)
      ⟨133, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T133_53_2 Q2.hfix133_53_2 Q2.hinj133_53_2
      Q2.hcardT133_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_53_2 i) (Q2.hfix133_53_2 i) _)
      colCert_133_53_3.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T133_53
      hfix133_53 hinj133_53 hcardT133_53
      (fun i => conj_mem_of_fixedPoints _ _ (T133_53 i) (hfix133_53 i) _)
      ⟨133, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T133_53_2 Q2.hfix133_53_2 Q2.hinj133_53_2
      Q2.hcardT133_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_53_2 i) (Q2.hfix133_53_2 i) _)
      colCert_133_53_4.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T133_53
      hfix133_53 hinj133_53 hcardT133_53
      (fun i => conj_mem_of_fixedPoints _ _ (T133_53 i) (hfix133_53 i) _)
      ⟨133, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T133_53_2 Q2.hfix133_53_2 Q2.hinj133_53_2
      Q2.hcardT133_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_53_2 i) (Q2.hfix133_53_2 i) _)
      colCert_133_53_5.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T133_53
      hfix133_53 hinj133_53 hcardT133_53
      (fun i => conj_mem_of_fixedPoints _ _ (T133_53 i) (hfix133_53 i) _)
      ⟨133, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T133_53_2 Q2.hfix133_53_2 Q2.hinj133_53_2
      Q2.hcardT133_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_53_2 i) (Q2.hfix133_53_2 i) _)
      colCert_133_53_10.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T133_53
      hfix133_53 hinj133_53 hcardT133_53
      (fun i => conj_mem_of_fixedPoints _ _ (T133_53 i) (hfix133_53 i) _)
      ⟨133, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T133_53_2 Q2.hfix133_53_2 Q2.hinj133_53_2
      Q2.hcardT133_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_53_2 i) (Q2.hfix133_53_2 i) _)
      colCert_133_53_15.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T133_53
      hfix133_53 hinj133_53 hcardT133_53
      (fun i => conj_mem_of_fixedPoints _ _ (T133_53 i) (hfix133_53 i) _)
      ⟨133, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T133_53_2 Q2.hfix133_53_2 Q2.hinj133_53_2
      Q2.hcardT133_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_53_2 i) (Q2.hfix133_53_2 i) _)
      colCert_133_53_20.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_83_0 (hp : 0 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 0 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 0 (transLenTr ⟨83, by decide⟩ 0 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 0 (transLenTr ⟨83, by decide⟩ 0 hp)) T133_83
      hfix133_83 hinj133_83 hcardT133_83
      (fun i => conj_mem_of_fixedPoints _ _ (T133_83 i) (hfix133_83 i) _)
      ⟨133, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 0 hp) Q2.T133_83_2 Q2.hfix133_83_2 Q2.hinj133_83_2
      Q2.hcardT133_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_83_2 i) (Q2.hfix133_83_2 i) _)
      colCert_133_83_0.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_83_1 (hp : 1 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 1 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 1 (transLenTr ⟨83, by decide⟩ 1 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 1 (transLenTr ⟨83, by decide⟩ 1 hp)) T133_83
      hfix133_83 hinj133_83 hcardT133_83
      (fun i => conj_mem_of_fixedPoints _ _ (T133_83 i) (hfix133_83 i) _)
      ⟨133, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 1 hp) Q2.T133_83_2 Q2.hfix133_83_2 Q2.hinj133_83_2
      Q2.hcardT133_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_83_2 i) (Q2.hfix133_83_2 i) _)
      colCert_133_83_1.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_83_2 (hp : 2 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 2 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 2 (transLenTr ⟨83, by decide⟩ 2 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 2 (transLenTr ⟨83, by decide⟩ 2 hp)) T133_83
      hfix133_83 hinj133_83 hcardT133_83
      (fun i => conj_mem_of_fixedPoints _ _ (T133_83 i) (hfix133_83 i) _)
      ⟨133, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 2 hp) Q2.T133_83_2 Q2.hfix133_83_2 Q2.hinj133_83_2
      Q2.hcardT133_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_83_2 i) (Q2.hfix133_83_2 i) _)
      colCert_133_83_2.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_83_3 (hp : 3 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 3 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 3 (transLenTr ⟨83, by decide⟩ 3 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 3 (transLenTr ⟨83, by decide⟩ 3 hp)) T133_83
      hfix133_83 hinj133_83 hcardT133_83
      (fun i => conj_mem_of_fixedPoints _ _ (T133_83 i) (hfix133_83 i) _)
      ⟨133, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 3 hp) Q2.T133_83_2 Q2.hfix133_83_2 Q2.hinj133_83_2
      Q2.hcardT133_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_83_2 i) (Q2.hfix133_83_2 i) _)
      colCert_133_83_3.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_83_4 (hp : 4 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 4 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 4 (transLenTr ⟨83, by decide⟩ 4 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 4 (transLenTr ⟨83, by decide⟩ 4 hp)) T133_83
      hfix133_83 hinj133_83 hcardT133_83
      (fun i => conj_mem_of_fixedPoints _ _ (T133_83 i) (hfix133_83 i) _)
      ⟨133, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 4 hp) Q2.T133_83_2 Q2.hfix133_83_2 Q2.hinj133_83_2
      Q2.hcardT133_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_83_2 i) (Q2.hfix133_83_2 i) _)
      colCert_133_83_4.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_83_5 (hp : 5 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 5 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 5 (transLenTr ⟨83, by decide⟩ 5 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 5 (transLenTr ⟨83, by decide⟩ 5 hp)) T133_83
      hfix133_83 hinj133_83 hcardT133_83
      (fun i => conj_mem_of_fixedPoints _ _ (T133_83 i) (hfix133_83 i) _)
      ⟨133, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 5 hp) Q2.T133_83_2 Q2.hfix133_83_2 Q2.hinj133_83_2
      Q2.hcardT133_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_83_2 i) (Q2.hfix133_83_2 i) _)
      colCert_133_83_5.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_83_10 (hp : 10 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 10 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 10 (transLenTr ⟨83, by decide⟩ 10 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 10 (transLenTr ⟨83, by decide⟩ 10 hp)) T133_83
      hfix133_83 hinj133_83 hcardT133_83
      (fun i => conj_mem_of_fixedPoints _ _ (T133_83 i) (hfix133_83 i) _)
      ⟨133, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 10 hp) Q2.T133_83_2 Q2.hfix133_83_2 Q2.hinj133_83_2
      Q2.hcardT133_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_83_2 i) (Q2.hfix133_83_2 i) _)
      colCert_133_83_10.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_83_15 (hp : 15 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 15 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 15 (transLenTr ⟨83, by decide⟩ 15 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 15 (transLenTr ⟨83, by decide⟩ 15 hp)) T133_83
      hfix133_83 hinj133_83 hcardT133_83
      (fun i => conj_mem_of_fixedPoints _ _ (T133_83 i) (hfix133_83 i) _)
      ⟨133, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 15 hp) Q2.T133_83_2 Q2.hfix133_83_2 Q2.hinj133_83_2
      Q2.hcardT133_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_83_2 i) (Q2.hfix133_83_2 i) _)
      colCert_133_83_15.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_83_20 (hp : 20 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 20 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 20 (transLenTr ⟨83, by decide⟩ 20 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 20 (transLenTr ⟨83, by decide⟩ 20 hp)) T133_83
      hfix133_83 hinj133_83 hcardT133_83
      (fun i => conj_mem_of_fixedPoints _ _ (T133_83 i) (hfix133_83 i) _)
      ⟨133, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 20 hp) Q2.T133_83_2 Q2.hfix133_83_2 Q2.hinj133_83_2
      Q2.hcardT133_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_83_2 i) (Q2.hfix133_83_2 i) _)
      colCert_133_83_20.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_94_0 (hp : 0 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 0 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 0 (transLenTr ⟨94, by decide⟩ 0 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 0 (transLenTr ⟨94, by decide⟩ 0 hp)) T133_94
      hfix133_94 hinj133_94 hcardT133_94
      (fun i => conj_mem_of_fixedPoints _ _ (T133_94 i) (hfix133_94 i) _)
      ⟨133, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 0 hp) Q2.T133_94_2 Q2.hfix133_94_2 Q2.hinj133_94_2
      Q2.hcardT133_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_94_2 i) (Q2.hfix133_94_2 i) _)
      colCert_133_94_0.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_94_1 (hp : 1 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 1 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 1 (transLenTr ⟨94, by decide⟩ 1 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 1 (transLenTr ⟨94, by decide⟩ 1 hp)) T133_94
      hfix133_94 hinj133_94 hcardT133_94
      (fun i => conj_mem_of_fixedPoints _ _ (T133_94 i) (hfix133_94 i) _)
      ⟨133, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 1 hp) Q2.T133_94_2 Q2.hfix133_94_2 Q2.hinj133_94_2
      Q2.hcardT133_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_94_2 i) (Q2.hfix133_94_2 i) _)
      colCert_133_94_1.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_94_2 (hp : 2 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 2 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 2 (transLenTr ⟨94, by decide⟩ 2 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 2 (transLenTr ⟨94, by decide⟩ 2 hp)) T133_94
      hfix133_94 hinj133_94 hcardT133_94
      (fun i => conj_mem_of_fixedPoints _ _ (T133_94 i) (hfix133_94 i) _)
      ⟨133, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 2 hp) Q2.T133_94_2 Q2.hfix133_94_2 Q2.hinj133_94_2
      Q2.hcardT133_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_94_2 i) (Q2.hfix133_94_2 i) _)
      colCert_133_94_2.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_94_3 (hp : 3 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 3 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 3 (transLenTr ⟨94, by decide⟩ 3 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 3 (transLenTr ⟨94, by decide⟩ 3 hp)) T133_94
      hfix133_94 hinj133_94 hcardT133_94
      (fun i => conj_mem_of_fixedPoints _ _ (T133_94 i) (hfix133_94 i) _)
      ⟨133, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 3 hp) Q2.T133_94_2 Q2.hfix133_94_2 Q2.hinj133_94_2
      Q2.hcardT133_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_94_2 i) (Q2.hfix133_94_2 i) _)
      colCert_133_94_3.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_94_4 (hp : 4 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 4 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 4 (transLenTr ⟨94, by decide⟩ 4 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 4 (transLenTr ⟨94, by decide⟩ 4 hp)) T133_94
      hfix133_94 hinj133_94 hcardT133_94
      (fun i => conj_mem_of_fixedPoints _ _ (T133_94 i) (hfix133_94 i) _)
      ⟨133, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 4 hp) Q2.T133_94_2 Q2.hfix133_94_2 Q2.hinj133_94_2
      Q2.hcardT133_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_94_2 i) (Q2.hfix133_94_2 i) _)
      colCert_133_94_4.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_94_5 (hp : 5 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 5 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 5 (transLenTr ⟨94, by decide⟩ 5 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 5 (transLenTr ⟨94, by decide⟩ 5 hp)) T133_94
      hfix133_94 hinj133_94 hcardT133_94
      (fun i => conj_mem_of_fixedPoints _ _ (T133_94 i) (hfix133_94 i) _)
      ⟨133, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 5 hp) Q2.T133_94_2 Q2.hfix133_94_2 Q2.hinj133_94_2
      Q2.hcardT133_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_94_2 i) (Q2.hfix133_94_2 i) _)
      colCert_133_94_5.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_94_10 (hp : 10 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 10 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 10 (transLenTr ⟨94, by decide⟩ 10 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 10 (transLenTr ⟨94, by decide⟩ 10 hp)) T133_94
      hfix133_94 hinj133_94 hcardT133_94
      (fun i => conj_mem_of_fixedPoints _ _ (T133_94 i) (hfix133_94 i) _)
      ⟨133, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 10 hp) Q2.T133_94_2 Q2.hfix133_94_2 Q2.hinj133_94_2
      Q2.hcardT133_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_94_2 i) (Q2.hfix133_94_2 i) _)
      colCert_133_94_10.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_94_15 (hp : 15 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 15 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 15 (transLenTr ⟨94, by decide⟩ 15 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 15 (transLenTr ⟨94, by decide⟩ 15 hp)) T133_94
      hfix133_94 hinj133_94 hcardT133_94
      (fun i => conj_mem_of_fixedPoints _ _ (T133_94 i) (hfix133_94 i) _)
      ⟨133, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 15 hp) Q2.T133_94_2 Q2.hfix133_94_2 Q2.hinj133_94_2
      Q2.hcardT133_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_94_2 i) (Q2.hfix133_94_2 i) _)
      colCert_133_94_15.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_94_20 (hp : 20 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 20 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 20 (transLenTr ⟨94, by decide⟩ 20 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 20 (transLenTr ⟨94, by decide⟩ 20 hp)) T133_94
      hfix133_94 hinj133_94 hcardT133_94
      (fun i => conj_mem_of_fixedPoints _ _ (T133_94 i) (hfix133_94 i) _)
      ⟨133, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 20 hp) Q2.T133_94_2 Q2.hfix133_94_2 Q2.hinj133_94_2
      Q2.hcardT133_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_94_2 i) (Q2.hfix133_94_2 i) _)
      colCert_133_94_20.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_98_0 (hp : 0 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 0 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 0 (transLenTr ⟨98, by decide⟩ 0 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 0 (transLenTr ⟨98, by decide⟩ 0 hp)) T133_98
      hfix133_98 hinj133_98 hcardT133_98
      (fun i => conj_mem_of_fixedPoints _ _ (T133_98 i) (hfix133_98 i) _)
      ⟨133, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 0 hp) Q2.T133_98_2 Q2.hfix133_98_2 Q2.hinj133_98_2
      Q2.hcardT133_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_98_2 i) (Q2.hfix133_98_2 i) _)
      colCert_133_98_0.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_98_1 (hp : 1 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 1 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 1 (transLenTr ⟨98, by decide⟩ 1 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 1 (transLenTr ⟨98, by decide⟩ 1 hp)) T133_98
      hfix133_98 hinj133_98 hcardT133_98
      (fun i => conj_mem_of_fixedPoints _ _ (T133_98 i) (hfix133_98 i) _)
      ⟨133, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 1 hp) Q2.T133_98_2 Q2.hfix133_98_2 Q2.hinj133_98_2
      Q2.hcardT133_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_98_2 i) (Q2.hfix133_98_2 i) _)
      colCert_133_98_1.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_98_2 (hp : 2 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 2 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 2 (transLenTr ⟨98, by decide⟩ 2 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 2 (transLenTr ⟨98, by decide⟩ 2 hp)) T133_98
      hfix133_98 hinj133_98 hcardT133_98
      (fun i => conj_mem_of_fixedPoints _ _ (T133_98 i) (hfix133_98 i) _)
      ⟨133, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 2 hp) Q2.T133_98_2 Q2.hfix133_98_2 Q2.hinj133_98_2
      Q2.hcardT133_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_98_2 i) (Q2.hfix133_98_2 i) _)
      colCert_133_98_2.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_98_3 (hp : 3 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 3 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 3 (transLenTr ⟨98, by decide⟩ 3 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 3 (transLenTr ⟨98, by decide⟩ 3 hp)) T133_98
      hfix133_98 hinj133_98 hcardT133_98
      (fun i => conj_mem_of_fixedPoints _ _ (T133_98 i) (hfix133_98 i) _)
      ⟨133, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 3 hp) Q2.T133_98_2 Q2.hfix133_98_2 Q2.hinj133_98_2
      Q2.hcardT133_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_98_2 i) (Q2.hfix133_98_2 i) _)
      colCert_133_98_3.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_98_4 (hp : 4 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 4 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 4 (transLenTr ⟨98, by decide⟩ 4 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 4 (transLenTr ⟨98, by decide⟩ 4 hp)) T133_98
      hfix133_98 hinj133_98 hcardT133_98
      (fun i => conj_mem_of_fixedPoints _ _ (T133_98 i) (hfix133_98 i) _)
      ⟨133, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 4 hp) Q2.T133_98_2 Q2.hfix133_98_2 Q2.hinj133_98_2
      Q2.hcardT133_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_98_2 i) (Q2.hfix133_98_2 i) _)
      colCert_133_98_4.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_98_5 (hp : 5 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 5 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 5 (transLenTr ⟨98, by decide⟩ 5 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 5 (transLenTr ⟨98, by decide⟩ 5 hp)) T133_98
      hfix133_98 hinj133_98 hcardT133_98
      (fun i => conj_mem_of_fixedPoints _ _ (T133_98 i) (hfix133_98 i) _)
      ⟨133, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 5 hp) Q2.T133_98_2 Q2.hfix133_98_2 Q2.hinj133_98_2
      Q2.hcardT133_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_98_2 i) (Q2.hfix133_98_2 i) _)
      colCert_133_98_5.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_98_10 (hp : 10 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 10 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 10 (transLenTr ⟨98, by decide⟩ 10 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨133, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 10 (transLenTr ⟨98, by decide⟩ 10 hp)) T133_98
      hfix133_98 hinj133_98 hcardT133_98
      (fun i => conj_mem_of_fixedPoints _ _ (T133_98 i) (hfix133_98 i) _)
      ⟨133, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 10 hp) Q2.T133_98_2 Q2.hfix133_98_2 Q2.hinj133_98_2
      Q2.hcardT133_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_98_2 i) (Q2.hfix133_98_2 i) _)
      ?_).symm
  rw [show colData1 (⟨133, by decide⟩ : Fin 148)
        ((colE1 ⟨98, by decide⟩ 10 (transLenTr ⟨98, by decide⟩ 10 hp) : ↥(reps ⟨98, by decide⟩)) : Coordinate 1)
        T133_98 = colFn colCertDiv_133_98_10.D1 (m := 5) from colCertDiv_133_98_10.bind1,
    show colData2 (⟨133, by decide⟩ : Fin 148)
        ((colE2 ⟨98, by decide⟩ 10 hp : ↥(Q2.reps ⟨98, by decide⟩)) : Coordinate 2)
        Q2.T133_98_2 = colFn colCertDiv_133_98_10.D2 (m := 5) from colCertDiv_133_98_10.bind2]
  rw [alnId_133 j hj]
  exact fastcode_of_div ⟨133, by decide⟩ _ _ _
    ((alnId_133 j hj) ▸ Q2.listedAt (⟨133, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨133, by decide⟩ : Fin 148) hj hq).1) colCertDiv_133_98_10_match


theorem leaf_133_98_15 (hp : 15 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 15 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 15 (transLenTr ⟨98, by decide⟩ 15 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨133, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 15 (transLenTr ⟨98, by decide⟩ 15 hp)) T133_98
      hfix133_98 hinj133_98 hcardT133_98
      (fun i => conj_mem_of_fixedPoints _ _ (T133_98 i) (hfix133_98 i) _)
      ⟨133, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 15 hp) Q2.T133_98_2 Q2.hfix133_98_2 Q2.hinj133_98_2
      Q2.hcardT133_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_98_2 i) (Q2.hfix133_98_2 i) _)
      ?_).symm
  rw [show colData1 (⟨133, by decide⟩ : Fin 148)
        ((colE1 ⟨98, by decide⟩ 15 (transLenTr ⟨98, by decide⟩ 15 hp) : ↥(reps ⟨98, by decide⟩)) : Coordinate 1)
        T133_98 = colFn colCertDiv_133_98_15.D1 (m := 5) from colCertDiv_133_98_15.bind1,
    show colData2 (⟨133, by decide⟩ : Fin 148)
        ((colE2 ⟨98, by decide⟩ 15 hp : ↥(Q2.reps ⟨98, by decide⟩)) : Coordinate 2)
        Q2.T133_98_2 = colFn colCertDiv_133_98_15.D2 (m := 5) from colCertDiv_133_98_15.bind2]
  rw [alnId_133 j hj]
  exact fastcode_of_div ⟨133, by decide⟩ _ _ _
    ((alnId_133 j hj) ▸ Q2.listedAt (⟨133, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨133, by decide⟩ : Fin 148) hj hq).1) colCertDiv_133_98_15_match


theorem leaf_133_98_20 (hp : 20 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 20 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 20 (transLenTr ⟨98, by decide⟩ 20 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨133, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 20 (transLenTr ⟨98, by decide⟩ 20 hp)) T133_98
      hfix133_98 hinj133_98 hcardT133_98
      (fun i => conj_mem_of_fixedPoints _ _ (T133_98 i) (hfix133_98 i) _)
      ⟨133, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 20 hp) Q2.T133_98_2 Q2.hfix133_98_2 Q2.hinj133_98_2
      Q2.hcardT133_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_98_2 i) (Q2.hfix133_98_2 i) _)
      ?_).symm
  rw [show colData1 (⟨133, by decide⟩ : Fin 148)
        ((colE1 ⟨98, by decide⟩ 20 (transLenTr ⟨98, by decide⟩ 20 hp) : ↥(reps ⟨98, by decide⟩)) : Coordinate 1)
        T133_98 = colFn colCertDiv_133_98_20.D1 (m := 5) from colCertDiv_133_98_20.bind1,
    show colData2 (⟨133, by decide⟩ : Fin 148)
        ((colE2 ⟨98, by decide⟩ 20 hp : ↥(Q2.reps ⟨98, by decide⟩)) : Coordinate 2)
        Q2.T133_98_2 = colFn colCertDiv_133_98_20.D2 (m := 5) from colCertDiv_133_98_20.bind2]
  rw [alnId_133 j hj]
  exact fastcode_of_div ⟨133, by decide⟩ _ _ _
    ((alnId_133 j hj) ▸ Q2.listedAt (⟨133, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨133, by decide⟩ : Fin 148) hj hq).1) colCertDiv_133_98_20_match


theorem leaf_133_101_0 (hp : 0 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 0 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 0 (transLenTr ⟨101, by decide⟩ 0 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 0 (transLenTr ⟨101, by decide⟩ 0 hp)) T133_101
      hfix133_101 hinj133_101 hcardT133_101
      (fun i => conj_mem_of_fixedPoints _ _ (T133_101 i) (hfix133_101 i) _)
      ⟨133, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 0 hp) Q2.T133_101_2 Q2.hfix133_101_2 Q2.hinj133_101_2
      Q2.hcardT133_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_101_2 i) (Q2.hfix133_101_2 i) _)
      colCert_133_101_0.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_101_1 (hp : 1 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 1 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 1 (transLenTr ⟨101, by decide⟩ 1 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 1 (transLenTr ⟨101, by decide⟩ 1 hp)) T133_101
      hfix133_101 hinj133_101 hcardT133_101
      (fun i => conj_mem_of_fixedPoints _ _ (T133_101 i) (hfix133_101 i) _)
      ⟨133, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 1 hp) Q2.T133_101_2 Q2.hfix133_101_2 Q2.hinj133_101_2
      Q2.hcardT133_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_101_2 i) (Q2.hfix133_101_2 i) _)
      colCert_133_101_1.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_101_2 (hp : 2 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 2 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 2 (transLenTr ⟨101, by decide⟩ 2 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 2 (transLenTr ⟨101, by decide⟩ 2 hp)) T133_101
      hfix133_101 hinj133_101 hcardT133_101
      (fun i => conj_mem_of_fixedPoints _ _ (T133_101 i) (hfix133_101 i) _)
      ⟨133, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 2 hp) Q2.T133_101_2 Q2.hfix133_101_2 Q2.hinj133_101_2
      Q2.hcardT133_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_101_2 i) (Q2.hfix133_101_2 i) _)
      colCert_133_101_2.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_101_3 (hp : 3 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 3 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 3 (transLenTr ⟨101, by decide⟩ 3 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 3 (transLenTr ⟨101, by decide⟩ 3 hp)) T133_101
      hfix133_101 hinj133_101 hcardT133_101
      (fun i => conj_mem_of_fixedPoints _ _ (T133_101 i) (hfix133_101 i) _)
      ⟨133, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 3 hp) Q2.T133_101_2 Q2.hfix133_101_2 Q2.hinj133_101_2
      Q2.hcardT133_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_101_2 i) (Q2.hfix133_101_2 i) _)
      colCert_133_101_3.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_101_4 (hp : 4 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 4 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 4 (transLenTr ⟨101, by decide⟩ 4 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 4 (transLenTr ⟨101, by decide⟩ 4 hp)) T133_101
      hfix133_101 hinj133_101 hcardT133_101
      (fun i => conj_mem_of_fixedPoints _ _ (T133_101 i) (hfix133_101 i) _)
      ⟨133, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 4 hp) Q2.T133_101_2 Q2.hfix133_101_2 Q2.hinj133_101_2
      Q2.hcardT133_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_101_2 i) (Q2.hfix133_101_2 i) _)
      colCert_133_101_4.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_101_5 (hp : 5 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 5 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 5 (transLenTr ⟨101, by decide⟩ 5 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 5 (transLenTr ⟨101, by decide⟩ 5 hp)) T133_101
      hfix133_101 hinj133_101 hcardT133_101
      (fun i => conj_mem_of_fixedPoints _ _ (T133_101 i) (hfix133_101 i) _)
      ⟨133, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 5 hp) Q2.T133_101_2 Q2.hfix133_101_2 Q2.hinj133_101_2
      Q2.hcardT133_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_101_2 i) (Q2.hfix133_101_2 i) _)
      colCert_133_101_5.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_101_10 (hp : 10 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 10 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 10 (transLenTr ⟨101, by decide⟩ 10 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨133, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 10 (transLenTr ⟨101, by decide⟩ 10 hp)) T133_101
      hfix133_101 hinj133_101 hcardT133_101
      (fun i => conj_mem_of_fixedPoints _ _ (T133_101 i) (hfix133_101 i) _)
      ⟨133, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 10 hp) Q2.T133_101_2 Q2.hfix133_101_2 Q2.hinj133_101_2
      Q2.hcardT133_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_101_2 i) (Q2.hfix133_101_2 i) _)
      ?_).symm
  rw [show colData1 (⟨133, by decide⟩ : Fin 148)
        ((colE1 ⟨101, by decide⟩ 10 (transLenTr ⟨101, by decide⟩ 10 hp) : ↥(reps ⟨101, by decide⟩)) : Coordinate 1)
        T133_101 = colFn colCertDiv_133_101_10.D1 (m := 5) from colCertDiv_133_101_10.bind1,
    show colData2 (⟨133, by decide⟩ : Fin 148)
        ((colE2 ⟨101, by decide⟩ 10 hp : ↥(Q2.reps ⟨101, by decide⟩)) : Coordinate 2)
        Q2.T133_101_2 = colFn colCertDiv_133_101_10.D2 (m := 5) from colCertDiv_133_101_10.bind2]
  rw [alnId_133 j hj]
  exact fastcode_of_div ⟨133, by decide⟩ _ _ _
    ((alnId_133 j hj) ▸ Q2.listedAt (⟨133, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨133, by decide⟩ : Fin 148) hj hq).1) colCertDiv_133_101_10_match


theorem leaf_133_101_15 (hp : 15 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 15 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 15 (transLenTr ⟨101, by decide⟩ 15 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨133, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 15 (transLenTr ⟨101, by decide⟩ 15 hp)) T133_101
      hfix133_101 hinj133_101 hcardT133_101
      (fun i => conj_mem_of_fixedPoints _ _ (T133_101 i) (hfix133_101 i) _)
      ⟨133, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 15 hp) Q2.T133_101_2 Q2.hfix133_101_2 Q2.hinj133_101_2
      Q2.hcardT133_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_101_2 i) (Q2.hfix133_101_2 i) _)
      ?_).symm
  rw [show colData1 (⟨133, by decide⟩ : Fin 148)
        ((colE1 ⟨101, by decide⟩ 15 (transLenTr ⟨101, by decide⟩ 15 hp) : ↥(reps ⟨101, by decide⟩)) : Coordinate 1)
        T133_101 = colFn colCertDiv_133_101_15.D1 (m := 5) from colCertDiv_133_101_15.bind1,
    show colData2 (⟨133, by decide⟩ : Fin 148)
        ((colE2 ⟨101, by decide⟩ 15 hp : ↥(Q2.reps ⟨101, by decide⟩)) : Coordinate 2)
        Q2.T133_101_2 = colFn colCertDiv_133_101_15.D2 (m := 5) from colCertDiv_133_101_15.bind2]
  rw [alnId_133 j hj]
  exact fastcode_of_div ⟨133, by decide⟩ _ _ _
    ((alnId_133 j hj) ▸ Q2.listedAt (⟨133, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨133, by decide⟩ : Fin 148) hj hq).1) colCertDiv_133_101_15_match


theorem leaf_133_101_20 (hp : 20 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 20 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 20 (transLenTr ⟨101, by decide⟩ 20 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨133, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 20 (transLenTr ⟨101, by decide⟩ 20 hp)) T133_101
      hfix133_101 hinj133_101 hcardT133_101
      (fun i => conj_mem_of_fixedPoints _ _ (T133_101 i) (hfix133_101 i) _)
      ⟨133, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 20 hp) Q2.T133_101_2 Q2.hfix133_101_2 Q2.hinj133_101_2
      Q2.hcardT133_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_101_2 i) (Q2.hfix133_101_2 i) _)
      ?_).symm
  rw [show colData1 (⟨133, by decide⟩ : Fin 148)
        ((colE1 ⟨101, by decide⟩ 20 (transLenTr ⟨101, by decide⟩ 20 hp) : ↥(reps ⟨101, by decide⟩)) : Coordinate 1)
        T133_101 = colFn colCertDiv_133_101_20.D1 (m := 5) from colCertDiv_133_101_20.bind1,
    show colData2 (⟨133, by decide⟩ : Fin 148)
        ((colE2 ⟨101, by decide⟩ 20 hp : ↥(Q2.reps ⟨101, by decide⟩)) : Coordinate 2)
        Q2.T133_101_2 = colFn colCertDiv_133_101_20.D2 (m := 5) from colCertDiv_133_101_20.bind2]
  rw [alnId_133 j hj]
  exact fastcode_of_div ⟨133, by decide⟩ _ _ _
    ((alnId_133 j hj) ▸ Q2.listedAt (⟨133, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨133, by decide⟩ : Fin 148) hj hq).1) colCertDiv_133_101_20_match


theorem leaf_133_105_0 (hp : 0 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 0 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 0 (transLenTr ⟨105, by decide⟩ 0 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 0 (transLenTr ⟨105, by decide⟩ 0 hp)) T133_105
      hfix133_105 hinj133_105 hcardT133_105
      (fun i => conj_mem_of_fixedPoints _ _ (T133_105 i) (hfix133_105 i) _)
      ⟨133, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 0 hp) Q2.T133_105_2 Q2.hfix133_105_2 Q2.hinj133_105_2
      Q2.hcardT133_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_105_2 i) (Q2.hfix133_105_2 i) _)
      colCert_133_105_0.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_105_1 (hp : 1 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 1 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 1 (transLenTr ⟨105, by decide⟩ 1 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 1 (transLenTr ⟨105, by decide⟩ 1 hp)) T133_105
      hfix133_105 hinj133_105 hcardT133_105
      (fun i => conj_mem_of_fixedPoints _ _ (T133_105 i) (hfix133_105 i) _)
      ⟨133, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 1 hp) Q2.T133_105_2 Q2.hfix133_105_2 Q2.hinj133_105_2
      Q2.hcardT133_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_105_2 i) (Q2.hfix133_105_2 i) _)
      colCert_133_105_1.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_105_2 (hp : 2 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 2 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 2 (transLenTr ⟨105, by decide⟩ 2 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 2 (transLenTr ⟨105, by decide⟩ 2 hp)) T133_105
      hfix133_105 hinj133_105 hcardT133_105
      (fun i => conj_mem_of_fixedPoints _ _ (T133_105 i) (hfix133_105 i) _)
      ⟨133, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 2 hp) Q2.T133_105_2 Q2.hfix133_105_2 Q2.hinj133_105_2
      Q2.hcardT133_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_105_2 i) (Q2.hfix133_105_2 i) _)
      colCert_133_105_2.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_105_3 (hp : 3 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 3 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 3 (transLenTr ⟨105, by decide⟩ 3 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 3 (transLenTr ⟨105, by decide⟩ 3 hp)) T133_105
      hfix133_105 hinj133_105 hcardT133_105
      (fun i => conj_mem_of_fixedPoints _ _ (T133_105 i) (hfix133_105 i) _)
      ⟨133, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 3 hp) Q2.T133_105_2 Q2.hfix133_105_2 Q2.hinj133_105_2
      Q2.hcardT133_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_105_2 i) (Q2.hfix133_105_2 i) _)
      colCert_133_105_3.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_105_4 (hp : 4 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 4 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 4 (transLenTr ⟨105, by decide⟩ 4 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 4 (transLenTr ⟨105, by decide⟩ 4 hp)) T133_105
      hfix133_105 hinj133_105 hcardT133_105
      (fun i => conj_mem_of_fixedPoints _ _ (T133_105 i) (hfix133_105 i) _)
      ⟨133, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 4 hp) Q2.T133_105_2 Q2.hfix133_105_2 Q2.hinj133_105_2
      Q2.hcardT133_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_105_2 i) (Q2.hfix133_105_2 i) _)
      colCert_133_105_4.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_105_5 (hp : 5 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 5 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 5 (transLenTr ⟨105, by decide⟩ 5 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 5 (transLenTr ⟨105, by decide⟩ 5 hp)) T133_105
      hfix133_105 hinj133_105 hcardT133_105
      (fun i => conj_mem_of_fixedPoints _ _ (T133_105 i) (hfix133_105 i) _)
      ⟨133, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 5 hp) Q2.T133_105_2 Q2.hfix133_105_2 Q2.hinj133_105_2
      Q2.hcardT133_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_105_2 i) (Q2.hfix133_105_2 i) _)
      colCert_133_105_5.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_105_10 (hp : 10 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 10 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 10 (transLenTr ⟨105, by decide⟩ 10 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 10 (transLenTr ⟨105, by decide⟩ 10 hp)) T133_105
      hfix133_105 hinj133_105 hcardT133_105
      (fun i => conj_mem_of_fixedPoints _ _ (T133_105 i) (hfix133_105 i) _)
      ⟨133, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 10 hp) Q2.T133_105_2 Q2.hfix133_105_2 Q2.hinj133_105_2
      Q2.hcardT133_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_105_2 i) (Q2.hfix133_105_2 i) _)
      colCert_133_105_10.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_105_15 (hp : 15 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 15 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 15 (transLenTr ⟨105, by decide⟩ 15 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 15 (transLenTr ⟨105, by decide⟩ 15 hp)) T133_105
      hfix133_105 hinj133_105 hcardT133_105
      (fun i => conj_mem_of_fixedPoints _ _ (T133_105 i) (hfix133_105 i) _)
      ⟨133, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 15 hp) Q2.T133_105_2 Q2.hfix133_105_2 Q2.hinj133_105_2
      Q2.hcardT133_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_105_2 i) (Q2.hfix133_105_2 i) _)
      colCert_133_105_15.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_105_20 (hp : 20 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 20 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 20 (transLenTr ⟨105, by decide⟩ 20 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 20 (transLenTr ⟨105, by decide⟩ 20 hp)) T133_105
      hfix133_105 hinj133_105 hcardT133_105
      (fun i => conj_mem_of_fixedPoints _ _ (T133_105 i) (hfix133_105 i) _)
      ⟨133, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 20 hp) Q2.T133_105_2 Q2.hfix133_105_2 Q2.hinj133_105_2
      Q2.hcardT133_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_105_2 i) (Q2.hfix133_105_2 i) _)
      colCert_133_105_20.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_105_25 (hp : 25 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 25 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 25 (transLenTr ⟨105, by decide⟩ 25 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 25 (transLenTr ⟨105, by decide⟩ 25 hp)) T133_105
      hfix133_105 hinj133_105 hcardT133_105
      (fun i => conj_mem_of_fixedPoints _ _ (T133_105 i) (hfix133_105 i) _)
      ⟨133, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 25 hp) Q2.T133_105_2 Q2.hfix133_105_2 Q2.hinj133_105_2
      Q2.hcardT133_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_105_2 i) (Q2.hfix133_105_2 i) _)
      colCert_133_105_25.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_105_50 (hp : 50 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 50 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 50 (transLenTr ⟨105, by decide⟩ 50 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 50 (transLenTr ⟨105, by decide⟩ 50 hp)) T133_105
      hfix133_105 hinj133_105 hcardT133_105
      (fun i => conj_mem_of_fixedPoints _ _ (T133_105 i) (hfix133_105 i) _)
      ⟨133, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 50 hp) Q2.T133_105_2 Q2.hfix133_105_2 Q2.hinj133_105_2
      Q2.hcardT133_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_105_2 i) (Q2.hfix133_105_2 i) _)
      colCert_133_105_50.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_105_75 (hp : 75 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 75 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 75 (transLenTr ⟨105, by decide⟩ 75 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 75 (transLenTr ⟨105, by decide⟩ 75 hp)) T133_105
      hfix133_105 hinj133_105 hcardT133_105
      (fun i => conj_mem_of_fixedPoints _ _ (T133_105 i) (hfix133_105 i) _)
      ⟨133, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 75 hp) Q2.T133_105_2 Q2.hfix133_105_2 Q2.hinj133_105_2
      Q2.hcardT133_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_105_2 i) (Q2.hfix133_105_2 i) _)
      colCert_133_105_75.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_105_100 (hp : 100 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 100 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 100 (transLenTr ⟨105, by decide⟩ 100 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 100 (transLenTr ⟨105, by decide⟩ 100 hp)) T133_105
      hfix133_105 hinj133_105 hcardT133_105
      (fun i => conj_mem_of_fixedPoints _ _ (T133_105 i) (hfix133_105 i) _)
      ⟨133, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 100 hp) Q2.T133_105_2 Q2.hfix133_105_2 Q2.hinj133_105_2
      Q2.hcardT133_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_105_2 i) (Q2.hfix133_105_2 i) _)
      colCert_133_105_100.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_112_0 (hp : 0 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 0 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 0 (transLenTr ⟨112, by decide⟩ 0 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 0 (transLenTr ⟨112, by decide⟩ 0 hp)) T133_112
      hfix133_112 hinj133_112 hcardT133_112
      (fun i => conj_mem_of_fixedPoints _ _ (T133_112 i) (hfix133_112 i) _)
      ⟨133, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 0 hp) Q2.T133_112_2 Q2.hfix133_112_2 Q2.hinj133_112_2
      Q2.hcardT133_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_112_2 i) (Q2.hfix133_112_2 i) _)
      colCert_133_112_0.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_112_1 (hp : 1 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 1 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 1 (transLenTr ⟨112, by decide⟩ 1 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 1 (transLenTr ⟨112, by decide⟩ 1 hp)) T133_112
      hfix133_112 hinj133_112 hcardT133_112
      (fun i => conj_mem_of_fixedPoints _ _ (T133_112 i) (hfix133_112 i) _)
      ⟨133, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 1 hp) Q2.T133_112_2 Q2.hfix133_112_2 Q2.hinj133_112_2
      Q2.hcardT133_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_112_2 i) (Q2.hfix133_112_2 i) _)
      colCert_133_112_1.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_112_2 (hp : 2 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 2 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 2 (transLenTr ⟨112, by decide⟩ 2 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 2 (transLenTr ⟨112, by decide⟩ 2 hp)) T133_112
      hfix133_112 hinj133_112 hcardT133_112
      (fun i => conj_mem_of_fixedPoints _ _ (T133_112 i) (hfix133_112 i) _)
      ⟨133, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 2 hp) Q2.T133_112_2 Q2.hfix133_112_2 Q2.hinj133_112_2
      Q2.hcardT133_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_112_2 i) (Q2.hfix133_112_2 i) _)
      colCert_133_112_2.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_112_3 (hp : 3 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 3 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 3 (transLenTr ⟨112, by decide⟩ 3 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 3 (transLenTr ⟨112, by decide⟩ 3 hp)) T133_112
      hfix133_112 hinj133_112 hcardT133_112
      (fun i => conj_mem_of_fixedPoints _ _ (T133_112 i) (hfix133_112 i) _)
      ⟨133, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 3 hp) Q2.T133_112_2 Q2.hfix133_112_2 Q2.hinj133_112_2
      Q2.hcardT133_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_112_2 i) (Q2.hfix133_112_2 i) _)
      colCert_133_112_3.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_112_4 (hp : 4 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 4 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 4 (transLenTr ⟨112, by decide⟩ 4 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 4 (transLenTr ⟨112, by decide⟩ 4 hp)) T133_112
      hfix133_112 hinj133_112 hcardT133_112
      (fun i => conj_mem_of_fixedPoints _ _ (T133_112 i) (hfix133_112 i) _)
      ⟨133, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 4 hp) Q2.T133_112_2 Q2.hfix133_112_2 Q2.hinj133_112_2
      Q2.hcardT133_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_112_2 i) (Q2.hfix133_112_2 i) _)
      colCert_133_112_4.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_112_5 (hp : 5 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 5 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 5 (transLenTr ⟨112, by decide⟩ 5 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 5 (transLenTr ⟨112, by decide⟩ 5 hp)) T133_112
      hfix133_112 hinj133_112 hcardT133_112
      (fun i => conj_mem_of_fixedPoints _ _ (T133_112 i) (hfix133_112 i) _)
      ⟨133, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 5 hp) Q2.T133_112_2 Q2.hfix133_112_2 Q2.hinj133_112_2
      Q2.hcardT133_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_112_2 i) (Q2.hfix133_112_2 i) _)
      colCert_133_112_5.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_112_10 (hp : 10 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 10 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 10 (transLenTr ⟨112, by decide⟩ 10 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 10 (transLenTr ⟨112, by decide⟩ 10 hp)) T133_112
      hfix133_112 hinj133_112 hcardT133_112
      (fun i => conj_mem_of_fixedPoints _ _ (T133_112 i) (hfix133_112 i) _)
      ⟨133, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 10 hp) Q2.T133_112_2 Q2.hfix133_112_2 Q2.hinj133_112_2
      Q2.hcardT133_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_112_2 i) (Q2.hfix133_112_2 i) _)
      colCert_133_112_10.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_112_15 (hp : 15 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 15 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 15 (transLenTr ⟨112, by decide⟩ 15 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨133, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 15 (transLenTr ⟨112, by decide⟩ 15 hp)) T133_112
      hfix133_112 hinj133_112 hcardT133_112
      (fun i => conj_mem_of_fixedPoints _ _ (T133_112 i) (hfix133_112 i) _)
      ⟨133, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 15 hp) Q2.T133_112_2 Q2.hfix133_112_2 Q2.hinj133_112_2
      Q2.hcardT133_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_112_2 i) (Q2.hfix133_112_2 i) _)
      ?_).symm
  rw [show colData1 (⟨133, by decide⟩ : Fin 148)
        ((colE1 ⟨112, by decide⟩ 15 (transLenTr ⟨112, by decide⟩ 15 hp) : ↥(reps ⟨112, by decide⟩)) : Coordinate 1)
        T133_112 = colFn colCertDiv_133_112_15.D1 (m := 5) from colCertDiv_133_112_15.bind1,
    show colData2 (⟨133, by decide⟩ : Fin 148)
        ((colE2 ⟨112, by decide⟩ 15 hp : ↥(Q2.reps ⟨112, by decide⟩)) : Coordinate 2)
        Q2.T133_112_2 = colFn colCertDiv_133_112_15.D2 (m := 5) from colCertDiv_133_112_15.bind2]
  rw [alnId_133 j hj]
  exact fastcode_of_div ⟨133, by decide⟩ _ _ _
    ((alnId_133 j hj) ▸ Q2.listedAt (⟨133, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨133, by decide⟩ : Fin 148) hj hq).1) colCertDiv_133_112_15_match


theorem leaf_133_112_20 (hp : 20 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 20 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 20 (transLenTr ⟨112, by decide⟩ 20 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨133, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 20 (transLenTr ⟨112, by decide⟩ 20 hp)) T133_112
      hfix133_112 hinj133_112 hcardT133_112
      (fun i => conj_mem_of_fixedPoints _ _ (T133_112 i) (hfix133_112 i) _)
      ⟨133, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 20 hp) Q2.T133_112_2 Q2.hfix133_112_2 Q2.hinj133_112_2
      Q2.hcardT133_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_112_2 i) (Q2.hfix133_112_2 i) _)
      ?_).symm
  rw [show colData1 (⟨133, by decide⟩ : Fin 148)
        ((colE1 ⟨112, by decide⟩ 20 (transLenTr ⟨112, by decide⟩ 20 hp) : ↥(reps ⟨112, by decide⟩)) : Coordinate 1)
        T133_112 = colFn colCertDiv_133_112_20.D1 (m := 5) from colCertDiv_133_112_20.bind1,
    show colData2 (⟨133, by decide⟩ : Fin 148)
        ((colE2 ⟨112, by decide⟩ 20 hp : ↥(Q2.reps ⟨112, by decide⟩)) : Coordinate 2)
        Q2.T133_112_2 = colFn colCertDiv_133_112_20.D2 (m := 5) from colCertDiv_133_112_20.bind2]
  rw [alnId_133 j hj]
  exact fastcode_of_div ⟨133, by decide⟩ _ _ _
    ((alnId_133 j hj) ▸ Q2.listedAt (⟨133, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨133, by decide⟩ : Fin 148) hj hq).1) colCertDiv_133_112_20_match


theorem leaf_133_133_0 (hp : 0 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 0 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 0 (transLenTr ⟨133, by decide⟩ 0 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 0 (transLenTr ⟨133, by decide⟩ 0 hp)) T133_133
      hfix133_133 hinj133_133 hcardT133_133
      (fun i => conj_mem_of_fixedPoints _ _ (T133_133 i) (hfix133_133 i) _)
      ⟨133, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 0 hp) Q2.T133_133_2 Q2.hfix133_133_2 Q2.hinj133_133_2
      Q2.hcardT133_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_133_2 i) (Q2.hfix133_133_2 i) _)
      colCert_133_133_0.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_133_1 (hp : 1 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 1 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 1 (transLenTr ⟨133, by decide⟩ 1 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 1 (transLenTr ⟨133, by decide⟩ 1 hp)) T133_133
      hfix133_133 hinj133_133 hcardT133_133
      (fun i => conj_mem_of_fixedPoints _ _ (T133_133 i) (hfix133_133 i) _)
      ⟨133, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 1 hp) Q2.T133_133_2 Q2.hfix133_133_2 Q2.hinj133_133_2
      Q2.hcardT133_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_133_2 i) (Q2.hfix133_133_2 i) _)
      colCert_133_133_1.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_133_2 (hp : 2 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 2 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 2 (transLenTr ⟨133, by decide⟩ 2 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 2 (transLenTr ⟨133, by decide⟩ 2 hp)) T133_133
      hfix133_133 hinj133_133 hcardT133_133
      (fun i => conj_mem_of_fixedPoints _ _ (T133_133 i) (hfix133_133 i) _)
      ⟨133, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 2 hp) Q2.T133_133_2 Q2.hfix133_133_2 Q2.hinj133_133_2
      Q2.hcardT133_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_133_2 i) (Q2.hfix133_133_2 i) _)
      colCert_133_133_2.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_133_3 (hp : 3 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 3 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 3 (transLenTr ⟨133, by decide⟩ 3 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 3 (transLenTr ⟨133, by decide⟩ 3 hp)) T133_133
      hfix133_133 hinj133_133 hcardT133_133
      (fun i => conj_mem_of_fixedPoints _ _ (T133_133 i) (hfix133_133 i) _)
      ⟨133, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 3 hp) Q2.T133_133_2 Q2.hfix133_133_2 Q2.hinj133_133_2
      Q2.hcardT133_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_133_2 i) (Q2.hfix133_133_2 i) _)
      colCert_133_133_3.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_133_4 (hp : 4 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 4 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 4 (transLenTr ⟨133, by decide⟩ 4 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 4 (transLenTr ⟨133, by decide⟩ 4 hp)) T133_133
      hfix133_133 hinj133_133 hcardT133_133
      (fun i => conj_mem_of_fixedPoints _ _ (T133_133 i) (hfix133_133 i) _)
      ⟨133, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 4 hp) Q2.T133_133_2 Q2.hfix133_133_2 Q2.hinj133_133_2
      Q2.hcardT133_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_133_2 i) (Q2.hfix133_133_2 i) _)
      colCert_133_133_4.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_133_5 (hp : 5 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 5 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 5 (transLenTr ⟨133, by decide⟩ 5 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 5 (transLenTr ⟨133, by decide⟩ 5 hp)) T133_133
      hfix133_133 hinj133_133 hcardT133_133
      (fun i => conj_mem_of_fixedPoints _ _ (T133_133 i) (hfix133_133 i) _)
      ⟨133, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 5 hp) Q2.T133_133_2 Q2.hfix133_133_2 Q2.hinj133_133_2
      Q2.hcardT133_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_133_2 i) (Q2.hfix133_133_2 i) _)
      colCert_133_133_5.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_133_6 (hp : 6 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 6 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 6 (transLenTr ⟨133, by decide⟩ 6 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 6 (transLenTr ⟨133, by decide⟩ 6 hp)) T133_133
      hfix133_133 hinj133_133 hcardT133_133
      (fun i => conj_mem_of_fixedPoints _ _ (T133_133 i) (hfix133_133 i) _)
      ⟨133, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 6 hp) Q2.T133_133_2 Q2.hfix133_133_2 Q2.hinj133_133_2
      Q2.hcardT133_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_133_2 i) (Q2.hfix133_133_2 i) _)
      colCert_133_133_6.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_133_7 (hp : 7 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 7 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 7 (transLenTr ⟨133, by decide⟩ 7 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 7 (transLenTr ⟨133, by decide⟩ 7 hp)) T133_133
      hfix133_133 hinj133_133 hcardT133_133
      (fun i => conj_mem_of_fixedPoints _ _ (T133_133 i) (hfix133_133 i) _)
      ⟨133, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 7 hp) Q2.T133_133_2 Q2.hfix133_133_2 Q2.hinj133_133_2
      Q2.hcardT133_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_133_2 i) (Q2.hfix133_133_2 i) _)
      colCert_133_133_7.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_133_8 (hp : 8 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 8 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 8 (transLenTr ⟨133, by decide⟩ 8 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 8 (transLenTr ⟨133, by decide⟩ 8 hp)) T133_133
      hfix133_133 hinj133_133 hcardT133_133
      (fun i => conj_mem_of_fixedPoints _ _ (T133_133 i) (hfix133_133 i) _)
      ⟨133, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 8 hp) Q2.T133_133_2 Q2.hfix133_133_2 Q2.hinj133_133_2
      Q2.hcardT133_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_133_2 i) (Q2.hfix133_133_2 i) _)
      colCert_133_133_8.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_133_9 (hp : 9 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 9 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 9 (transLenTr ⟨133, by decide⟩ 9 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 9 (transLenTr ⟨133, by decide⟩ 9 hp)) T133_133
      hfix133_133 hinj133_133 hcardT133_133
      (fun i => conj_mem_of_fixedPoints _ _ (T133_133 i) (hfix133_133 i) _)
      ⟨133, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 9 hp) Q2.T133_133_2 Q2.hfix133_133_2 Q2.hinj133_133_2
      Q2.hcardT133_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_133_2 i) (Q2.hfix133_133_2 i) _)
      colCert_133_133_9.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_133_10 (hp : 10 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 10 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 10 (transLenTr ⟨133, by decide⟩ 10 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 10 (transLenTr ⟨133, by decide⟩ 10 hp)) T133_133
      hfix133_133 hinj133_133 hcardT133_133
      (fun i => conj_mem_of_fixedPoints _ _ (T133_133 i) (hfix133_133 i) _)
      ⟨133, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 10 hp) Q2.T133_133_2 Q2.hfix133_133_2 Q2.hinj133_133_2
      Q2.hcardT133_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_133_2 i) (Q2.hfix133_133_2 i) _)
      colCert_133_133_10.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_133_11 (hp : 11 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 11 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 11 (transLenTr ⟨133, by decide⟩ 11 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 11 (transLenTr ⟨133, by decide⟩ 11 hp)) T133_133
      hfix133_133 hinj133_133 hcardT133_133
      (fun i => conj_mem_of_fixedPoints _ _ (T133_133 i) (hfix133_133 i) _)
      ⟨133, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 11 hp) Q2.T133_133_2 Q2.hfix133_133_2 Q2.hinj133_133_2
      Q2.hcardT133_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_133_2 i) (Q2.hfix133_133_2 i) _)
      colCert_133_133_11.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_133_12 (hp : 12 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 12 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 12 (transLenTr ⟨133, by decide⟩ 12 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 12 (transLenTr ⟨133, by decide⟩ 12 hp)) T133_133
      hfix133_133 hinj133_133 hcardT133_133
      (fun i => conj_mem_of_fixedPoints _ _ (T133_133 i) (hfix133_133 i) _)
      ⟨133, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 12 hp) Q2.T133_133_2 Q2.hfix133_133_2 Q2.hinj133_133_2
      Q2.hcardT133_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_133_2 i) (Q2.hfix133_133_2 i) _)
      colCert_133_133_12.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_133_13 (hp : 13 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 13 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 13 (transLenTr ⟨133, by decide⟩ 13 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 13 (transLenTr ⟨133, by decide⟩ 13 hp)) T133_133
      hfix133_133 hinj133_133 hcardT133_133
      (fun i => conj_mem_of_fixedPoints _ _ (T133_133 i) (hfix133_133 i) _)
      ⟨133, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 13 hp) Q2.T133_133_2 Q2.hfix133_133_2 Q2.hinj133_133_2
      Q2.hcardT133_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_133_2 i) (Q2.hfix133_133_2 i) _)
      colCert_133_133_13.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_133_14 (hp : 14 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 14 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 14 (transLenTr ⟨133, by decide⟩ 14 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 14 (transLenTr ⟨133, by decide⟩ 14 hp)) T133_133
      hfix133_133 hinj133_133 hcardT133_133
      (fun i => conj_mem_of_fixedPoints _ _ (T133_133 i) (hfix133_133 i) _)
      ⟨133, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 14 hp) Q2.T133_133_2 Q2.hfix133_133_2 Q2.hinj133_133_2
      Q2.hcardT133_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_133_2 i) (Q2.hfix133_133_2 i) _)
      colCert_133_133_14.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_133_15 (hp : 15 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 15 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 15 (transLenTr ⟨133, by decide⟩ 15 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 15 (transLenTr ⟨133, by decide⟩ 15 hp)) T133_133
      hfix133_133 hinj133_133 hcardT133_133
      (fun i => conj_mem_of_fixedPoints _ _ (T133_133 i) (hfix133_133 i) _)
      ⟨133, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 15 hp) Q2.T133_133_2 Q2.hfix133_133_2 Q2.hinj133_133_2
      Q2.hcardT133_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_133_2 i) (Q2.hfix133_133_2 i) _)
      colCert_133_133_15.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_133_16 (hp : 16 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 16 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 16 (transLenTr ⟨133, by decide⟩ 16 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 16 (transLenTr ⟨133, by decide⟩ 16 hp)) T133_133
      hfix133_133 hinj133_133 hcardT133_133
      (fun i => conj_mem_of_fixedPoints _ _ (T133_133 i) (hfix133_133 i) _)
      ⟨133, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 16 hp) Q2.T133_133_2 Q2.hfix133_133_2 Q2.hinj133_133_2
      Q2.hcardT133_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_133_2 i) (Q2.hfix133_133_2 i) _)
      colCert_133_133_16.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_133_17 (hp : 17 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 17 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 17 (transLenTr ⟨133, by decide⟩ 17 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 17 (transLenTr ⟨133, by decide⟩ 17 hp)) T133_133
      hfix133_133 hinj133_133 hcardT133_133
      (fun i => conj_mem_of_fixedPoints _ _ (T133_133 i) (hfix133_133 i) _)
      ⟨133, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 17 hp) Q2.T133_133_2 Q2.hfix133_133_2 Q2.hinj133_133_2
      Q2.hcardT133_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_133_2 i) (Q2.hfix133_133_2 i) _)
      colCert_133_133_17.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_133_18 (hp : 18 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 18 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 18 (transLenTr ⟨133, by decide⟩ 18 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 18 (transLenTr ⟨133, by decide⟩ 18 hp)) T133_133
      hfix133_133 hinj133_133 hcardT133_133
      (fun i => conj_mem_of_fixedPoints _ _ (T133_133 i) (hfix133_133 i) _)
      ⟨133, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 18 hp) Q2.T133_133_2 Q2.hfix133_133_2 Q2.hinj133_133_2
      Q2.hcardT133_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_133_2 i) (Q2.hfix133_133_2 i) _)
      colCert_133_133_18.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_133_19 (hp : 19 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 19 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 19 (transLenTr ⟨133, by decide⟩ 19 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 19 (transLenTr ⟨133, by decide⟩ 19 hp)) T133_133
      hfix133_133 hinj133_133 hcardT133_133
      (fun i => conj_mem_of_fixedPoints _ _ (T133_133 i) (hfix133_133 i) _)
      ⟨133, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 19 hp) Q2.T133_133_2 Q2.hfix133_133_2 Q2.hinj133_133_2
      Q2.hcardT133_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_133_2 i) (Q2.hfix133_133_2 i) _)
      colCert_133_133_19.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_133_20 (hp : 20 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 20 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 20 (transLenTr ⟨133, by decide⟩ 20 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 20 (transLenTr ⟨133, by decide⟩ 20 hp)) T133_133
      hfix133_133 hinj133_133 hcardT133_133
      (fun i => conj_mem_of_fixedPoints _ _ (T133_133 i) (hfix133_133 i) _)
      ⟨133, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 20 hp) Q2.T133_133_2 Q2.hfix133_133_2 Q2.hinj133_133_2
      Q2.hcardT133_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_133_2 i) (Q2.hfix133_133_2 i) _)
      colCert_133_133_20.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_133_21 (hp : 21 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 21 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 21 (transLenTr ⟨133, by decide⟩ 21 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 21 (transLenTr ⟨133, by decide⟩ 21 hp)) T133_133
      hfix133_133 hinj133_133 hcardT133_133
      (fun i => conj_mem_of_fixedPoints _ _ (T133_133 i) (hfix133_133 i) _)
      ⟨133, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 21 hp) Q2.T133_133_2 Q2.hfix133_133_2 Q2.hinj133_133_2
      Q2.hcardT133_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_133_2 i) (Q2.hfix133_133_2 i) _)
      colCert_133_133_21.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_133_22 (hp : 22 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 22 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 22 (transLenTr ⟨133, by decide⟩ 22 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 22 (transLenTr ⟨133, by decide⟩ 22 hp)) T133_133
      hfix133_133 hinj133_133 hcardT133_133
      (fun i => conj_mem_of_fixedPoints _ _ (T133_133 i) (hfix133_133 i) _)
      ⟨133, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 22 hp) Q2.T133_133_2 Q2.hfix133_133_2 Q2.hinj133_133_2
      Q2.hcardT133_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_133_2 i) (Q2.hfix133_133_2 i) _)
      colCert_133_133_22.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_133_23 (hp : 23 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 23 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 23 (transLenTr ⟨133, by decide⟩ 23 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 23 (transLenTr ⟨133, by decide⟩ 23 hp)) T133_133
      hfix133_133 hinj133_133 hcardT133_133
      (fun i => conj_mem_of_fixedPoints _ _ (T133_133 i) (hfix133_133 i) _)
      ⟨133, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 23 hp) Q2.T133_133_2 Q2.hfix133_133_2 Q2.hinj133_133_2
      Q2.hcardT133_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_133_2 i) (Q2.hfix133_133_2 i) _)
      colCert_133_133_23.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_133_133_24 (hp : 24 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 133 []).length)
    (hq : (normIsRep.getD 133 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 24 hp)
        (rowE2 (⟨133, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 24 (transLenTr ⟨133, by decide⟩ 24 hp))
        (rowE1 (⟨133, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨133, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨133, by decide⟩ (listedAt ⟨133, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 24 (transLenTr ⟨133, by decide⟩ 24 hp)) T133_133
      hfix133_133 hinj133_133 hcardT133_133
      (fun i => conj_mem_of_fixedPoints _ _ (T133_133 i) (hfix133_133 i) _)
      ⟨133, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨133, by decide⟩ (Q2.listedAt ⟨133, by decide⟩
        (alnCheck_rep ⟨133, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 24 hp) Q2.T133_133_2 Q2.hfix133_133_2 Q2.hinj133_133_2
      Q2.hcardT133_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T133_133_2 i) (Q2.hfix133_133_2 i) _)
      colCert_133_133_24.hD ?_).symm
  rw [alnId_133 j hj]


theorem leaf_134_4_0 (hp : 0 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 0 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp)) T134_4
      hfix134_4 hinj134_4 hcardT134_4
      (fun i => conj_mem_of_fixedPoints _ _ (T134_4 i) (hfix134_4 i) _)
      ⟨134, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 0 hp) Q2.T134_4_2 Q2.hfix134_4_2 Q2.hinj134_4_2
      Q2.hcardT134_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_4_2 i) (Q2.hfix134_4_2 i) _)
      colCert_134_4_0.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_4_1 (hp : 1 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 1 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp)) T134_4
      hfix134_4 hinj134_4 hcardT134_4
      (fun i => conj_mem_of_fixedPoints _ _ (T134_4 i) (hfix134_4 i) _)
      ⟨134, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 1 hp) Q2.T134_4_2 Q2.hfix134_4_2 Q2.hinj134_4_2
      Q2.hcardT134_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_4_2 i) (Q2.hfix134_4_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp) : ↥(reps ⟨4, by decide⟩)) : Coordinate 1)
        T134_4 = colFn colCertDiv_134_4_1.D1 (m := 5) from colCertDiv_134_4_1.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨4, by decide⟩ 1 hp : ↥(Q2.reps ⟨4, by decide⟩)) : Coordinate 2)
        Q2.T134_4_2 = colFn colCertDiv_134_4_1.D2 (m := 5) from colCertDiv_134_4_1.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_4_1_match


theorem leaf_134_4_2 (hp : 2 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 2 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp)) T134_4
      hfix134_4 hinj134_4 hcardT134_4
      (fun i => conj_mem_of_fixedPoints _ _ (T134_4 i) (hfix134_4 i) _)
      ⟨134, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 2 hp) Q2.T134_4_2 Q2.hfix134_4_2 Q2.hinj134_4_2
      Q2.hcardT134_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_4_2 i) (Q2.hfix134_4_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp) : ↥(reps ⟨4, by decide⟩)) : Coordinate 1)
        T134_4 = colFn colCertDiv_134_4_2.D1 (m := 5) from colCertDiv_134_4_2.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨4, by decide⟩ 2 hp : ↥(Q2.reps ⟨4, by decide⟩)) : Coordinate 2)
        Q2.T134_4_2 = colFn colCertDiv_134_4_2.D2 (m := 5) from colCertDiv_134_4_2.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_4_2_match


theorem leaf_134_4_3 (hp : 3 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 3 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp)) T134_4
      hfix134_4 hinj134_4 hcardT134_4
      (fun i => conj_mem_of_fixedPoints _ _ (T134_4 i) (hfix134_4 i) _)
      ⟨134, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 3 hp) Q2.T134_4_2 Q2.hfix134_4_2 Q2.hinj134_4_2
      Q2.hcardT134_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_4_2 i) (Q2.hfix134_4_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp) : ↥(reps ⟨4, by decide⟩)) : Coordinate 1)
        T134_4 = colFn colCertDiv_134_4_3.D1 (m := 5) from colCertDiv_134_4_3.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨4, by decide⟩ 3 hp : ↥(Q2.reps ⟨4, by decide⟩)) : Coordinate 2)
        Q2.T134_4_2 = colFn colCertDiv_134_4_3.D2 (m := 5) from colCertDiv_134_4_3.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_4_3_match


theorem leaf_134_4_4 (hp : 4 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 4 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp)) T134_4
      hfix134_4 hinj134_4 hcardT134_4
      (fun i => conj_mem_of_fixedPoints _ _ (T134_4 i) (hfix134_4 i) _)
      ⟨134, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 4 hp) Q2.T134_4_2 Q2.hfix134_4_2 Q2.hinj134_4_2
      Q2.hcardT134_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_4_2 i) (Q2.hfix134_4_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp) : ↥(reps ⟨4, by decide⟩)) : Coordinate 1)
        T134_4 = colFn colCertDiv_134_4_4.D1 (m := 5) from colCertDiv_134_4_4.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨4, by decide⟩ 4 hp : ↥(Q2.reps ⟨4, by decide⟩)) : Coordinate 2)
        Q2.T134_4_2 = colFn colCertDiv_134_4_4.D2 (m := 5) from colCertDiv_134_4_4.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_4_4_match


theorem leaf_134_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T134_10
      hfix134_10 hinj134_10 hcardT134_10
      (fun i => conj_mem_of_fixedPoints _ _ (T134_10 i) (hfix134_10 i) _)
      ⟨134, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T134_10_2 Q2.hfix134_10_2 Q2.hinj134_10_2
      Q2.hcardT134_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_10_2 i) (Q2.hfix134_10_2 i) _)
      colCert_134_10_0.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T134_10
      hfix134_10 hinj134_10 hcardT134_10
      (fun i => conj_mem_of_fixedPoints _ _ (T134_10 i) (hfix134_10 i) _)
      ⟨134, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T134_10_2 Q2.hfix134_10_2 Q2.hinj134_10_2
      Q2.hcardT134_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_10_2 i) (Q2.hfix134_10_2 i) _)
      colCert_134_10_1.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T134_10
      hfix134_10 hinj134_10 hcardT134_10
      (fun i => conj_mem_of_fixedPoints _ _ (T134_10 i) (hfix134_10 i) _)
      ⟨134, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T134_10_2 Q2.hfix134_10_2 Q2.hinj134_10_2
      Q2.hcardT134_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_10_2 i) (Q2.hfix134_10_2 i) _)
      colCert_134_10_2.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T134_10
      hfix134_10 hinj134_10 hcardT134_10
      (fun i => conj_mem_of_fixedPoints _ _ (T134_10 i) (hfix134_10 i) _)
      ⟨134, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T134_10_2 Q2.hfix134_10_2 Q2.hinj134_10_2
      Q2.hcardT134_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_10_2 i) (Q2.hfix134_10_2 i) _)
      colCert_134_10_3.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T134_10
      hfix134_10 hinj134_10 hcardT134_10
      (fun i => conj_mem_of_fixedPoints _ _ (T134_10 i) (hfix134_10 i) _)
      ⟨134, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T134_10_2 Q2.hfix134_10_2 Q2.hinj134_10_2
      Q2.hcardT134_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_10_2 i) (Q2.hfix134_10_2 i) _)
      colCert_134_10_4.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T134_12
      hfix134_12 hinj134_12 hcardT134_12
      (fun i => conj_mem_of_fixedPoints _ _ (T134_12 i) (hfix134_12 i) _)
      ⟨134, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T134_12_2 Q2.hfix134_12_2 Q2.hinj134_12_2
      Q2.hcardT134_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_12_2 i) (Q2.hfix134_12_2 i) _)
      colCert_134_12_0.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T134_12
      hfix134_12 hinj134_12 hcardT134_12
      (fun i => conj_mem_of_fixedPoints _ _ (T134_12 i) (hfix134_12 i) _)
      ⟨134, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T134_12_2 Q2.hfix134_12_2 Q2.hinj134_12_2
      Q2.hcardT134_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_12_2 i) (Q2.hfix134_12_2 i) _)
      colCert_134_12_1.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T134_12
      hfix134_12 hinj134_12 hcardT134_12
      (fun i => conj_mem_of_fixedPoints _ _ (T134_12 i) (hfix134_12 i) _)
      ⟨134, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T134_12_2 Q2.hfix134_12_2 Q2.hinj134_12_2
      Q2.hcardT134_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_12_2 i) (Q2.hfix134_12_2 i) _)
      colCert_134_12_2.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T134_12
      hfix134_12 hinj134_12 hcardT134_12
      (fun i => conj_mem_of_fixedPoints _ _ (T134_12 i) (hfix134_12 i) _)
      ⟨134, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T134_12_2 Q2.hfix134_12_2 Q2.hinj134_12_2
      Q2.hcardT134_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_12_2 i) (Q2.hfix134_12_2 i) _)
      colCert_134_12_3.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T134_12
      hfix134_12 hinj134_12 hcardT134_12
      (fun i => conj_mem_of_fixedPoints _ _ (T134_12 i) (hfix134_12 i) _)
      ⟨134, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T134_12_2 Q2.hfix134_12_2 Q2.hinj134_12_2
      Q2.hcardT134_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_12_2 i) (Q2.hfix134_12_2 i) _)
      colCert_134_12_4.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_22_0 (hp : 0 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 0 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 0 (transLenTr ⟨22, by decide⟩ 0 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 0 (transLenTr ⟨22, by decide⟩ 0 hp)) T134_22
      hfix134_22 hinj134_22 hcardT134_22
      (fun i => conj_mem_of_fixedPoints _ _ (T134_22 i) (hfix134_22 i) _)
      ⟨134, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 0 hp) Q2.T134_22_2 Q2.hfix134_22_2 Q2.hinj134_22_2
      Q2.hcardT134_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_22_2 i) (Q2.hfix134_22_2 i) _)
      colCert_134_22_0.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_22_1 (hp : 1 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 1 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 1 (transLenTr ⟨22, by decide⟩ 1 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 1 (transLenTr ⟨22, by decide⟩ 1 hp)) T134_22
      hfix134_22 hinj134_22 hcardT134_22
      (fun i => conj_mem_of_fixedPoints _ _ (T134_22 i) (hfix134_22 i) _)
      ⟨134, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 1 hp) Q2.T134_22_2 Q2.hfix134_22_2 Q2.hinj134_22_2
      Q2.hcardT134_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_22_2 i) (Q2.hfix134_22_2 i) _)
      colCert_134_22_1.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_22_2 (hp : 2 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 2 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 2 (transLenTr ⟨22, by decide⟩ 2 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 2 (transLenTr ⟨22, by decide⟩ 2 hp)) T134_22
      hfix134_22 hinj134_22 hcardT134_22
      (fun i => conj_mem_of_fixedPoints _ _ (T134_22 i) (hfix134_22 i) _)
      ⟨134, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 2 hp) Q2.T134_22_2 Q2.hfix134_22_2 Q2.hinj134_22_2
      Q2.hcardT134_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_22_2 i) (Q2.hfix134_22_2 i) _)
      colCert_134_22_2.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_22_3 (hp : 3 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 3 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 3 (transLenTr ⟨22, by decide⟩ 3 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 3 (transLenTr ⟨22, by decide⟩ 3 hp)) T134_22
      hfix134_22 hinj134_22 hcardT134_22
      (fun i => conj_mem_of_fixedPoints _ _ (T134_22 i) (hfix134_22 i) _)
      ⟨134, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 3 hp) Q2.T134_22_2 Q2.hfix134_22_2 Q2.hinj134_22_2
      Q2.hcardT134_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_22_2 i) (Q2.hfix134_22_2 i) _)
      colCert_134_22_3.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_22_4 (hp : 4 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 4 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 4 (transLenTr ⟨22, by decide⟩ 4 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 4 (transLenTr ⟨22, by decide⟩ 4 hp)) T134_22
      hfix134_22 hinj134_22 hcardT134_22
      (fun i => conj_mem_of_fixedPoints _ _ (T134_22 i) (hfix134_22 i) _)
      ⟨134, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 4 hp) Q2.T134_22_2 Q2.hfix134_22_2 Q2.hinj134_22_2
      Q2.hcardT134_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_22_2 i) (Q2.hfix134_22_2 i) _)
      colCert_134_22_4.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_22_5 (hp : 5 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 5 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp)) T134_22
      hfix134_22 hinj134_22 hcardT134_22
      (fun i => conj_mem_of_fixedPoints _ _ (T134_22 i) (hfix134_22 i) _)
      ⟨134, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 5 hp) Q2.T134_22_2 Q2.hfix134_22_2 Q2.hinj134_22_2
      Q2.hcardT134_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_22_2 i) (Q2.hfix134_22_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp) : ↥(reps ⟨22, by decide⟩)) : Coordinate 1)
        T134_22 = colFn colCertDiv_134_22_5.D1 (m := 5) from colCertDiv_134_22_5.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨22, by decide⟩ 5 hp : ↥(Q2.reps ⟨22, by decide⟩)) : Coordinate 2)
        Q2.T134_22_2 = colFn colCertDiv_134_22_5.D2 (m := 5) from colCertDiv_134_22_5.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_22_5_match


theorem leaf_134_22_10 (hp : 10 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 10 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp)) T134_22
      hfix134_22 hinj134_22 hcardT134_22
      (fun i => conj_mem_of_fixedPoints _ _ (T134_22 i) (hfix134_22 i) _)
      ⟨134, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 10 hp) Q2.T134_22_2 Q2.hfix134_22_2 Q2.hinj134_22_2
      Q2.hcardT134_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_22_2 i) (Q2.hfix134_22_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp) : ↥(reps ⟨22, by decide⟩)) : Coordinate 1)
        T134_22 = colFn colCertDiv_134_22_10.D1 (m := 5) from colCertDiv_134_22_10.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨22, by decide⟩ 10 hp : ↥(Q2.reps ⟨22, by decide⟩)) : Coordinate 2)
        Q2.T134_22_2 = colFn colCertDiv_134_22_10.D2 (m := 5) from colCertDiv_134_22_10.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_22_10_match


theorem leaf_134_22_15 (hp : 15 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 15 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp)) T134_22
      hfix134_22 hinj134_22 hcardT134_22
      (fun i => conj_mem_of_fixedPoints _ _ (T134_22 i) (hfix134_22 i) _)
      ⟨134, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 15 hp) Q2.T134_22_2 Q2.hfix134_22_2 Q2.hinj134_22_2
      Q2.hcardT134_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_22_2 i) (Q2.hfix134_22_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp) : ↥(reps ⟨22, by decide⟩)) : Coordinate 1)
        T134_22 = colFn colCertDiv_134_22_15.D1 (m := 5) from colCertDiv_134_22_15.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨22, by decide⟩ 15 hp : ↥(Q2.reps ⟨22, by decide⟩)) : Coordinate 2)
        Q2.T134_22_2 = colFn colCertDiv_134_22_15.D2 (m := 5) from colCertDiv_134_22_15.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_22_15_match


theorem leaf_134_22_20 (hp : 20 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 20 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp)) T134_22
      hfix134_22 hinj134_22 hcardT134_22
      (fun i => conj_mem_of_fixedPoints _ _ (T134_22 i) (hfix134_22 i) _)
      ⟨134, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 20 hp) Q2.T134_22_2 Q2.hfix134_22_2 Q2.hinj134_22_2
      Q2.hcardT134_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_22_2 i) (Q2.hfix134_22_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp) : ↥(reps ⟨22, by decide⟩)) : Coordinate 1)
        T134_22 = colFn colCertDiv_134_22_20.D1 (m := 5) from colCertDiv_134_22_20.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨22, by decide⟩ 20 hp : ↥(Q2.reps ⟨22, by decide⟩)) : Coordinate 2)
        Q2.T134_22_2 = colFn colCertDiv_134_22_20.D2 (m := 5) from colCertDiv_134_22_20.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_22_20_match


theorem leaf_134_28_0 (hp : 0 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 0 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp)) T134_28
      hfix134_28 hinj134_28 hcardT134_28
      (fun i => conj_mem_of_fixedPoints _ _ (T134_28 i) (hfix134_28 i) _)
      ⟨134, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 0 hp) Q2.T134_28_2 Q2.hfix134_28_2 Q2.hinj134_28_2
      Q2.hcardT134_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_28_2 i) (Q2.hfix134_28_2 i) _)
      colCert_134_28_0.hD ?_).symm
  rw [alnId_134 j hj]


end LeanDring.P5Presentation
