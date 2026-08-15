/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C031
import LeanDring.P5.Data.ColRestCheap.C124
import LeanDring.P5.Data.ColRestCheap.C125
import LeanDring.P5.Data.ColRestCheap.C126
import LeanDring.P5.Data.ColRestCheap.C127
import LeanDring.P5.Data.ColRestCheap.C128
import LeanDring.P5.Data.EntryK.C044
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C042

/-! # Stage-5 leaves, chunk 54 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_147_97_0 (hp : 0 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 0 (transLenTr ⟨97, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 0 (transLenTr ⟨97, by decide⟩ 0 hp)) T147_97
      hfix147_97 hinj147_97 hcardT147_97
      (fun i => conj_mem_of_fixedPoints _ _ (T147_97 i) (hfix147_97 i) _)
      ⟨147, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 0 hp) Q2.T147_97_2 Q2.hfix147_97_2 Q2.hinj147_97_2
      Q2.hcardT147_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_97_2 i) (Q2.hfix147_97_2 i) _)
      colCert_147_97_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_97_1 (hp : 1 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 1 (transLenTr ⟨97, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 1 (transLenTr ⟨97, by decide⟩ 1 hp)) T147_97
      hfix147_97 hinj147_97 hcardT147_97
      (fun i => conj_mem_of_fixedPoints _ _ (T147_97 i) (hfix147_97 i) _)
      ⟨147, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 1 hp) Q2.T147_97_2 Q2.hfix147_97_2 Q2.hinj147_97_2
      Q2.hcardT147_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_97_2 i) (Q2.hfix147_97_2 i) _)
      colCert_147_97_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_97_2 (hp : 2 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 2 (transLenTr ⟨97, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 2 (transLenTr ⟨97, by decide⟩ 2 hp)) T147_97
      hfix147_97 hinj147_97 hcardT147_97
      (fun i => conj_mem_of_fixedPoints _ _ (T147_97 i) (hfix147_97 i) _)
      ⟨147, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 2 hp) Q2.T147_97_2 Q2.hfix147_97_2 Q2.hinj147_97_2
      Q2.hcardT147_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_97_2 i) (Q2.hfix147_97_2 i) _)
      colCert_147_97_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_97_3 (hp : 3 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 3 (transLenTr ⟨97, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 3 (transLenTr ⟨97, by decide⟩ 3 hp)) T147_97
      hfix147_97 hinj147_97 hcardT147_97
      (fun i => conj_mem_of_fixedPoints _ _ (T147_97 i) (hfix147_97 i) _)
      ⟨147, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 3 hp) Q2.T147_97_2 Q2.hfix147_97_2 Q2.hinj147_97_2
      Q2.hcardT147_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_97_2 i) (Q2.hfix147_97_2 i) _)
      colCert_147_97_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_97_4 (hp : 4 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 4 (transLenTr ⟨97, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 4 (transLenTr ⟨97, by decide⟩ 4 hp)) T147_97
      hfix147_97 hinj147_97 hcardT147_97
      (fun i => conj_mem_of_fixedPoints _ _ (T147_97 i) (hfix147_97 i) _)
      ⟨147, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 4 hp) Q2.T147_97_2 Q2.hfix147_97_2 Q2.hinj147_97_2
      Q2.hcardT147_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_97_2 i) (Q2.hfix147_97_2 i) _)
      colCert_147_97_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_97_5 (hp : 5 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 5 (transLenTr ⟨97, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 5 (transLenTr ⟨97, by decide⟩ 5 hp)) T147_97
      hfix147_97 hinj147_97 hcardT147_97
      (fun i => conj_mem_of_fixedPoints _ _ (T147_97 i) (hfix147_97 i) _)
      ⟨147, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 5 hp) Q2.T147_97_2 Q2.hfix147_97_2 Q2.hinj147_97_2
      Q2.hcardT147_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_97_2 i) (Q2.hfix147_97_2 i) _)
      colCert_147_97_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_97_10 (hp : 10 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 10 (transLenTr ⟨97, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 10 (transLenTr ⟨97, by decide⟩ 10 hp)) T147_97
      hfix147_97 hinj147_97 hcardT147_97
      (fun i => conj_mem_of_fixedPoints _ _ (T147_97 i) (hfix147_97 i) _)
      ⟨147, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 10 hp) Q2.T147_97_2 Q2.hfix147_97_2 Q2.hinj147_97_2
      Q2.hcardT147_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_97_2 i) (Q2.hfix147_97_2 i) _)
      colCert_147_97_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_97_15 (hp : 15 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 15 (transLenTr ⟨97, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 15 (transLenTr ⟨97, by decide⟩ 15 hp)) T147_97
      hfix147_97 hinj147_97 hcardT147_97
      (fun i => conj_mem_of_fixedPoints _ _ (T147_97 i) (hfix147_97 i) _)
      ⟨147, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 15 hp) Q2.T147_97_2 Q2.hfix147_97_2 Q2.hinj147_97_2
      Q2.hcardT147_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_97_2 i) (Q2.hfix147_97_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨97, by decide⟩ 15 (transLenTr ⟨97, by decide⟩ 15 hp) : ↥(reps ⟨97, by decide⟩)) : Coordinate 1)
        T147_97 = colFn colCertDiv_147_97_15.D1 (m := 1) from colCertDiv_147_97_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨97, by decide⟩ 15 hp : ↥(Q2.reps ⟨97, by decide⟩)) : Coordinate 2)
        Q2.T147_97_2 = colFn colCertDiv_147_97_15.D2 (m := 1) from colCertDiv_147_97_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_97_15_match


theorem leaf_147_97_20 (hp : 20 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 20 (transLenTr ⟨97, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 20 (transLenTr ⟨97, by decide⟩ 20 hp)) T147_97
      hfix147_97 hinj147_97 hcardT147_97
      (fun i => conj_mem_of_fixedPoints _ _ (T147_97 i) (hfix147_97 i) _)
      ⟨147, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 20 hp) Q2.T147_97_2 Q2.hfix147_97_2 Q2.hinj147_97_2
      Q2.hcardT147_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_97_2 i) (Q2.hfix147_97_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨97, by decide⟩ 20 (transLenTr ⟨97, by decide⟩ 20 hp) : ↥(reps ⟨97, by decide⟩)) : Coordinate 1)
        T147_97 = colFn colCertDiv_147_97_20.D1 (m := 1) from colCertDiv_147_97_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨97, by decide⟩ 20 hp : ↥(Q2.reps ⟨97, by decide⟩)) : Coordinate 2)
        Q2.T147_97_2 = colFn colCertDiv_147_97_20.D2 (m := 1) from colCertDiv_147_97_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_97_20_match


theorem leaf_147_98_0 (hp : 0 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 0 (transLenTr ⟨98, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 0 (transLenTr ⟨98, by decide⟩ 0 hp)) T147_98
      hfix147_98 hinj147_98 hcardT147_98
      (fun i => conj_mem_of_fixedPoints _ _ (T147_98 i) (hfix147_98 i) _)
      ⟨147, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 0 hp) Q2.T147_98_2 Q2.hfix147_98_2 Q2.hinj147_98_2
      Q2.hcardT147_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_98_2 i) (Q2.hfix147_98_2 i) _)
      colCert_147_98_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_98_1 (hp : 1 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 1 (transLenTr ⟨98, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 1 (transLenTr ⟨98, by decide⟩ 1 hp)) T147_98
      hfix147_98 hinj147_98 hcardT147_98
      (fun i => conj_mem_of_fixedPoints _ _ (T147_98 i) (hfix147_98 i) _)
      ⟨147, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 1 hp) Q2.T147_98_2 Q2.hfix147_98_2 Q2.hinj147_98_2
      Q2.hcardT147_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_98_2 i) (Q2.hfix147_98_2 i) _)
      colCert_147_98_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_98_2 (hp : 2 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 2 (transLenTr ⟨98, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 2 (transLenTr ⟨98, by decide⟩ 2 hp)) T147_98
      hfix147_98 hinj147_98 hcardT147_98
      (fun i => conj_mem_of_fixedPoints _ _ (T147_98 i) (hfix147_98 i) _)
      ⟨147, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 2 hp) Q2.T147_98_2 Q2.hfix147_98_2 Q2.hinj147_98_2
      Q2.hcardT147_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_98_2 i) (Q2.hfix147_98_2 i) _)
      colCert_147_98_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_98_3 (hp : 3 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 3 (transLenTr ⟨98, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 3 (transLenTr ⟨98, by decide⟩ 3 hp)) T147_98
      hfix147_98 hinj147_98 hcardT147_98
      (fun i => conj_mem_of_fixedPoints _ _ (T147_98 i) (hfix147_98 i) _)
      ⟨147, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 3 hp) Q2.T147_98_2 Q2.hfix147_98_2 Q2.hinj147_98_2
      Q2.hcardT147_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_98_2 i) (Q2.hfix147_98_2 i) _)
      colCert_147_98_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_98_4 (hp : 4 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 4 (transLenTr ⟨98, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 4 (transLenTr ⟨98, by decide⟩ 4 hp)) T147_98
      hfix147_98 hinj147_98 hcardT147_98
      (fun i => conj_mem_of_fixedPoints _ _ (T147_98 i) (hfix147_98 i) _)
      ⟨147, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 4 hp) Q2.T147_98_2 Q2.hfix147_98_2 Q2.hinj147_98_2
      Q2.hcardT147_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_98_2 i) (Q2.hfix147_98_2 i) _)
      colCert_147_98_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_98_5 (hp : 5 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 5 (transLenTr ⟨98, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 5 (transLenTr ⟨98, by decide⟩ 5 hp)) T147_98
      hfix147_98 hinj147_98 hcardT147_98
      (fun i => conj_mem_of_fixedPoints _ _ (T147_98 i) (hfix147_98 i) _)
      ⟨147, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 5 hp) Q2.T147_98_2 Q2.hfix147_98_2 Q2.hinj147_98_2
      Q2.hcardT147_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_98_2 i) (Q2.hfix147_98_2 i) _)
      colCert_147_98_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_98_10 (hp : 10 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 10 (transLenTr ⟨98, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 10 (transLenTr ⟨98, by decide⟩ 10 hp)) T147_98
      hfix147_98 hinj147_98 hcardT147_98
      (fun i => conj_mem_of_fixedPoints _ _ (T147_98 i) (hfix147_98 i) _)
      ⟨147, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 10 hp) Q2.T147_98_2 Q2.hfix147_98_2 Q2.hinj147_98_2
      Q2.hcardT147_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_98_2 i) (Q2.hfix147_98_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨98, by decide⟩ 10 (transLenTr ⟨98, by decide⟩ 10 hp) : ↥(reps ⟨98, by decide⟩)) : Coordinate 1)
        T147_98 = colFn colCertDiv_147_98_10.D1 (m := 1) from colCertDiv_147_98_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨98, by decide⟩ 10 hp : ↥(Q2.reps ⟨98, by decide⟩)) : Coordinate 2)
        Q2.T147_98_2 = colFn colCertDiv_147_98_10.D2 (m := 1) from colCertDiv_147_98_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_98_10_match


theorem leaf_147_98_15 (hp : 15 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 15 (transLenTr ⟨98, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 15 (transLenTr ⟨98, by decide⟩ 15 hp)) T147_98
      hfix147_98 hinj147_98 hcardT147_98
      (fun i => conj_mem_of_fixedPoints _ _ (T147_98 i) (hfix147_98 i) _)
      ⟨147, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 15 hp) Q2.T147_98_2 Q2.hfix147_98_2 Q2.hinj147_98_2
      Q2.hcardT147_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_98_2 i) (Q2.hfix147_98_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨98, by decide⟩ 15 (transLenTr ⟨98, by decide⟩ 15 hp) : ↥(reps ⟨98, by decide⟩)) : Coordinate 1)
        T147_98 = colFn colCertDiv_147_98_15.D1 (m := 1) from colCertDiv_147_98_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨98, by decide⟩ 15 hp : ↥(Q2.reps ⟨98, by decide⟩)) : Coordinate 2)
        Q2.T147_98_2 = colFn colCertDiv_147_98_15.D2 (m := 1) from colCertDiv_147_98_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_98_15_match


theorem leaf_147_98_20 (hp : 20 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 20 (transLenTr ⟨98, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 20 (transLenTr ⟨98, by decide⟩ 20 hp)) T147_98
      hfix147_98 hinj147_98 hcardT147_98
      (fun i => conj_mem_of_fixedPoints _ _ (T147_98 i) (hfix147_98 i) _)
      ⟨147, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 20 hp) Q2.T147_98_2 Q2.hfix147_98_2 Q2.hinj147_98_2
      Q2.hcardT147_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_98_2 i) (Q2.hfix147_98_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨98, by decide⟩ 20 (transLenTr ⟨98, by decide⟩ 20 hp) : ↥(reps ⟨98, by decide⟩)) : Coordinate 1)
        T147_98 = colFn colCertDiv_147_98_20.D1 (m := 1) from colCertDiv_147_98_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨98, by decide⟩ 20 hp : ↥(Q2.reps ⟨98, by decide⟩)) : Coordinate 2)
        Q2.T147_98_2 = colFn colCertDiv_147_98_20.D2 (m := 1) from colCertDiv_147_98_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_98_20_match


theorem leaf_147_99_0 (hp : 0 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 0 (transLenTr ⟨99, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 0 (transLenTr ⟨99, by decide⟩ 0 hp)) T147_99
      hfix147_99 hinj147_99 hcardT147_99
      (fun i => conj_mem_of_fixedPoints _ _ (T147_99 i) (hfix147_99 i) _)
      ⟨147, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 0 hp) Q2.T147_99_2 Q2.hfix147_99_2 Q2.hinj147_99_2
      Q2.hcardT147_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_99_2 i) (Q2.hfix147_99_2 i) _)
      colCert_147_99_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_99_1 (hp : 1 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 1 (transLenTr ⟨99, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 1 (transLenTr ⟨99, by decide⟩ 1 hp)) T147_99
      hfix147_99 hinj147_99 hcardT147_99
      (fun i => conj_mem_of_fixedPoints _ _ (T147_99 i) (hfix147_99 i) _)
      ⟨147, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 1 hp) Q2.T147_99_2 Q2.hfix147_99_2 Q2.hinj147_99_2
      Q2.hcardT147_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_99_2 i) (Q2.hfix147_99_2 i) _)
      colCert_147_99_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_99_2 (hp : 2 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 2 (transLenTr ⟨99, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 2 (transLenTr ⟨99, by decide⟩ 2 hp)) T147_99
      hfix147_99 hinj147_99 hcardT147_99
      (fun i => conj_mem_of_fixedPoints _ _ (T147_99 i) (hfix147_99 i) _)
      ⟨147, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 2 hp) Q2.T147_99_2 Q2.hfix147_99_2 Q2.hinj147_99_2
      Q2.hcardT147_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_99_2 i) (Q2.hfix147_99_2 i) _)
      colCert_147_99_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_99_3 (hp : 3 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 3 (transLenTr ⟨99, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 3 (transLenTr ⟨99, by decide⟩ 3 hp)) T147_99
      hfix147_99 hinj147_99 hcardT147_99
      (fun i => conj_mem_of_fixedPoints _ _ (T147_99 i) (hfix147_99 i) _)
      ⟨147, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 3 hp) Q2.T147_99_2 Q2.hfix147_99_2 Q2.hinj147_99_2
      Q2.hcardT147_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_99_2 i) (Q2.hfix147_99_2 i) _)
      colCert_147_99_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_99_4 (hp : 4 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 4 (transLenTr ⟨99, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 4 (transLenTr ⟨99, by decide⟩ 4 hp)) T147_99
      hfix147_99 hinj147_99 hcardT147_99
      (fun i => conj_mem_of_fixedPoints _ _ (T147_99 i) (hfix147_99 i) _)
      ⟨147, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 4 hp) Q2.T147_99_2 Q2.hfix147_99_2 Q2.hinj147_99_2
      Q2.hcardT147_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_99_2 i) (Q2.hfix147_99_2 i) _)
      colCert_147_99_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_99_5 (hp : 5 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 5 (transLenTr ⟨99, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 5 (transLenTr ⟨99, by decide⟩ 5 hp)) T147_99
      hfix147_99 hinj147_99 hcardT147_99
      (fun i => conj_mem_of_fixedPoints _ _ (T147_99 i) (hfix147_99 i) _)
      ⟨147, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 5 hp) Q2.T147_99_2 Q2.hfix147_99_2 Q2.hinj147_99_2
      Q2.hcardT147_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_99_2 i) (Q2.hfix147_99_2 i) _)
      colCert_147_99_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_99_10 (hp : 10 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 10 (transLenTr ⟨99, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 10 (transLenTr ⟨99, by decide⟩ 10 hp)) T147_99
      hfix147_99 hinj147_99 hcardT147_99
      (fun i => conj_mem_of_fixedPoints _ _ (T147_99 i) (hfix147_99 i) _)
      ⟨147, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 10 hp) Q2.T147_99_2 Q2.hfix147_99_2 Q2.hinj147_99_2
      Q2.hcardT147_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_99_2 i) (Q2.hfix147_99_2 i) _)
      colCert_147_99_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_99_15 (hp : 15 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 15 (transLenTr ⟨99, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 15 (transLenTr ⟨99, by decide⟩ 15 hp)) T147_99
      hfix147_99 hinj147_99 hcardT147_99
      (fun i => conj_mem_of_fixedPoints _ _ (T147_99 i) (hfix147_99 i) _)
      ⟨147, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 15 hp) Q2.T147_99_2 Q2.hfix147_99_2 Q2.hinj147_99_2
      Q2.hcardT147_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_99_2 i) (Q2.hfix147_99_2 i) _)
      colCert_147_99_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_99_20 (hp : 20 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 20 (transLenTr ⟨99, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 20 (transLenTr ⟨99, by decide⟩ 20 hp)) T147_99
      hfix147_99 hinj147_99 hcardT147_99
      (fun i => conj_mem_of_fixedPoints _ _ (T147_99 i) (hfix147_99 i) _)
      ⟨147, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 20 hp) Q2.T147_99_2 Q2.hfix147_99_2 Q2.hinj147_99_2
      Q2.hcardT147_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_99_2 i) (Q2.hfix147_99_2 i) _)
      colCert_147_99_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_100_0 (hp : 0 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 0 (transLenTr ⟨100, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 0 (transLenTr ⟨100, by decide⟩ 0 hp)) T147_100
      hfix147_100 hinj147_100 hcardT147_100
      (fun i => conj_mem_of_fixedPoints _ _ (T147_100 i) (hfix147_100 i) _)
      ⟨147, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 0 hp) Q2.T147_100_2 Q2.hfix147_100_2 Q2.hinj147_100_2
      Q2.hcardT147_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_100_2 i) (Q2.hfix147_100_2 i) _)
      colCert_147_100_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_100_1 (hp : 1 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 1 (transLenTr ⟨100, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 1 (transLenTr ⟨100, by decide⟩ 1 hp)) T147_100
      hfix147_100 hinj147_100 hcardT147_100
      (fun i => conj_mem_of_fixedPoints _ _ (T147_100 i) (hfix147_100 i) _)
      ⟨147, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 1 hp) Q2.T147_100_2 Q2.hfix147_100_2 Q2.hinj147_100_2
      Q2.hcardT147_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_100_2 i) (Q2.hfix147_100_2 i) _)
      colCert_147_100_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_100_2 (hp : 2 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 2 (transLenTr ⟨100, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 2 (transLenTr ⟨100, by decide⟩ 2 hp)) T147_100
      hfix147_100 hinj147_100 hcardT147_100
      (fun i => conj_mem_of_fixedPoints _ _ (T147_100 i) (hfix147_100 i) _)
      ⟨147, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 2 hp) Q2.T147_100_2 Q2.hfix147_100_2 Q2.hinj147_100_2
      Q2.hcardT147_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_100_2 i) (Q2.hfix147_100_2 i) _)
      colCert_147_100_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_100_3 (hp : 3 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 3 (transLenTr ⟨100, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 3 (transLenTr ⟨100, by decide⟩ 3 hp)) T147_100
      hfix147_100 hinj147_100 hcardT147_100
      (fun i => conj_mem_of_fixedPoints _ _ (T147_100 i) (hfix147_100 i) _)
      ⟨147, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 3 hp) Q2.T147_100_2 Q2.hfix147_100_2 Q2.hinj147_100_2
      Q2.hcardT147_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_100_2 i) (Q2.hfix147_100_2 i) _)
      colCert_147_100_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_100_4 (hp : 4 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 4 (transLenTr ⟨100, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 4 (transLenTr ⟨100, by decide⟩ 4 hp)) T147_100
      hfix147_100 hinj147_100 hcardT147_100
      (fun i => conj_mem_of_fixedPoints _ _ (T147_100 i) (hfix147_100 i) _)
      ⟨147, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 4 hp) Q2.T147_100_2 Q2.hfix147_100_2 Q2.hinj147_100_2
      Q2.hcardT147_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_100_2 i) (Q2.hfix147_100_2 i) _)
      colCert_147_100_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_100_5 (hp : 5 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 5 (transLenTr ⟨100, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 5 (transLenTr ⟨100, by decide⟩ 5 hp)) T147_100
      hfix147_100 hinj147_100 hcardT147_100
      (fun i => conj_mem_of_fixedPoints _ _ (T147_100 i) (hfix147_100 i) _)
      ⟨147, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 5 hp) Q2.T147_100_2 Q2.hfix147_100_2 Q2.hinj147_100_2
      Q2.hcardT147_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_100_2 i) (Q2.hfix147_100_2 i) _)
      colCert_147_100_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_100_10 (hp : 10 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 10 (transLenTr ⟨100, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 10 (transLenTr ⟨100, by decide⟩ 10 hp)) T147_100
      hfix147_100 hinj147_100 hcardT147_100
      (fun i => conj_mem_of_fixedPoints _ _ (T147_100 i) (hfix147_100 i) _)
      ⟨147, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 10 hp) Q2.T147_100_2 Q2.hfix147_100_2 Q2.hinj147_100_2
      Q2.hcardT147_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_100_2 i) (Q2.hfix147_100_2 i) _)
      colCert_147_100_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_100_15 (hp : 15 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 15 (transLenTr ⟨100, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 15 (transLenTr ⟨100, by decide⟩ 15 hp)) T147_100
      hfix147_100 hinj147_100 hcardT147_100
      (fun i => conj_mem_of_fixedPoints _ _ (T147_100 i) (hfix147_100 i) _)
      ⟨147, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 15 hp) Q2.T147_100_2 Q2.hfix147_100_2 Q2.hinj147_100_2
      Q2.hcardT147_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_100_2 i) (Q2.hfix147_100_2 i) _)
      colCert_147_100_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_100_20 (hp : 20 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 20 (transLenTr ⟨100, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 20 (transLenTr ⟨100, by decide⟩ 20 hp)) T147_100
      hfix147_100 hinj147_100 hcardT147_100
      (fun i => conj_mem_of_fixedPoints _ _ (T147_100 i) (hfix147_100 i) _)
      ⟨147, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 20 hp) Q2.T147_100_2 Q2.hfix147_100_2 Q2.hinj147_100_2
      Q2.hcardT147_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_100_2 i) (Q2.hfix147_100_2 i) _)
      colCert_147_100_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_100_25 (hp : 25 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 25 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 25 (transLenTr ⟨100, by decide⟩ 25 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 25 (transLenTr ⟨100, by decide⟩ 25 hp)) T147_100
      hfix147_100 hinj147_100 hcardT147_100
      (fun i => conj_mem_of_fixedPoints _ _ (T147_100 i) (hfix147_100 i) _)
      ⟨147, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 25 hp) Q2.T147_100_2 Q2.hfix147_100_2 Q2.hinj147_100_2
      Q2.hcardT147_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_100_2 i) (Q2.hfix147_100_2 i) _)
      colCert_147_100_25.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_100_50 (hp : 50 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 50 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 50 (transLenTr ⟨100, by decide⟩ 50 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 50 (transLenTr ⟨100, by decide⟩ 50 hp)) T147_100
      hfix147_100 hinj147_100 hcardT147_100
      (fun i => conj_mem_of_fixedPoints _ _ (T147_100 i) (hfix147_100 i) _)
      ⟨147, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 50 hp) Q2.T147_100_2 Q2.hfix147_100_2 Q2.hinj147_100_2
      Q2.hcardT147_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_100_2 i) (Q2.hfix147_100_2 i) _)
      colCert_147_100_50.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_100_75 (hp : 75 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 75 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 75 (transLenTr ⟨100, by decide⟩ 75 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 75 (transLenTr ⟨100, by decide⟩ 75 hp)) T147_100
      hfix147_100 hinj147_100 hcardT147_100
      (fun i => conj_mem_of_fixedPoints _ _ (T147_100 i) (hfix147_100 i) _)
      ⟨147, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 75 hp) Q2.T147_100_2 Q2.hfix147_100_2 Q2.hinj147_100_2
      Q2.hcardT147_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_100_2 i) (Q2.hfix147_100_2 i) _)
      colCert_147_100_75.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_100_100 (hp : 100 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 100 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 100 (transLenTr ⟨100, by decide⟩ 100 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 100 (transLenTr ⟨100, by decide⟩ 100 hp)) T147_100
      hfix147_100 hinj147_100 hcardT147_100
      (fun i => conj_mem_of_fixedPoints _ _ (T147_100 i) (hfix147_100 i) _)
      ⟨147, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 100 hp) Q2.T147_100_2 Q2.hfix147_100_2 Q2.hinj147_100_2
      Q2.hcardT147_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_100_2 i) (Q2.hfix147_100_2 i) _)
      colCert_147_100_100.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_101_0 (hp : 0 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 0 (transLenTr ⟨101, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 0 (transLenTr ⟨101, by decide⟩ 0 hp)) T147_101
      hfix147_101 hinj147_101 hcardT147_101
      (fun i => conj_mem_of_fixedPoints _ _ (T147_101 i) (hfix147_101 i) _)
      ⟨147, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 0 hp) Q2.T147_101_2 Q2.hfix147_101_2 Q2.hinj147_101_2
      Q2.hcardT147_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_101_2 i) (Q2.hfix147_101_2 i) _)
      colCert_147_101_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_101_1 (hp : 1 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 1 (transLenTr ⟨101, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 1 (transLenTr ⟨101, by decide⟩ 1 hp)) T147_101
      hfix147_101 hinj147_101 hcardT147_101
      (fun i => conj_mem_of_fixedPoints _ _ (T147_101 i) (hfix147_101 i) _)
      ⟨147, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 1 hp) Q2.T147_101_2 Q2.hfix147_101_2 Q2.hinj147_101_2
      Q2.hcardT147_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_101_2 i) (Q2.hfix147_101_2 i) _)
      colCert_147_101_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_101_2 (hp : 2 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 2 (transLenTr ⟨101, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 2 (transLenTr ⟨101, by decide⟩ 2 hp)) T147_101
      hfix147_101 hinj147_101 hcardT147_101
      (fun i => conj_mem_of_fixedPoints _ _ (T147_101 i) (hfix147_101 i) _)
      ⟨147, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 2 hp) Q2.T147_101_2 Q2.hfix147_101_2 Q2.hinj147_101_2
      Q2.hcardT147_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_101_2 i) (Q2.hfix147_101_2 i) _)
      colCert_147_101_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_101_3 (hp : 3 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 3 (transLenTr ⟨101, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 3 (transLenTr ⟨101, by decide⟩ 3 hp)) T147_101
      hfix147_101 hinj147_101 hcardT147_101
      (fun i => conj_mem_of_fixedPoints _ _ (T147_101 i) (hfix147_101 i) _)
      ⟨147, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 3 hp) Q2.T147_101_2 Q2.hfix147_101_2 Q2.hinj147_101_2
      Q2.hcardT147_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_101_2 i) (Q2.hfix147_101_2 i) _)
      colCert_147_101_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_101_4 (hp : 4 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 4 (transLenTr ⟨101, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 4 (transLenTr ⟨101, by decide⟩ 4 hp)) T147_101
      hfix147_101 hinj147_101 hcardT147_101
      (fun i => conj_mem_of_fixedPoints _ _ (T147_101 i) (hfix147_101 i) _)
      ⟨147, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 4 hp) Q2.T147_101_2 Q2.hfix147_101_2 Q2.hinj147_101_2
      Q2.hcardT147_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_101_2 i) (Q2.hfix147_101_2 i) _)
      colCert_147_101_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_101_5 (hp : 5 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 5 (transLenTr ⟨101, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 5 (transLenTr ⟨101, by decide⟩ 5 hp)) T147_101
      hfix147_101 hinj147_101 hcardT147_101
      (fun i => conj_mem_of_fixedPoints _ _ (T147_101 i) (hfix147_101 i) _)
      ⟨147, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 5 hp) Q2.T147_101_2 Q2.hfix147_101_2 Q2.hinj147_101_2
      Q2.hcardT147_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_101_2 i) (Q2.hfix147_101_2 i) _)
      colCert_147_101_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_101_10 (hp : 10 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 10 (transLenTr ⟨101, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 10 (transLenTr ⟨101, by decide⟩ 10 hp)) T147_101
      hfix147_101 hinj147_101 hcardT147_101
      (fun i => conj_mem_of_fixedPoints _ _ (T147_101 i) (hfix147_101 i) _)
      ⟨147, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 10 hp) Q2.T147_101_2 Q2.hfix147_101_2 Q2.hinj147_101_2
      Q2.hcardT147_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_101_2 i) (Q2.hfix147_101_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨101, by decide⟩ 10 (transLenTr ⟨101, by decide⟩ 10 hp) : ↥(reps ⟨101, by decide⟩)) : Coordinate 1)
        T147_101 = colFn colCertDiv_147_101_10.D1 (m := 1) from colCertDiv_147_101_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨101, by decide⟩ 10 hp : ↥(Q2.reps ⟨101, by decide⟩)) : Coordinate 2)
        Q2.T147_101_2 = colFn colCertDiv_147_101_10.D2 (m := 1) from colCertDiv_147_101_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_101_10_match


theorem leaf_147_101_15 (hp : 15 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 15 (transLenTr ⟨101, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 15 (transLenTr ⟨101, by decide⟩ 15 hp)) T147_101
      hfix147_101 hinj147_101 hcardT147_101
      (fun i => conj_mem_of_fixedPoints _ _ (T147_101 i) (hfix147_101 i) _)
      ⟨147, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 15 hp) Q2.T147_101_2 Q2.hfix147_101_2 Q2.hinj147_101_2
      Q2.hcardT147_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_101_2 i) (Q2.hfix147_101_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨101, by decide⟩ 15 (transLenTr ⟨101, by decide⟩ 15 hp) : ↥(reps ⟨101, by decide⟩)) : Coordinate 1)
        T147_101 = colFn colCertDiv_147_101_15.D1 (m := 1) from colCertDiv_147_101_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨101, by decide⟩ 15 hp : ↥(Q2.reps ⟨101, by decide⟩)) : Coordinate 2)
        Q2.T147_101_2 = colFn colCertDiv_147_101_15.D2 (m := 1) from colCertDiv_147_101_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_101_15_match


theorem leaf_147_101_20 (hp : 20 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 20 (transLenTr ⟨101, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 20 (transLenTr ⟨101, by decide⟩ 20 hp)) T147_101
      hfix147_101 hinj147_101 hcardT147_101
      (fun i => conj_mem_of_fixedPoints _ _ (T147_101 i) (hfix147_101 i) _)
      ⟨147, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 20 hp) Q2.T147_101_2 Q2.hfix147_101_2 Q2.hinj147_101_2
      Q2.hcardT147_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_101_2 i) (Q2.hfix147_101_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨101, by decide⟩ 20 (transLenTr ⟨101, by decide⟩ 20 hp) : ↥(reps ⟨101, by decide⟩)) : Coordinate 1)
        T147_101 = colFn colCertDiv_147_101_20.D1 (m := 1) from colCertDiv_147_101_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨101, by decide⟩ 20 hp : ↥(Q2.reps ⟨101, by decide⟩)) : Coordinate 2)
        Q2.T147_101_2 = colFn colCertDiv_147_101_20.D2 (m := 1) from colCertDiv_147_101_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_101_20_match


theorem leaf_147_102_0 (hp : 0 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 0 (transLenTr ⟨102, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 0 (transLenTr ⟨102, by decide⟩ 0 hp)) T147_102
      hfix147_102 hinj147_102 hcardT147_102
      (fun i => conj_mem_of_fixedPoints _ _ (T147_102 i) (hfix147_102 i) _)
      ⟨147, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 0 hp) Q2.T147_102_2 Q2.hfix147_102_2 Q2.hinj147_102_2
      Q2.hcardT147_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_102_2 i) (Q2.hfix147_102_2 i) _)
      colCert_147_102_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_102_1 (hp : 1 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 1 (transLenTr ⟨102, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 1 (transLenTr ⟨102, by decide⟩ 1 hp)) T147_102
      hfix147_102 hinj147_102 hcardT147_102
      (fun i => conj_mem_of_fixedPoints _ _ (T147_102 i) (hfix147_102 i) _)
      ⟨147, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 1 hp) Q2.T147_102_2 Q2.hfix147_102_2 Q2.hinj147_102_2
      Q2.hcardT147_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_102_2 i) (Q2.hfix147_102_2 i) _)
      colCert_147_102_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_102_2 (hp : 2 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 2 (transLenTr ⟨102, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 2 (transLenTr ⟨102, by decide⟩ 2 hp)) T147_102
      hfix147_102 hinj147_102 hcardT147_102
      (fun i => conj_mem_of_fixedPoints _ _ (T147_102 i) (hfix147_102 i) _)
      ⟨147, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 2 hp) Q2.T147_102_2 Q2.hfix147_102_2 Q2.hinj147_102_2
      Q2.hcardT147_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_102_2 i) (Q2.hfix147_102_2 i) _)
      colCert_147_102_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_102_3 (hp : 3 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 3 (transLenTr ⟨102, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 3 (transLenTr ⟨102, by decide⟩ 3 hp)) T147_102
      hfix147_102 hinj147_102 hcardT147_102
      (fun i => conj_mem_of_fixedPoints _ _ (T147_102 i) (hfix147_102 i) _)
      ⟨147, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 3 hp) Q2.T147_102_2 Q2.hfix147_102_2 Q2.hinj147_102_2
      Q2.hcardT147_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_102_2 i) (Q2.hfix147_102_2 i) _)
      colCert_147_102_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_102_4 (hp : 4 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 4 (transLenTr ⟨102, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 4 (transLenTr ⟨102, by decide⟩ 4 hp)) T147_102
      hfix147_102 hinj147_102 hcardT147_102
      (fun i => conj_mem_of_fixedPoints _ _ (T147_102 i) (hfix147_102 i) _)
      ⟨147, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 4 hp) Q2.T147_102_2 Q2.hfix147_102_2 Q2.hinj147_102_2
      Q2.hcardT147_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_102_2 i) (Q2.hfix147_102_2 i) _)
      colCert_147_102_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_102_5 (hp : 5 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 5 (transLenTr ⟨102, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 5 (transLenTr ⟨102, by decide⟩ 5 hp)) T147_102
      hfix147_102 hinj147_102 hcardT147_102
      (fun i => conj_mem_of_fixedPoints _ _ (T147_102 i) (hfix147_102 i) _)
      ⟨147, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 5 hp) Q2.T147_102_2 Q2.hfix147_102_2 Q2.hinj147_102_2
      Q2.hcardT147_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_102_2 i) (Q2.hfix147_102_2 i) _)
      colCert_147_102_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_102_10 (hp : 10 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 10 (transLenTr ⟨102, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 10 (transLenTr ⟨102, by decide⟩ 10 hp)) T147_102
      hfix147_102 hinj147_102 hcardT147_102
      (fun i => conj_mem_of_fixedPoints _ _ (T147_102 i) (hfix147_102 i) _)
      ⟨147, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 10 hp) Q2.T147_102_2 Q2.hfix147_102_2 Q2.hinj147_102_2
      Q2.hcardT147_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_102_2 i) (Q2.hfix147_102_2 i) _)
      colCert_147_102_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_102_15 (hp : 15 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 15 (transLenTr ⟨102, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 15 (transLenTr ⟨102, by decide⟩ 15 hp)) T147_102
      hfix147_102 hinj147_102 hcardT147_102
      (fun i => conj_mem_of_fixedPoints _ _ (T147_102 i) (hfix147_102 i) _)
      ⟨147, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 15 hp) Q2.T147_102_2 Q2.hfix147_102_2 Q2.hinj147_102_2
      Q2.hcardT147_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_102_2 i) (Q2.hfix147_102_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨102, by decide⟩ 15 (transLenTr ⟨102, by decide⟩ 15 hp) : ↥(reps ⟨102, by decide⟩)) : Coordinate 1)
        T147_102 = colFn colCertDiv_147_102_15.D1 (m := 1) from colCertDiv_147_102_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨102, by decide⟩ 15 hp : ↥(Q2.reps ⟨102, by decide⟩)) : Coordinate 2)
        Q2.T147_102_2 = colFn colCertDiv_147_102_15.D2 (m := 1) from colCertDiv_147_102_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_102_15_match


theorem leaf_147_102_20 (hp : 20 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 20 (transLenTr ⟨102, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 20 (transLenTr ⟨102, by decide⟩ 20 hp)) T147_102
      hfix147_102 hinj147_102 hcardT147_102
      (fun i => conj_mem_of_fixedPoints _ _ (T147_102 i) (hfix147_102 i) _)
      ⟨147, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 20 hp) Q2.T147_102_2 Q2.hfix147_102_2 Q2.hinj147_102_2
      Q2.hcardT147_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_102_2 i) (Q2.hfix147_102_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨102, by decide⟩ 20 (transLenTr ⟨102, by decide⟩ 20 hp) : ↥(reps ⟨102, by decide⟩)) : Coordinate 1)
        T147_102 = colFn colCertDiv_147_102_20.D1 (m := 1) from colCertDiv_147_102_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨102, by decide⟩ 20 hp : ↥(Q2.reps ⟨102, by decide⟩)) : Coordinate 2)
        Q2.T147_102_2 = colFn colCertDiv_147_102_20.D2 (m := 1) from colCertDiv_147_102_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_102_20_match


theorem leaf_147_103_0 (hp : 0 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 0 (transLenTr ⟨103, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 0 (transLenTr ⟨103, by decide⟩ 0 hp)) T147_103
      hfix147_103 hinj147_103 hcardT147_103
      (fun i => conj_mem_of_fixedPoints _ _ (T147_103 i) (hfix147_103 i) _)
      ⟨147, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 0 hp) Q2.T147_103_2 Q2.hfix147_103_2 Q2.hinj147_103_2
      Q2.hcardT147_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_103_2 i) (Q2.hfix147_103_2 i) _)
      colCert_147_103_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_103_1 (hp : 1 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 1 (transLenTr ⟨103, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 1 (transLenTr ⟨103, by decide⟩ 1 hp)) T147_103
      hfix147_103 hinj147_103 hcardT147_103
      (fun i => conj_mem_of_fixedPoints _ _ (T147_103 i) (hfix147_103 i) _)
      ⟨147, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 1 hp) Q2.T147_103_2 Q2.hfix147_103_2 Q2.hinj147_103_2
      Q2.hcardT147_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_103_2 i) (Q2.hfix147_103_2 i) _)
      colCert_147_103_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_103_2 (hp : 2 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 2 (transLenTr ⟨103, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 2 (transLenTr ⟨103, by decide⟩ 2 hp)) T147_103
      hfix147_103 hinj147_103 hcardT147_103
      (fun i => conj_mem_of_fixedPoints _ _ (T147_103 i) (hfix147_103 i) _)
      ⟨147, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 2 hp) Q2.T147_103_2 Q2.hfix147_103_2 Q2.hinj147_103_2
      Q2.hcardT147_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_103_2 i) (Q2.hfix147_103_2 i) _)
      colCert_147_103_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_103_3 (hp : 3 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 3 (transLenTr ⟨103, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 3 (transLenTr ⟨103, by decide⟩ 3 hp)) T147_103
      hfix147_103 hinj147_103 hcardT147_103
      (fun i => conj_mem_of_fixedPoints _ _ (T147_103 i) (hfix147_103 i) _)
      ⟨147, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 3 hp) Q2.T147_103_2 Q2.hfix147_103_2 Q2.hinj147_103_2
      Q2.hcardT147_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_103_2 i) (Q2.hfix147_103_2 i) _)
      colCert_147_103_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_103_4 (hp : 4 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 4 (transLenTr ⟨103, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 4 (transLenTr ⟨103, by decide⟩ 4 hp)) T147_103
      hfix147_103 hinj147_103 hcardT147_103
      (fun i => conj_mem_of_fixedPoints _ _ (T147_103 i) (hfix147_103 i) _)
      ⟨147, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 4 hp) Q2.T147_103_2 Q2.hfix147_103_2 Q2.hinj147_103_2
      Q2.hcardT147_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_103_2 i) (Q2.hfix147_103_2 i) _)
      colCert_147_103_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_103_5 (hp : 5 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 5 (transLenTr ⟨103, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 5 (transLenTr ⟨103, by decide⟩ 5 hp)) T147_103
      hfix147_103 hinj147_103 hcardT147_103
      (fun i => conj_mem_of_fixedPoints _ _ (T147_103 i) (hfix147_103 i) _)
      ⟨147, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 5 hp) Q2.T147_103_2 Q2.hfix147_103_2 Q2.hinj147_103_2
      Q2.hcardT147_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_103_2 i) (Q2.hfix147_103_2 i) _)
      colCert_147_103_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_103_10 (hp : 10 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 10 (transLenTr ⟨103, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 10 (transLenTr ⟨103, by decide⟩ 10 hp)) T147_103
      hfix147_103 hinj147_103 hcardT147_103
      (fun i => conj_mem_of_fixedPoints _ _ (T147_103 i) (hfix147_103 i) _)
      ⟨147, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 10 hp) Q2.T147_103_2 Q2.hfix147_103_2 Q2.hinj147_103_2
      Q2.hcardT147_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_103_2 i) (Q2.hfix147_103_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨103, by decide⟩ 10 (transLenTr ⟨103, by decide⟩ 10 hp) : ↥(reps ⟨103, by decide⟩)) : Coordinate 1)
        T147_103 = colFn colCertDiv_147_103_10.D1 (m := 1) from colCertDiv_147_103_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨103, by decide⟩ 10 hp : ↥(Q2.reps ⟨103, by decide⟩)) : Coordinate 2)
        Q2.T147_103_2 = colFn colCertDiv_147_103_10.D2 (m := 1) from colCertDiv_147_103_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_103_10_match


theorem leaf_147_103_15 (hp : 15 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 15 (transLenTr ⟨103, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 15 (transLenTr ⟨103, by decide⟩ 15 hp)) T147_103
      hfix147_103 hinj147_103 hcardT147_103
      (fun i => conj_mem_of_fixedPoints _ _ (T147_103 i) (hfix147_103 i) _)
      ⟨147, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 15 hp) Q2.T147_103_2 Q2.hfix147_103_2 Q2.hinj147_103_2
      Q2.hcardT147_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_103_2 i) (Q2.hfix147_103_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨103, by decide⟩ 15 (transLenTr ⟨103, by decide⟩ 15 hp) : ↥(reps ⟨103, by decide⟩)) : Coordinate 1)
        T147_103 = colFn colCertDiv_147_103_15.D1 (m := 1) from colCertDiv_147_103_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨103, by decide⟩ 15 hp : ↥(Q2.reps ⟨103, by decide⟩)) : Coordinate 2)
        Q2.T147_103_2 = colFn colCertDiv_147_103_15.D2 (m := 1) from colCertDiv_147_103_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_103_15_match


theorem leaf_147_103_20 (hp : 20 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 20 (transLenTr ⟨103, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 20 (transLenTr ⟨103, by decide⟩ 20 hp)) T147_103
      hfix147_103 hinj147_103 hcardT147_103
      (fun i => conj_mem_of_fixedPoints _ _ (T147_103 i) (hfix147_103 i) _)
      ⟨147, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 20 hp) Q2.T147_103_2 Q2.hfix147_103_2 Q2.hinj147_103_2
      Q2.hcardT147_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_103_2 i) (Q2.hfix147_103_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨103, by decide⟩ 20 (transLenTr ⟨103, by decide⟩ 20 hp) : ↥(reps ⟨103, by decide⟩)) : Coordinate 1)
        T147_103 = colFn colCertDiv_147_103_20.D1 (m := 1) from colCertDiv_147_103_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨103, by decide⟩ 20 hp : ↥(Q2.reps ⟨103, by decide⟩)) : Coordinate 2)
        Q2.T147_103_2 = colFn colCertDiv_147_103_20.D2 (m := 1) from colCertDiv_147_103_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_103_20_match


theorem leaf_147_104_0 (hp : 0 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 0 (transLenTr ⟨104, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 0 (transLenTr ⟨104, by decide⟩ 0 hp)) T147_104
      hfix147_104 hinj147_104 hcardT147_104
      (fun i => conj_mem_of_fixedPoints _ _ (T147_104 i) (hfix147_104 i) _)
      ⟨147, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 0 hp) Q2.T147_104_2 Q2.hfix147_104_2 Q2.hinj147_104_2
      Q2.hcardT147_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_104_2 i) (Q2.hfix147_104_2 i) _)
      colCert_147_104_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_104_1 (hp : 1 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 1 (transLenTr ⟨104, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 1 (transLenTr ⟨104, by decide⟩ 1 hp)) T147_104
      hfix147_104 hinj147_104 hcardT147_104
      (fun i => conj_mem_of_fixedPoints _ _ (T147_104 i) (hfix147_104 i) _)
      ⟨147, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 1 hp) Q2.T147_104_2 Q2.hfix147_104_2 Q2.hinj147_104_2
      Q2.hcardT147_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_104_2 i) (Q2.hfix147_104_2 i) _)
      colCert_147_104_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_104_2 (hp : 2 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 2 (transLenTr ⟨104, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 2 (transLenTr ⟨104, by decide⟩ 2 hp)) T147_104
      hfix147_104 hinj147_104 hcardT147_104
      (fun i => conj_mem_of_fixedPoints _ _ (T147_104 i) (hfix147_104 i) _)
      ⟨147, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 2 hp) Q2.T147_104_2 Q2.hfix147_104_2 Q2.hinj147_104_2
      Q2.hcardT147_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_104_2 i) (Q2.hfix147_104_2 i) _)
      colCert_147_104_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_104_3 (hp : 3 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 3 (transLenTr ⟨104, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 3 (transLenTr ⟨104, by decide⟩ 3 hp)) T147_104
      hfix147_104 hinj147_104 hcardT147_104
      (fun i => conj_mem_of_fixedPoints _ _ (T147_104 i) (hfix147_104 i) _)
      ⟨147, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 3 hp) Q2.T147_104_2 Q2.hfix147_104_2 Q2.hinj147_104_2
      Q2.hcardT147_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_104_2 i) (Q2.hfix147_104_2 i) _)
      colCert_147_104_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_104_4 (hp : 4 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 4 (transLenTr ⟨104, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 4 (transLenTr ⟨104, by decide⟩ 4 hp)) T147_104
      hfix147_104 hinj147_104 hcardT147_104
      (fun i => conj_mem_of_fixedPoints _ _ (T147_104 i) (hfix147_104 i) _)
      ⟨147, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 4 hp) Q2.T147_104_2 Q2.hfix147_104_2 Q2.hinj147_104_2
      Q2.hcardT147_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_104_2 i) (Q2.hfix147_104_2 i) _)
      colCert_147_104_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_104_5 (hp : 5 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 5 (transLenTr ⟨104, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 5 (transLenTr ⟨104, by decide⟩ 5 hp)) T147_104
      hfix147_104 hinj147_104 hcardT147_104
      (fun i => conj_mem_of_fixedPoints _ _ (T147_104 i) (hfix147_104 i) _)
      ⟨147, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 5 hp) Q2.T147_104_2 Q2.hfix147_104_2 Q2.hinj147_104_2
      Q2.hcardT147_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_104_2 i) (Q2.hfix147_104_2 i) _)
      colCert_147_104_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_104_10 (hp : 10 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 10 (transLenTr ⟨104, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 10 (transLenTr ⟨104, by decide⟩ 10 hp)) T147_104
      hfix147_104 hinj147_104 hcardT147_104
      (fun i => conj_mem_of_fixedPoints _ _ (T147_104 i) (hfix147_104 i) _)
      ⟨147, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 10 hp) Q2.T147_104_2 Q2.hfix147_104_2 Q2.hinj147_104_2
      Q2.hcardT147_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_104_2 i) (Q2.hfix147_104_2 i) _)
      colCert_147_104_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_104_15 (hp : 15 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 15 (transLenTr ⟨104, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 15 (transLenTr ⟨104, by decide⟩ 15 hp)) T147_104
      hfix147_104 hinj147_104 hcardT147_104
      (fun i => conj_mem_of_fixedPoints _ _ (T147_104 i) (hfix147_104 i) _)
      ⟨147, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 15 hp) Q2.T147_104_2 Q2.hfix147_104_2 Q2.hinj147_104_2
      Q2.hcardT147_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_104_2 i) (Q2.hfix147_104_2 i) _)
      colCert_147_104_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_104_20 (hp : 20 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 20 (transLenTr ⟨104, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 20 (transLenTr ⟨104, by decide⟩ 20 hp)) T147_104
      hfix147_104 hinj147_104 hcardT147_104
      (fun i => conj_mem_of_fixedPoints _ _ (T147_104 i) (hfix147_104 i) _)
      ⟨147, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 20 hp) Q2.T147_104_2 Q2.hfix147_104_2 Q2.hinj147_104_2
      Q2.hcardT147_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_104_2 i) (Q2.hfix147_104_2 i) _)
      colCert_147_104_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_105_0 (hp : 0 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 0 (transLenTr ⟨105, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 0 (transLenTr ⟨105, by decide⟩ 0 hp)) T147_105
      hfix147_105 hinj147_105 hcardT147_105
      (fun i => conj_mem_of_fixedPoints _ _ (T147_105 i) (hfix147_105 i) _)
      ⟨147, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 0 hp) Q2.T147_105_2 Q2.hfix147_105_2 Q2.hinj147_105_2
      Q2.hcardT147_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_105_2 i) (Q2.hfix147_105_2 i) _)
      colCert_147_105_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_105_1 (hp : 1 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 1 (transLenTr ⟨105, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 1 (transLenTr ⟨105, by decide⟩ 1 hp)) T147_105
      hfix147_105 hinj147_105 hcardT147_105
      (fun i => conj_mem_of_fixedPoints _ _ (T147_105 i) (hfix147_105 i) _)
      ⟨147, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 1 hp) Q2.T147_105_2 Q2.hfix147_105_2 Q2.hinj147_105_2
      Q2.hcardT147_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_105_2 i) (Q2.hfix147_105_2 i) _)
      colCert_147_105_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_105_2 (hp : 2 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 2 (transLenTr ⟨105, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 2 (transLenTr ⟨105, by decide⟩ 2 hp)) T147_105
      hfix147_105 hinj147_105 hcardT147_105
      (fun i => conj_mem_of_fixedPoints _ _ (T147_105 i) (hfix147_105 i) _)
      ⟨147, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 2 hp) Q2.T147_105_2 Q2.hfix147_105_2 Q2.hinj147_105_2
      Q2.hcardT147_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_105_2 i) (Q2.hfix147_105_2 i) _)
      colCert_147_105_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_105_3 (hp : 3 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 3 (transLenTr ⟨105, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 3 (transLenTr ⟨105, by decide⟩ 3 hp)) T147_105
      hfix147_105 hinj147_105 hcardT147_105
      (fun i => conj_mem_of_fixedPoints _ _ (T147_105 i) (hfix147_105 i) _)
      ⟨147, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 3 hp) Q2.T147_105_2 Q2.hfix147_105_2 Q2.hinj147_105_2
      Q2.hcardT147_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_105_2 i) (Q2.hfix147_105_2 i) _)
      colCert_147_105_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_105_4 (hp : 4 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 4 (transLenTr ⟨105, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 4 (transLenTr ⟨105, by decide⟩ 4 hp)) T147_105
      hfix147_105 hinj147_105 hcardT147_105
      (fun i => conj_mem_of_fixedPoints _ _ (T147_105 i) (hfix147_105 i) _)
      ⟨147, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 4 hp) Q2.T147_105_2 Q2.hfix147_105_2 Q2.hinj147_105_2
      Q2.hcardT147_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_105_2 i) (Q2.hfix147_105_2 i) _)
      colCert_147_105_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_105_5 (hp : 5 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 5 (transLenTr ⟨105, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 5 (transLenTr ⟨105, by decide⟩ 5 hp)) T147_105
      hfix147_105 hinj147_105 hcardT147_105
      (fun i => conj_mem_of_fixedPoints _ _ (T147_105 i) (hfix147_105 i) _)
      ⟨147, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 5 hp) Q2.T147_105_2 Q2.hfix147_105_2 Q2.hinj147_105_2
      Q2.hcardT147_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_105_2 i) (Q2.hfix147_105_2 i) _)
      colCert_147_105_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_105_10 (hp : 10 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 10 (transLenTr ⟨105, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 10 (transLenTr ⟨105, by decide⟩ 10 hp)) T147_105
      hfix147_105 hinj147_105 hcardT147_105
      (fun i => conj_mem_of_fixedPoints _ _ (T147_105 i) (hfix147_105 i) _)
      ⟨147, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 10 hp) Q2.T147_105_2 Q2.hfix147_105_2 Q2.hinj147_105_2
      Q2.hcardT147_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_105_2 i) (Q2.hfix147_105_2 i) _)
      colCert_147_105_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_105_15 (hp : 15 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 15 (transLenTr ⟨105, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 15 (transLenTr ⟨105, by decide⟩ 15 hp)) T147_105
      hfix147_105 hinj147_105 hcardT147_105
      (fun i => conj_mem_of_fixedPoints _ _ (T147_105 i) (hfix147_105 i) _)
      ⟨147, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 15 hp) Q2.T147_105_2 Q2.hfix147_105_2 Q2.hinj147_105_2
      Q2.hcardT147_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_105_2 i) (Q2.hfix147_105_2 i) _)
      colCert_147_105_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_105_20 (hp : 20 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 20 (transLenTr ⟨105, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 20 (transLenTr ⟨105, by decide⟩ 20 hp)) T147_105
      hfix147_105 hinj147_105 hcardT147_105
      (fun i => conj_mem_of_fixedPoints _ _ (T147_105 i) (hfix147_105 i) _)
      ⟨147, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 20 hp) Q2.T147_105_2 Q2.hfix147_105_2 Q2.hinj147_105_2
      Q2.hcardT147_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_105_2 i) (Q2.hfix147_105_2 i) _)
      colCert_147_105_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_105_25 (hp : 25 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 25 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 25 (transLenTr ⟨105, by decide⟩ 25 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 25 (transLenTr ⟨105, by decide⟩ 25 hp)) T147_105
      hfix147_105 hinj147_105 hcardT147_105
      (fun i => conj_mem_of_fixedPoints _ _ (T147_105 i) (hfix147_105 i) _)
      ⟨147, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 25 hp) Q2.T147_105_2 Q2.hfix147_105_2 Q2.hinj147_105_2
      Q2.hcardT147_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_105_2 i) (Q2.hfix147_105_2 i) _)
      colCert_147_105_25.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_105_50 (hp : 50 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 50 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 50 (transLenTr ⟨105, by decide⟩ 50 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 50 (transLenTr ⟨105, by decide⟩ 50 hp)) T147_105
      hfix147_105 hinj147_105 hcardT147_105
      (fun i => conj_mem_of_fixedPoints _ _ (T147_105 i) (hfix147_105 i) _)
      ⟨147, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 50 hp) Q2.T147_105_2 Q2.hfix147_105_2 Q2.hinj147_105_2
      Q2.hcardT147_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_105_2 i) (Q2.hfix147_105_2 i) _)
      colCert_147_105_50.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_105_75 (hp : 75 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 75 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 75 (transLenTr ⟨105, by decide⟩ 75 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 75 (transLenTr ⟨105, by decide⟩ 75 hp)) T147_105
      hfix147_105 hinj147_105 hcardT147_105
      (fun i => conj_mem_of_fixedPoints _ _ (T147_105 i) (hfix147_105 i) _)
      ⟨147, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 75 hp) Q2.T147_105_2 Q2.hfix147_105_2 Q2.hinj147_105_2
      Q2.hcardT147_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_105_2 i) (Q2.hfix147_105_2 i) _)
      colCert_147_105_75.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_105_100 (hp : 100 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 100 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 100 (transLenTr ⟨105, by decide⟩ 100 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 100 (transLenTr ⟨105, by decide⟩ 100 hp)) T147_105
      hfix147_105 hinj147_105 hcardT147_105
      (fun i => conj_mem_of_fixedPoints _ _ (T147_105 i) (hfix147_105 i) _)
      ⟨147, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 100 hp) Q2.T147_105_2 Q2.hfix147_105_2 Q2.hinj147_105_2
      Q2.hcardT147_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_105_2 i) (Q2.hfix147_105_2 i) _)
      colCert_147_105_100.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_106_0 (hp : 0 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 0 (transLenTr ⟨106, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 0 (transLenTr ⟨106, by decide⟩ 0 hp)) T147_106
      hfix147_106 hinj147_106 hcardT147_106
      (fun i => conj_mem_of_fixedPoints _ _ (T147_106 i) (hfix147_106 i) _)
      ⟨147, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 0 hp) Q2.T147_106_2 Q2.hfix147_106_2 Q2.hinj147_106_2
      Q2.hcardT147_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_106_2 i) (Q2.hfix147_106_2 i) _)
      colCert_147_106_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_106_1 (hp : 1 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 1 (transLenTr ⟨106, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 1 (transLenTr ⟨106, by decide⟩ 1 hp)) T147_106
      hfix147_106 hinj147_106 hcardT147_106
      (fun i => conj_mem_of_fixedPoints _ _ (T147_106 i) (hfix147_106 i) _)
      ⟨147, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 1 hp) Q2.T147_106_2 Q2.hfix147_106_2 Q2.hinj147_106_2
      Q2.hcardT147_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_106_2 i) (Q2.hfix147_106_2 i) _)
      colCert_147_106_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_106_2 (hp : 2 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 2 (transLenTr ⟨106, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 2 (transLenTr ⟨106, by decide⟩ 2 hp)) T147_106
      hfix147_106 hinj147_106 hcardT147_106
      (fun i => conj_mem_of_fixedPoints _ _ (T147_106 i) (hfix147_106 i) _)
      ⟨147, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 2 hp) Q2.T147_106_2 Q2.hfix147_106_2 Q2.hinj147_106_2
      Q2.hcardT147_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_106_2 i) (Q2.hfix147_106_2 i) _)
      colCert_147_106_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_106_3 (hp : 3 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 3 (transLenTr ⟨106, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 3 (transLenTr ⟨106, by decide⟩ 3 hp)) T147_106
      hfix147_106 hinj147_106 hcardT147_106
      (fun i => conj_mem_of_fixedPoints _ _ (T147_106 i) (hfix147_106 i) _)
      ⟨147, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 3 hp) Q2.T147_106_2 Q2.hfix147_106_2 Q2.hinj147_106_2
      Q2.hcardT147_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_106_2 i) (Q2.hfix147_106_2 i) _)
      colCert_147_106_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_106_4 (hp : 4 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 4 (transLenTr ⟨106, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 4 (transLenTr ⟨106, by decide⟩ 4 hp)) T147_106
      hfix147_106 hinj147_106 hcardT147_106
      (fun i => conj_mem_of_fixedPoints _ _ (T147_106 i) (hfix147_106 i) _)
      ⟨147, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 4 hp) Q2.T147_106_2 Q2.hfix147_106_2 Q2.hinj147_106_2
      Q2.hcardT147_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_106_2 i) (Q2.hfix147_106_2 i) _)
      colCert_147_106_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_106_5 (hp : 5 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 5 (transLenTr ⟨106, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 5 (transLenTr ⟨106, by decide⟩ 5 hp)) T147_106
      hfix147_106 hinj147_106 hcardT147_106
      (fun i => conj_mem_of_fixedPoints _ _ (T147_106 i) (hfix147_106 i) _)
      ⟨147, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 5 hp) Q2.T147_106_2 Q2.hfix147_106_2 Q2.hinj147_106_2
      Q2.hcardT147_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_106_2 i) (Q2.hfix147_106_2 i) _)
      colCert_147_106_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_106_10 (hp : 10 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 10 (transLenTr ⟨106, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 10 (transLenTr ⟨106, by decide⟩ 10 hp)) T147_106
      hfix147_106 hinj147_106 hcardT147_106
      (fun i => conj_mem_of_fixedPoints _ _ (T147_106 i) (hfix147_106 i) _)
      ⟨147, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 10 hp) Q2.T147_106_2 Q2.hfix147_106_2 Q2.hinj147_106_2
      Q2.hcardT147_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_106_2 i) (Q2.hfix147_106_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨106, by decide⟩ 10 (transLenTr ⟨106, by decide⟩ 10 hp) : ↥(reps ⟨106, by decide⟩)) : Coordinate 1)
        T147_106 = colFn colCertDiv_147_106_10.D1 (m := 1) from colCertDiv_147_106_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨106, by decide⟩ 10 hp : ↥(Q2.reps ⟨106, by decide⟩)) : Coordinate 2)
        Q2.T147_106_2 = colFn colCertDiv_147_106_10.D2 (m := 1) from colCertDiv_147_106_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_106_10_match


theorem leaf_147_106_15 (hp : 15 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 15 (transLenTr ⟨106, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 15 (transLenTr ⟨106, by decide⟩ 15 hp)) T147_106
      hfix147_106 hinj147_106 hcardT147_106
      (fun i => conj_mem_of_fixedPoints _ _ (T147_106 i) (hfix147_106 i) _)
      ⟨147, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 15 hp) Q2.T147_106_2 Q2.hfix147_106_2 Q2.hinj147_106_2
      Q2.hcardT147_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_106_2 i) (Q2.hfix147_106_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨106, by decide⟩ 15 (transLenTr ⟨106, by decide⟩ 15 hp) : ↥(reps ⟨106, by decide⟩)) : Coordinate 1)
        T147_106 = colFn colCertDiv_147_106_15.D1 (m := 1) from colCertDiv_147_106_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨106, by decide⟩ 15 hp : ↥(Q2.reps ⟨106, by decide⟩)) : Coordinate 2)
        Q2.T147_106_2 = colFn colCertDiv_147_106_15.D2 (m := 1) from colCertDiv_147_106_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_106_15_match


theorem leaf_147_106_20 (hp : 20 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 20 (transLenTr ⟨106, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 20 (transLenTr ⟨106, by decide⟩ 20 hp)) T147_106
      hfix147_106 hinj147_106 hcardT147_106
      (fun i => conj_mem_of_fixedPoints _ _ (T147_106 i) (hfix147_106 i) _)
      ⟨147, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 20 hp) Q2.T147_106_2 Q2.hfix147_106_2 Q2.hinj147_106_2
      Q2.hcardT147_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_106_2 i) (Q2.hfix147_106_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨106, by decide⟩ 20 (transLenTr ⟨106, by decide⟩ 20 hp) : ↥(reps ⟨106, by decide⟩)) : Coordinate 1)
        T147_106 = colFn colCertDiv_147_106_20.D1 (m := 1) from colCertDiv_147_106_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨106, by decide⟩ 20 hp : ↥(Q2.reps ⟨106, by decide⟩)) : Coordinate 2)
        Q2.T147_106_2 = colFn colCertDiv_147_106_20.D2 (m := 1) from colCertDiv_147_106_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_106_20_match


theorem leaf_147_107_0 (hp : 0 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 0 (transLenTr ⟨107, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 0 (transLenTr ⟨107, by decide⟩ 0 hp)) T147_107
      hfix147_107 hinj147_107 hcardT147_107
      (fun i => conj_mem_of_fixedPoints _ _ (T147_107 i) (hfix147_107 i) _)
      ⟨147, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 0 hp) Q2.T147_107_2 Q2.hfix147_107_2 Q2.hinj147_107_2
      Q2.hcardT147_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_107_2 i) (Q2.hfix147_107_2 i) _)
      colCert_147_107_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_107_1 (hp : 1 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 1 (transLenTr ⟨107, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 1 (transLenTr ⟨107, by decide⟩ 1 hp)) T147_107
      hfix147_107 hinj147_107 hcardT147_107
      (fun i => conj_mem_of_fixedPoints _ _ (T147_107 i) (hfix147_107 i) _)
      ⟨147, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 1 hp) Q2.T147_107_2 Q2.hfix147_107_2 Q2.hinj147_107_2
      Q2.hcardT147_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_107_2 i) (Q2.hfix147_107_2 i) _)
      colCert_147_107_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_107_2 (hp : 2 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 2 (transLenTr ⟨107, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 2 (transLenTr ⟨107, by decide⟩ 2 hp)) T147_107
      hfix147_107 hinj147_107 hcardT147_107
      (fun i => conj_mem_of_fixedPoints _ _ (T147_107 i) (hfix147_107 i) _)
      ⟨147, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 2 hp) Q2.T147_107_2 Q2.hfix147_107_2 Q2.hinj147_107_2
      Q2.hcardT147_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_107_2 i) (Q2.hfix147_107_2 i) _)
      colCert_147_107_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_107_3 (hp : 3 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 3 (transLenTr ⟨107, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 3 (transLenTr ⟨107, by decide⟩ 3 hp)) T147_107
      hfix147_107 hinj147_107 hcardT147_107
      (fun i => conj_mem_of_fixedPoints _ _ (T147_107 i) (hfix147_107 i) _)
      ⟨147, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 3 hp) Q2.T147_107_2 Q2.hfix147_107_2 Q2.hinj147_107_2
      Q2.hcardT147_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_107_2 i) (Q2.hfix147_107_2 i) _)
      colCert_147_107_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_107_4 (hp : 4 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 4 (transLenTr ⟨107, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 4 (transLenTr ⟨107, by decide⟩ 4 hp)) T147_107
      hfix147_107 hinj147_107 hcardT147_107
      (fun i => conj_mem_of_fixedPoints _ _ (T147_107 i) (hfix147_107 i) _)
      ⟨147, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 4 hp) Q2.T147_107_2 Q2.hfix147_107_2 Q2.hinj147_107_2
      Q2.hcardT147_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_107_2 i) (Q2.hfix147_107_2 i) _)
      colCert_147_107_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_107_5 (hp : 5 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 5 (transLenTr ⟨107, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 5 (transLenTr ⟨107, by decide⟩ 5 hp)) T147_107
      hfix147_107 hinj147_107 hcardT147_107
      (fun i => conj_mem_of_fixedPoints _ _ (T147_107 i) (hfix147_107 i) _)
      ⟨147, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 5 hp) Q2.T147_107_2 Q2.hfix147_107_2 Q2.hinj147_107_2
      Q2.hcardT147_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_107_2 i) (Q2.hfix147_107_2 i) _)
      colCert_147_107_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_107_10 (hp : 10 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 10 (transLenTr ⟨107, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 10 (transLenTr ⟨107, by decide⟩ 10 hp)) T147_107
      hfix147_107 hinj147_107 hcardT147_107
      (fun i => conj_mem_of_fixedPoints _ _ (T147_107 i) (hfix147_107 i) _)
      ⟨147, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 10 hp) Q2.T147_107_2 Q2.hfix147_107_2 Q2.hinj147_107_2
      Q2.hcardT147_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_107_2 i) (Q2.hfix147_107_2 i) _)
      colCert_147_107_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_107_15 (hp : 15 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 15 (transLenTr ⟨107, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 15 (transLenTr ⟨107, by decide⟩ 15 hp)) T147_107
      hfix147_107 hinj147_107 hcardT147_107
      (fun i => conj_mem_of_fixedPoints _ _ (T147_107 i) (hfix147_107 i) _)
      ⟨147, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 15 hp) Q2.T147_107_2 Q2.hfix147_107_2 Q2.hinj147_107_2
      Q2.hcardT147_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_107_2 i) (Q2.hfix147_107_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨107, by decide⟩ 15 (transLenTr ⟨107, by decide⟩ 15 hp) : ↥(reps ⟨107, by decide⟩)) : Coordinate 1)
        T147_107 = colFn colCertDiv_147_107_15.D1 (m := 1) from colCertDiv_147_107_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨107, by decide⟩ 15 hp : ↥(Q2.reps ⟨107, by decide⟩)) : Coordinate 2)
        Q2.T147_107_2 = colFn colCertDiv_147_107_15.D2 (m := 1) from colCertDiv_147_107_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_107_15_match


theorem leaf_147_107_20 (hp : 20 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 20 (transLenTr ⟨107, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 20 (transLenTr ⟨107, by decide⟩ 20 hp)) T147_107
      hfix147_107 hinj147_107 hcardT147_107
      (fun i => conj_mem_of_fixedPoints _ _ (T147_107 i) (hfix147_107 i) _)
      ⟨147, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 20 hp) Q2.T147_107_2 Q2.hfix147_107_2 Q2.hinj147_107_2
      Q2.hcardT147_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_107_2 i) (Q2.hfix147_107_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨107, by decide⟩ 20 (transLenTr ⟨107, by decide⟩ 20 hp) : ↥(reps ⟨107, by decide⟩)) : Coordinate 1)
        T147_107 = colFn colCertDiv_147_107_20.D1 (m := 1) from colCertDiv_147_107_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨107, by decide⟩ 20 hp : ↥(Q2.reps ⟨107, by decide⟩)) : Coordinate 2)
        Q2.T147_107_2 = colFn colCertDiv_147_107_20.D2 (m := 1) from colCertDiv_147_107_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_107_20_match


theorem leaf_147_108_0 (hp : 0 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 0 (transLenTr ⟨108, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 0 (transLenTr ⟨108, by decide⟩ 0 hp)) T147_108
      hfix147_108 hinj147_108 hcardT147_108
      (fun i => conj_mem_of_fixedPoints _ _ (T147_108 i) (hfix147_108 i) _)
      ⟨147, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 0 hp) Q2.T147_108_2 Q2.hfix147_108_2 Q2.hinj147_108_2
      Q2.hcardT147_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_108_2 i) (Q2.hfix147_108_2 i) _)
      colCert_147_108_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_108_1 (hp : 1 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 1 (transLenTr ⟨108, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 1 (transLenTr ⟨108, by decide⟩ 1 hp)) T147_108
      hfix147_108 hinj147_108 hcardT147_108
      (fun i => conj_mem_of_fixedPoints _ _ (T147_108 i) (hfix147_108 i) _)
      ⟨147, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 1 hp) Q2.T147_108_2 Q2.hfix147_108_2 Q2.hinj147_108_2
      Q2.hcardT147_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_108_2 i) (Q2.hfix147_108_2 i) _)
      colCert_147_108_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_108_2 (hp : 2 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 2 (transLenTr ⟨108, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 2 (transLenTr ⟨108, by decide⟩ 2 hp)) T147_108
      hfix147_108 hinj147_108 hcardT147_108
      (fun i => conj_mem_of_fixedPoints _ _ (T147_108 i) (hfix147_108 i) _)
      ⟨147, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 2 hp) Q2.T147_108_2 Q2.hfix147_108_2 Q2.hinj147_108_2
      Q2.hcardT147_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_108_2 i) (Q2.hfix147_108_2 i) _)
      colCert_147_108_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_108_3 (hp : 3 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 3 (transLenTr ⟨108, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 3 (transLenTr ⟨108, by decide⟩ 3 hp)) T147_108
      hfix147_108 hinj147_108 hcardT147_108
      (fun i => conj_mem_of_fixedPoints _ _ (T147_108 i) (hfix147_108 i) _)
      ⟨147, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 3 hp) Q2.T147_108_2 Q2.hfix147_108_2 Q2.hinj147_108_2
      Q2.hcardT147_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_108_2 i) (Q2.hfix147_108_2 i) _)
      colCert_147_108_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_108_4 (hp : 4 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 4 (transLenTr ⟨108, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 4 (transLenTr ⟨108, by decide⟩ 4 hp)) T147_108
      hfix147_108 hinj147_108 hcardT147_108
      (fun i => conj_mem_of_fixedPoints _ _ (T147_108 i) (hfix147_108 i) _)
      ⟨147, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 4 hp) Q2.T147_108_2 Q2.hfix147_108_2 Q2.hinj147_108_2
      Q2.hcardT147_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_108_2 i) (Q2.hfix147_108_2 i) _)
      colCert_147_108_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_108_5 (hp : 5 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 5 (transLenTr ⟨108, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 5 (transLenTr ⟨108, by decide⟩ 5 hp)) T147_108
      hfix147_108 hinj147_108 hcardT147_108
      (fun i => conj_mem_of_fixedPoints _ _ (T147_108 i) (hfix147_108 i) _)
      ⟨147, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 5 hp) Q2.T147_108_2 Q2.hfix147_108_2 Q2.hinj147_108_2
      Q2.hcardT147_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_108_2 i) (Q2.hfix147_108_2 i) _)
      colCert_147_108_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_108_10 (hp : 10 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 10 (transLenTr ⟨108, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 10 (transLenTr ⟨108, by decide⟩ 10 hp)) T147_108
      hfix147_108 hinj147_108 hcardT147_108
      (fun i => conj_mem_of_fixedPoints _ _ (T147_108 i) (hfix147_108 i) _)
      ⟨147, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 10 hp) Q2.T147_108_2 Q2.hfix147_108_2 Q2.hinj147_108_2
      Q2.hcardT147_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_108_2 i) (Q2.hfix147_108_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨108, by decide⟩ 10 (transLenTr ⟨108, by decide⟩ 10 hp) : ↥(reps ⟨108, by decide⟩)) : Coordinate 1)
        T147_108 = colFn colCertDiv_147_108_10.D1 (m := 1) from colCertDiv_147_108_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨108, by decide⟩ 10 hp : ↥(Q2.reps ⟨108, by decide⟩)) : Coordinate 2)
        Q2.T147_108_2 = colFn colCertDiv_147_108_10.D2 (m := 1) from colCertDiv_147_108_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_108_10_match


theorem leaf_147_108_15 (hp : 15 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 15 (transLenTr ⟨108, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 15 (transLenTr ⟨108, by decide⟩ 15 hp)) T147_108
      hfix147_108 hinj147_108 hcardT147_108
      (fun i => conj_mem_of_fixedPoints _ _ (T147_108 i) (hfix147_108 i) _)
      ⟨147, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 15 hp) Q2.T147_108_2 Q2.hfix147_108_2 Q2.hinj147_108_2
      Q2.hcardT147_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_108_2 i) (Q2.hfix147_108_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨108, by decide⟩ 15 (transLenTr ⟨108, by decide⟩ 15 hp) : ↥(reps ⟨108, by decide⟩)) : Coordinate 1)
        T147_108 = colFn colCertDiv_147_108_15.D1 (m := 1) from colCertDiv_147_108_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨108, by decide⟩ 15 hp : ↥(Q2.reps ⟨108, by decide⟩)) : Coordinate 2)
        Q2.T147_108_2 = colFn colCertDiv_147_108_15.D2 (m := 1) from colCertDiv_147_108_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_108_15_match


theorem leaf_147_108_20 (hp : 20 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 20 (transLenTr ⟨108, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 20 (transLenTr ⟨108, by decide⟩ 20 hp)) T147_108
      hfix147_108 hinj147_108 hcardT147_108
      (fun i => conj_mem_of_fixedPoints _ _ (T147_108 i) (hfix147_108 i) _)
      ⟨147, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 20 hp) Q2.T147_108_2 Q2.hfix147_108_2 Q2.hinj147_108_2
      Q2.hcardT147_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_108_2 i) (Q2.hfix147_108_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨108, by decide⟩ 20 (transLenTr ⟨108, by decide⟩ 20 hp) : ↥(reps ⟨108, by decide⟩)) : Coordinate 1)
        T147_108 = colFn colCertDiv_147_108_20.D1 (m := 1) from colCertDiv_147_108_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨108, by decide⟩ 20 hp : ↥(Q2.reps ⟨108, by decide⟩)) : Coordinate 2)
        Q2.T147_108_2 = colFn colCertDiv_147_108_20.D2 (m := 1) from colCertDiv_147_108_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_108_20_match


theorem leaf_147_109_0 (hp : 0 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 0 (transLenTr ⟨109, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 0 (transLenTr ⟨109, by decide⟩ 0 hp)) T147_109
      hfix147_109 hinj147_109 hcardT147_109
      (fun i => conj_mem_of_fixedPoints _ _ (T147_109 i) (hfix147_109 i) _)
      ⟨147, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 0 hp) Q2.T147_109_2 Q2.hfix147_109_2 Q2.hinj147_109_2
      Q2.hcardT147_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_109_2 i) (Q2.hfix147_109_2 i) _)
      colCert_147_109_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_109_1 (hp : 1 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 1 (transLenTr ⟨109, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 1 (transLenTr ⟨109, by decide⟩ 1 hp)) T147_109
      hfix147_109 hinj147_109 hcardT147_109
      (fun i => conj_mem_of_fixedPoints _ _ (T147_109 i) (hfix147_109 i) _)
      ⟨147, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 1 hp) Q2.T147_109_2 Q2.hfix147_109_2 Q2.hinj147_109_2
      Q2.hcardT147_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_109_2 i) (Q2.hfix147_109_2 i) _)
      colCert_147_109_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_109_2 (hp : 2 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 2 (transLenTr ⟨109, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 2 (transLenTr ⟨109, by decide⟩ 2 hp)) T147_109
      hfix147_109 hinj147_109 hcardT147_109
      (fun i => conj_mem_of_fixedPoints _ _ (T147_109 i) (hfix147_109 i) _)
      ⟨147, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 2 hp) Q2.T147_109_2 Q2.hfix147_109_2 Q2.hinj147_109_2
      Q2.hcardT147_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_109_2 i) (Q2.hfix147_109_2 i) _)
      colCert_147_109_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_109_3 (hp : 3 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 3 (transLenTr ⟨109, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 3 (transLenTr ⟨109, by decide⟩ 3 hp)) T147_109
      hfix147_109 hinj147_109 hcardT147_109
      (fun i => conj_mem_of_fixedPoints _ _ (T147_109 i) (hfix147_109 i) _)
      ⟨147, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 3 hp) Q2.T147_109_2 Q2.hfix147_109_2 Q2.hinj147_109_2
      Q2.hcardT147_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_109_2 i) (Q2.hfix147_109_2 i) _)
      colCert_147_109_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_109_4 (hp : 4 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 4 (transLenTr ⟨109, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 4 (transLenTr ⟨109, by decide⟩ 4 hp)) T147_109
      hfix147_109 hinj147_109 hcardT147_109
      (fun i => conj_mem_of_fixedPoints _ _ (T147_109 i) (hfix147_109 i) _)
      ⟨147, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 4 hp) Q2.T147_109_2 Q2.hfix147_109_2 Q2.hinj147_109_2
      Q2.hcardT147_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_109_2 i) (Q2.hfix147_109_2 i) _)
      colCert_147_109_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_109_5 (hp : 5 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 5 (transLenTr ⟨109, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 5 (transLenTr ⟨109, by decide⟩ 5 hp)) T147_109
      hfix147_109 hinj147_109 hcardT147_109
      (fun i => conj_mem_of_fixedPoints _ _ (T147_109 i) (hfix147_109 i) _)
      ⟨147, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 5 hp) Q2.T147_109_2 Q2.hfix147_109_2 Q2.hinj147_109_2
      Q2.hcardT147_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_109_2 i) (Q2.hfix147_109_2 i) _)
      colCert_147_109_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_109_10 (hp : 10 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 10 (transLenTr ⟨109, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 10 (transLenTr ⟨109, by decide⟩ 10 hp)) T147_109
      hfix147_109 hinj147_109 hcardT147_109
      (fun i => conj_mem_of_fixedPoints _ _ (T147_109 i) (hfix147_109 i) _)
      ⟨147, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 10 hp) Q2.T147_109_2 Q2.hfix147_109_2 Q2.hinj147_109_2
      Q2.hcardT147_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_109_2 i) (Q2.hfix147_109_2 i) _)
      colCert_147_109_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_109_15 (hp : 15 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 15 (transLenTr ⟨109, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 15 (transLenTr ⟨109, by decide⟩ 15 hp)) T147_109
      hfix147_109 hinj147_109 hcardT147_109
      (fun i => conj_mem_of_fixedPoints _ _ (T147_109 i) (hfix147_109 i) _)
      ⟨147, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 15 hp) Q2.T147_109_2 Q2.hfix147_109_2 Q2.hinj147_109_2
      Q2.hcardT147_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_109_2 i) (Q2.hfix147_109_2 i) _)
      colCert_147_109_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_109_20 (hp : 20 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 20 (transLenTr ⟨109, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 20 (transLenTr ⟨109, by decide⟩ 20 hp)) T147_109
      hfix147_109 hinj147_109 hcardT147_109
      (fun i => conj_mem_of_fixedPoints _ _ (T147_109 i) (hfix147_109 i) _)
      ⟨147, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 20 hp) Q2.T147_109_2 Q2.hfix147_109_2 Q2.hinj147_109_2
      Q2.hcardT147_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_109_2 i) (Q2.hfix147_109_2 i) _)
      colCert_147_109_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_110_0 (hp : 0 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 0 (transLenTr ⟨110, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 0 (transLenTr ⟨110, by decide⟩ 0 hp)) T147_110
      hfix147_110 hinj147_110 hcardT147_110
      (fun i => conj_mem_of_fixedPoints _ _ (T147_110 i) (hfix147_110 i) _)
      ⟨147, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 0 hp) Q2.T147_110_2 Q2.hfix147_110_2 Q2.hinj147_110_2
      Q2.hcardT147_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_110_2 i) (Q2.hfix147_110_2 i) _)
      colCert_147_110_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_110_1 (hp : 1 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 1 (transLenTr ⟨110, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 1 (transLenTr ⟨110, by decide⟩ 1 hp)) T147_110
      hfix147_110 hinj147_110 hcardT147_110
      (fun i => conj_mem_of_fixedPoints _ _ (T147_110 i) (hfix147_110 i) _)
      ⟨147, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 1 hp) Q2.T147_110_2 Q2.hfix147_110_2 Q2.hinj147_110_2
      Q2.hcardT147_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_110_2 i) (Q2.hfix147_110_2 i) _)
      colCert_147_110_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_110_2 (hp : 2 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 2 (transLenTr ⟨110, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 2 (transLenTr ⟨110, by decide⟩ 2 hp)) T147_110
      hfix147_110 hinj147_110 hcardT147_110
      (fun i => conj_mem_of_fixedPoints _ _ (T147_110 i) (hfix147_110 i) _)
      ⟨147, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 2 hp) Q2.T147_110_2 Q2.hfix147_110_2 Q2.hinj147_110_2
      Q2.hcardT147_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_110_2 i) (Q2.hfix147_110_2 i) _)
      colCert_147_110_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_110_3 (hp : 3 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 3 (transLenTr ⟨110, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 3 (transLenTr ⟨110, by decide⟩ 3 hp)) T147_110
      hfix147_110 hinj147_110 hcardT147_110
      (fun i => conj_mem_of_fixedPoints _ _ (T147_110 i) (hfix147_110 i) _)
      ⟨147, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 3 hp) Q2.T147_110_2 Q2.hfix147_110_2 Q2.hinj147_110_2
      Q2.hcardT147_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_110_2 i) (Q2.hfix147_110_2 i) _)
      colCert_147_110_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_110_4 (hp : 4 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 4 (transLenTr ⟨110, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 4 (transLenTr ⟨110, by decide⟩ 4 hp)) T147_110
      hfix147_110 hinj147_110 hcardT147_110
      (fun i => conj_mem_of_fixedPoints _ _ (T147_110 i) (hfix147_110 i) _)
      ⟨147, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 4 hp) Q2.T147_110_2 Q2.hfix147_110_2 Q2.hinj147_110_2
      Q2.hcardT147_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_110_2 i) (Q2.hfix147_110_2 i) _)
      colCert_147_110_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_110_5 (hp : 5 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 5 (transLenTr ⟨110, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 5 (transLenTr ⟨110, by decide⟩ 5 hp)) T147_110
      hfix147_110 hinj147_110 hcardT147_110
      (fun i => conj_mem_of_fixedPoints _ _ (T147_110 i) (hfix147_110 i) _)
      ⟨147, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 5 hp) Q2.T147_110_2 Q2.hfix147_110_2 Q2.hinj147_110_2
      Q2.hcardT147_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_110_2 i) (Q2.hfix147_110_2 i) _)
      colCert_147_110_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_110_10 (hp : 10 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 10 (transLenTr ⟨110, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 10 (transLenTr ⟨110, by decide⟩ 10 hp)) T147_110
      hfix147_110 hinj147_110 hcardT147_110
      (fun i => conj_mem_of_fixedPoints _ _ (T147_110 i) (hfix147_110 i) _)
      ⟨147, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 10 hp) Q2.T147_110_2 Q2.hfix147_110_2 Q2.hinj147_110_2
      Q2.hcardT147_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_110_2 i) (Q2.hfix147_110_2 i) _)
      colCert_147_110_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_110_15 (hp : 15 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 15 (transLenTr ⟨110, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 15 (transLenTr ⟨110, by decide⟩ 15 hp)) T147_110
      hfix147_110 hinj147_110 hcardT147_110
      (fun i => conj_mem_of_fixedPoints _ _ (T147_110 i) (hfix147_110 i) _)
      ⟨147, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 15 hp) Q2.T147_110_2 Q2.hfix147_110_2 Q2.hinj147_110_2
      Q2.hcardT147_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_110_2 i) (Q2.hfix147_110_2 i) _)
      colCert_147_110_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_110_20 (hp : 20 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 20 (transLenTr ⟨110, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 20 (transLenTr ⟨110, by decide⟩ 20 hp)) T147_110
      hfix147_110 hinj147_110 hcardT147_110
      (fun i => conj_mem_of_fixedPoints _ _ (T147_110 i) (hfix147_110 i) _)
      ⟨147, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 20 hp) Q2.T147_110_2 Q2.hfix147_110_2 Q2.hinj147_110_2
      Q2.hcardT147_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_110_2 i) (Q2.hfix147_110_2 i) _)
      colCert_147_110_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_110_25 (hp : 25 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 25 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 25 (transLenTr ⟨110, by decide⟩ 25 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 25 (transLenTr ⟨110, by decide⟩ 25 hp)) T147_110
      hfix147_110 hinj147_110 hcardT147_110
      (fun i => conj_mem_of_fixedPoints _ _ (T147_110 i) (hfix147_110 i) _)
      ⟨147, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 25 hp) Q2.T147_110_2 Q2.hfix147_110_2 Q2.hinj147_110_2
      Q2.hcardT147_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_110_2 i) (Q2.hfix147_110_2 i) _)
      colCert_147_110_25.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_110_50 (hp : 50 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 50 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 50 (transLenTr ⟨110, by decide⟩ 50 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 50 (transLenTr ⟨110, by decide⟩ 50 hp)) T147_110
      hfix147_110 hinj147_110 hcardT147_110
      (fun i => conj_mem_of_fixedPoints _ _ (T147_110 i) (hfix147_110 i) _)
      ⟨147, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 50 hp) Q2.T147_110_2 Q2.hfix147_110_2 Q2.hinj147_110_2
      Q2.hcardT147_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_110_2 i) (Q2.hfix147_110_2 i) _)
      colCert_147_110_50.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_110_75 (hp : 75 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 75 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 75 (transLenTr ⟨110, by decide⟩ 75 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 75 (transLenTr ⟨110, by decide⟩ 75 hp)) T147_110
      hfix147_110 hinj147_110 hcardT147_110
      (fun i => conj_mem_of_fixedPoints _ _ (T147_110 i) (hfix147_110 i) _)
      ⟨147, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 75 hp) Q2.T147_110_2 Q2.hfix147_110_2 Q2.hinj147_110_2
      Q2.hcardT147_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_110_2 i) (Q2.hfix147_110_2 i) _)
      colCert_147_110_75.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_110_100 (hp : 100 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 100 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 100 (transLenTr ⟨110, by decide⟩ 100 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 100 (transLenTr ⟨110, by decide⟩ 100 hp)) T147_110
      hfix147_110 hinj147_110 hcardT147_110
      (fun i => conj_mem_of_fixedPoints _ _ (T147_110 i) (hfix147_110 i) _)
      ⟨147, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 100 hp) Q2.T147_110_2 Q2.hfix147_110_2 Q2.hinj147_110_2
      Q2.hcardT147_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_110_2 i) (Q2.hfix147_110_2 i) _)
      colCert_147_110_100.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_111_0 (hp : 0 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 0 (transLenTr ⟨111, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 0 (transLenTr ⟨111, by decide⟩ 0 hp)) T147_111
      hfix147_111 hinj147_111 hcardT147_111
      (fun i => conj_mem_of_fixedPoints _ _ (T147_111 i) (hfix147_111 i) _)
      ⟨147, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 0 hp) Q2.T147_111_2 Q2.hfix147_111_2 Q2.hinj147_111_2
      Q2.hcardT147_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_111_2 i) (Q2.hfix147_111_2 i) _)
      colCert_147_111_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_111_1 (hp : 1 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 1 (transLenTr ⟨111, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 1 (transLenTr ⟨111, by decide⟩ 1 hp)) T147_111
      hfix147_111 hinj147_111 hcardT147_111
      (fun i => conj_mem_of_fixedPoints _ _ (T147_111 i) (hfix147_111 i) _)
      ⟨147, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 1 hp) Q2.T147_111_2 Q2.hfix147_111_2 Q2.hinj147_111_2
      Q2.hcardT147_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_111_2 i) (Q2.hfix147_111_2 i) _)
      colCert_147_111_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_111_2 (hp : 2 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 2 (transLenTr ⟨111, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 2 (transLenTr ⟨111, by decide⟩ 2 hp)) T147_111
      hfix147_111 hinj147_111 hcardT147_111
      (fun i => conj_mem_of_fixedPoints _ _ (T147_111 i) (hfix147_111 i) _)
      ⟨147, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 2 hp) Q2.T147_111_2 Q2.hfix147_111_2 Q2.hinj147_111_2
      Q2.hcardT147_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_111_2 i) (Q2.hfix147_111_2 i) _)
      colCert_147_111_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_111_3 (hp : 3 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 3 (transLenTr ⟨111, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 3 (transLenTr ⟨111, by decide⟩ 3 hp)) T147_111
      hfix147_111 hinj147_111 hcardT147_111
      (fun i => conj_mem_of_fixedPoints _ _ (T147_111 i) (hfix147_111 i) _)
      ⟨147, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 3 hp) Q2.T147_111_2 Q2.hfix147_111_2 Q2.hinj147_111_2
      Q2.hcardT147_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_111_2 i) (Q2.hfix147_111_2 i) _)
      colCert_147_111_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_111_4 (hp : 4 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 4 (transLenTr ⟨111, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 4 (transLenTr ⟨111, by decide⟩ 4 hp)) T147_111
      hfix147_111 hinj147_111 hcardT147_111
      (fun i => conj_mem_of_fixedPoints _ _ (T147_111 i) (hfix147_111 i) _)
      ⟨147, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 4 hp) Q2.T147_111_2 Q2.hfix147_111_2 Q2.hinj147_111_2
      Q2.hcardT147_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_111_2 i) (Q2.hfix147_111_2 i) _)
      colCert_147_111_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_111_5 (hp : 5 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 5 (transLenTr ⟨111, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 5 (transLenTr ⟨111, by decide⟩ 5 hp)) T147_111
      hfix147_111 hinj147_111 hcardT147_111
      (fun i => conj_mem_of_fixedPoints _ _ (T147_111 i) (hfix147_111 i) _)
      ⟨147, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 5 hp) Q2.T147_111_2 Q2.hfix147_111_2 Q2.hinj147_111_2
      Q2.hcardT147_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_111_2 i) (Q2.hfix147_111_2 i) _)
      colCert_147_111_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_111_10 (hp : 10 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 10 (transLenTr ⟨111, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 10 (transLenTr ⟨111, by decide⟩ 10 hp)) T147_111
      hfix147_111 hinj147_111 hcardT147_111
      (fun i => conj_mem_of_fixedPoints _ _ (T147_111 i) (hfix147_111 i) _)
      ⟨147, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 10 hp) Q2.T147_111_2 Q2.hfix147_111_2 Q2.hinj147_111_2
      Q2.hcardT147_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_111_2 i) (Q2.hfix147_111_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨111, by decide⟩ 10 (transLenTr ⟨111, by decide⟩ 10 hp) : ↥(reps ⟨111, by decide⟩)) : Coordinate 1)
        T147_111 = colFn colCertDiv_147_111_10.D1 (m := 1) from colCertDiv_147_111_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨111, by decide⟩ 10 hp : ↥(Q2.reps ⟨111, by decide⟩)) : Coordinate 2)
        Q2.T147_111_2 = colFn colCertDiv_147_111_10.D2 (m := 1) from colCertDiv_147_111_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_111_10_match


theorem leaf_147_111_15 (hp : 15 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 15 (transLenTr ⟨111, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 15 (transLenTr ⟨111, by decide⟩ 15 hp)) T147_111
      hfix147_111 hinj147_111 hcardT147_111
      (fun i => conj_mem_of_fixedPoints _ _ (T147_111 i) (hfix147_111 i) _)
      ⟨147, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 15 hp) Q2.T147_111_2 Q2.hfix147_111_2 Q2.hinj147_111_2
      Q2.hcardT147_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_111_2 i) (Q2.hfix147_111_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨111, by decide⟩ 15 (transLenTr ⟨111, by decide⟩ 15 hp) : ↥(reps ⟨111, by decide⟩)) : Coordinate 1)
        T147_111 = colFn colCertDiv_147_111_15.D1 (m := 1) from colCertDiv_147_111_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨111, by decide⟩ 15 hp : ↥(Q2.reps ⟨111, by decide⟩)) : Coordinate 2)
        Q2.T147_111_2 = colFn colCertDiv_147_111_15.D2 (m := 1) from colCertDiv_147_111_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_111_15_match


theorem leaf_147_111_20 (hp : 20 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 20 (transLenTr ⟨111, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 20 (transLenTr ⟨111, by decide⟩ 20 hp)) T147_111
      hfix147_111 hinj147_111 hcardT147_111
      (fun i => conj_mem_of_fixedPoints _ _ (T147_111 i) (hfix147_111 i) _)
      ⟨147, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 20 hp) Q2.T147_111_2 Q2.hfix147_111_2 Q2.hinj147_111_2
      Q2.hcardT147_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_111_2 i) (Q2.hfix147_111_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨111, by decide⟩ 20 (transLenTr ⟨111, by decide⟩ 20 hp) : ↥(reps ⟨111, by decide⟩)) : Coordinate 1)
        T147_111 = colFn colCertDiv_147_111_20.D1 (m := 1) from colCertDiv_147_111_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨111, by decide⟩ 20 hp : ↥(Q2.reps ⟨111, by decide⟩)) : Coordinate 2)
        Q2.T147_111_2 = colFn colCertDiv_147_111_20.D2 (m := 1) from colCertDiv_147_111_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_111_20_match


theorem leaf_147_112_0 (hp : 0 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 0 (transLenTr ⟨112, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 0 (transLenTr ⟨112, by decide⟩ 0 hp)) T147_112
      hfix147_112 hinj147_112 hcardT147_112
      (fun i => conj_mem_of_fixedPoints _ _ (T147_112 i) (hfix147_112 i) _)
      ⟨147, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 0 hp) Q2.T147_112_2 Q2.hfix147_112_2 Q2.hinj147_112_2
      Q2.hcardT147_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_112_2 i) (Q2.hfix147_112_2 i) _)
      colCert_147_112_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_112_1 (hp : 1 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 1 (transLenTr ⟨112, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 1 (transLenTr ⟨112, by decide⟩ 1 hp)) T147_112
      hfix147_112 hinj147_112 hcardT147_112
      (fun i => conj_mem_of_fixedPoints _ _ (T147_112 i) (hfix147_112 i) _)
      ⟨147, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 1 hp) Q2.T147_112_2 Q2.hfix147_112_2 Q2.hinj147_112_2
      Q2.hcardT147_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_112_2 i) (Q2.hfix147_112_2 i) _)
      colCert_147_112_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_112_2 (hp : 2 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 2 (transLenTr ⟨112, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 2 (transLenTr ⟨112, by decide⟩ 2 hp)) T147_112
      hfix147_112 hinj147_112 hcardT147_112
      (fun i => conj_mem_of_fixedPoints _ _ (T147_112 i) (hfix147_112 i) _)
      ⟨147, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 2 hp) Q2.T147_112_2 Q2.hfix147_112_2 Q2.hinj147_112_2
      Q2.hcardT147_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_112_2 i) (Q2.hfix147_112_2 i) _)
      colCert_147_112_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_112_3 (hp : 3 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 3 (transLenTr ⟨112, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 3 (transLenTr ⟨112, by decide⟩ 3 hp)) T147_112
      hfix147_112 hinj147_112 hcardT147_112
      (fun i => conj_mem_of_fixedPoints _ _ (T147_112 i) (hfix147_112 i) _)
      ⟨147, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 3 hp) Q2.T147_112_2 Q2.hfix147_112_2 Q2.hinj147_112_2
      Q2.hcardT147_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_112_2 i) (Q2.hfix147_112_2 i) _)
      colCert_147_112_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_112_4 (hp : 4 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 4 (transLenTr ⟨112, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 4 (transLenTr ⟨112, by decide⟩ 4 hp)) T147_112
      hfix147_112 hinj147_112 hcardT147_112
      (fun i => conj_mem_of_fixedPoints _ _ (T147_112 i) (hfix147_112 i) _)
      ⟨147, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 4 hp) Q2.T147_112_2 Q2.hfix147_112_2 Q2.hinj147_112_2
      Q2.hcardT147_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_112_2 i) (Q2.hfix147_112_2 i) _)
      colCert_147_112_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_112_5 (hp : 5 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 5 (transLenTr ⟨112, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 5 (transLenTr ⟨112, by decide⟩ 5 hp)) T147_112
      hfix147_112 hinj147_112 hcardT147_112
      (fun i => conj_mem_of_fixedPoints _ _ (T147_112 i) (hfix147_112 i) _)
      ⟨147, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 5 hp) Q2.T147_112_2 Q2.hfix147_112_2 Q2.hinj147_112_2
      Q2.hcardT147_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_112_2 i) (Q2.hfix147_112_2 i) _)
      colCert_147_112_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_112_10 (hp : 10 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 10 (transLenTr ⟨112, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 10 (transLenTr ⟨112, by decide⟩ 10 hp)) T147_112
      hfix147_112 hinj147_112 hcardT147_112
      (fun i => conj_mem_of_fixedPoints _ _ (T147_112 i) (hfix147_112 i) _)
      ⟨147, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 10 hp) Q2.T147_112_2 Q2.hfix147_112_2 Q2.hinj147_112_2
      Q2.hcardT147_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_112_2 i) (Q2.hfix147_112_2 i) _)
      colCert_147_112_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_112_15 (hp : 15 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 15 (transLenTr ⟨112, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 15 (transLenTr ⟨112, by decide⟩ 15 hp)) T147_112
      hfix147_112 hinj147_112 hcardT147_112
      (fun i => conj_mem_of_fixedPoints _ _ (T147_112 i) (hfix147_112 i) _)
      ⟨147, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 15 hp) Q2.T147_112_2 Q2.hfix147_112_2 Q2.hinj147_112_2
      Q2.hcardT147_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_112_2 i) (Q2.hfix147_112_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨112, by decide⟩ 15 (transLenTr ⟨112, by decide⟩ 15 hp) : ↥(reps ⟨112, by decide⟩)) : Coordinate 1)
        T147_112 = colFn colCertDiv_147_112_15.D1 (m := 1) from colCertDiv_147_112_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨112, by decide⟩ 15 hp : ↥(Q2.reps ⟨112, by decide⟩)) : Coordinate 2)
        Q2.T147_112_2 = colFn colCertDiv_147_112_15.D2 (m := 1) from colCertDiv_147_112_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_112_15_match


theorem leaf_147_112_20 (hp : 20 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 20 (transLenTr ⟨112, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 20 (transLenTr ⟨112, by decide⟩ 20 hp)) T147_112
      hfix147_112 hinj147_112 hcardT147_112
      (fun i => conj_mem_of_fixedPoints _ _ (T147_112 i) (hfix147_112 i) _)
      ⟨147, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 20 hp) Q2.T147_112_2 Q2.hfix147_112_2 Q2.hinj147_112_2
      Q2.hcardT147_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_112_2 i) (Q2.hfix147_112_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨112, by decide⟩ 20 (transLenTr ⟨112, by decide⟩ 20 hp) : ↥(reps ⟨112, by decide⟩)) : Coordinate 1)
        T147_112 = colFn colCertDiv_147_112_20.D1 (m := 1) from colCertDiv_147_112_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨112, by decide⟩ 20 hp : ↥(Q2.reps ⟨112, by decide⟩)) : Coordinate 2)
        Q2.T147_112_2 = colFn colCertDiv_147_112_20.D2 (m := 1) from colCertDiv_147_112_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_112_20_match


theorem leaf_147_113_0 (hp : 0 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 0 (transLenTr ⟨113, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 0 (transLenTr ⟨113, by decide⟩ 0 hp)) T147_113
      hfix147_113 hinj147_113 hcardT147_113
      (fun i => conj_mem_of_fixedPoints _ _ (T147_113 i) (hfix147_113 i) _)
      ⟨147, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 0 hp) Q2.T147_113_2 Q2.hfix147_113_2 Q2.hinj147_113_2
      Q2.hcardT147_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_113_2 i) (Q2.hfix147_113_2 i) _)
      colCert_147_113_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_113_1 (hp : 1 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 1 (transLenTr ⟨113, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 1 (transLenTr ⟨113, by decide⟩ 1 hp)) T147_113
      hfix147_113 hinj147_113 hcardT147_113
      (fun i => conj_mem_of_fixedPoints _ _ (T147_113 i) (hfix147_113 i) _)
      ⟨147, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 1 hp) Q2.T147_113_2 Q2.hfix147_113_2 Q2.hinj147_113_2
      Q2.hcardT147_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_113_2 i) (Q2.hfix147_113_2 i) _)
      colCert_147_113_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_113_2 (hp : 2 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 2 (transLenTr ⟨113, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 2 (transLenTr ⟨113, by decide⟩ 2 hp)) T147_113
      hfix147_113 hinj147_113 hcardT147_113
      (fun i => conj_mem_of_fixedPoints _ _ (T147_113 i) (hfix147_113 i) _)
      ⟨147, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 2 hp) Q2.T147_113_2 Q2.hfix147_113_2 Q2.hinj147_113_2
      Q2.hcardT147_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_113_2 i) (Q2.hfix147_113_2 i) _)
      colCert_147_113_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_113_3 (hp : 3 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 3 (transLenTr ⟨113, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 3 (transLenTr ⟨113, by decide⟩ 3 hp)) T147_113
      hfix147_113 hinj147_113 hcardT147_113
      (fun i => conj_mem_of_fixedPoints _ _ (T147_113 i) (hfix147_113 i) _)
      ⟨147, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 3 hp) Q2.T147_113_2 Q2.hfix147_113_2 Q2.hinj147_113_2
      Q2.hcardT147_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_113_2 i) (Q2.hfix147_113_2 i) _)
      colCert_147_113_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_113_4 (hp : 4 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 4 (transLenTr ⟨113, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 4 (transLenTr ⟨113, by decide⟩ 4 hp)) T147_113
      hfix147_113 hinj147_113 hcardT147_113
      (fun i => conj_mem_of_fixedPoints _ _ (T147_113 i) (hfix147_113 i) _)
      ⟨147, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 4 hp) Q2.T147_113_2 Q2.hfix147_113_2 Q2.hinj147_113_2
      Q2.hcardT147_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_113_2 i) (Q2.hfix147_113_2 i) _)
      colCert_147_113_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_113_5 (hp : 5 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 5 (transLenTr ⟨113, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 5 (transLenTr ⟨113, by decide⟩ 5 hp)) T147_113
      hfix147_113 hinj147_113 hcardT147_113
      (fun i => conj_mem_of_fixedPoints _ _ (T147_113 i) (hfix147_113 i) _)
      ⟨147, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 5 hp) Q2.T147_113_2 Q2.hfix147_113_2 Q2.hinj147_113_2
      Q2.hcardT147_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_113_2 i) (Q2.hfix147_113_2 i) _)
      colCert_147_113_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_113_10 (hp : 10 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 10 (transLenTr ⟨113, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 10 (transLenTr ⟨113, by decide⟩ 10 hp)) T147_113
      hfix147_113 hinj147_113 hcardT147_113
      (fun i => conj_mem_of_fixedPoints _ _ (T147_113 i) (hfix147_113 i) _)
      ⟨147, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 10 hp) Q2.T147_113_2 Q2.hfix147_113_2 Q2.hinj147_113_2
      Q2.hcardT147_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_113_2 i) (Q2.hfix147_113_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨113, by decide⟩ 10 (transLenTr ⟨113, by decide⟩ 10 hp) : ↥(reps ⟨113, by decide⟩)) : Coordinate 1)
        T147_113 = colFn colCertDiv_147_113_10.D1 (m := 1) from colCertDiv_147_113_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨113, by decide⟩ 10 hp : ↥(Q2.reps ⟨113, by decide⟩)) : Coordinate 2)
        Q2.T147_113_2 = colFn colCertDiv_147_113_10.D2 (m := 1) from colCertDiv_147_113_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_113_10_match


theorem leaf_147_113_15 (hp : 15 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 15 (transLenTr ⟨113, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 15 (transLenTr ⟨113, by decide⟩ 15 hp)) T147_113
      hfix147_113 hinj147_113 hcardT147_113
      (fun i => conj_mem_of_fixedPoints _ _ (T147_113 i) (hfix147_113 i) _)
      ⟨147, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 15 hp) Q2.T147_113_2 Q2.hfix147_113_2 Q2.hinj147_113_2
      Q2.hcardT147_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_113_2 i) (Q2.hfix147_113_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨113, by decide⟩ 15 (transLenTr ⟨113, by decide⟩ 15 hp) : ↥(reps ⟨113, by decide⟩)) : Coordinate 1)
        T147_113 = colFn colCertDiv_147_113_15.D1 (m := 1) from colCertDiv_147_113_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨113, by decide⟩ 15 hp : ↥(Q2.reps ⟨113, by decide⟩)) : Coordinate 2)
        Q2.T147_113_2 = colFn colCertDiv_147_113_15.D2 (m := 1) from colCertDiv_147_113_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_113_15_match


theorem leaf_147_113_20 (hp : 20 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 20 (transLenTr ⟨113, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 20 (transLenTr ⟨113, by decide⟩ 20 hp)) T147_113
      hfix147_113 hinj147_113 hcardT147_113
      (fun i => conj_mem_of_fixedPoints _ _ (T147_113 i) (hfix147_113 i) _)
      ⟨147, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 20 hp) Q2.T147_113_2 Q2.hfix147_113_2 Q2.hinj147_113_2
      Q2.hcardT147_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_113_2 i) (Q2.hfix147_113_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨113, by decide⟩ 20 (transLenTr ⟨113, by decide⟩ 20 hp) : ↥(reps ⟨113, by decide⟩)) : Coordinate 1)
        T147_113 = colFn colCertDiv_147_113_20.D1 (m := 1) from colCertDiv_147_113_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨113, by decide⟩ 20 hp : ↥(Q2.reps ⟨113, by decide⟩)) : Coordinate 2)
        Q2.T147_113_2 = colFn colCertDiv_147_113_20.D2 (m := 1) from colCertDiv_147_113_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_113_20_match


theorem leaf_147_114_0 (hp : 0 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 0 (transLenTr ⟨114, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 0 (transLenTr ⟨114, by decide⟩ 0 hp)) T147_114
      hfix147_114 hinj147_114 hcardT147_114
      (fun i => conj_mem_of_fixedPoints _ _ (T147_114 i) (hfix147_114 i) _)
      ⟨147, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 0 hp) Q2.T147_114_2 Q2.hfix147_114_2 Q2.hinj147_114_2
      Q2.hcardT147_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_114_2 i) (Q2.hfix147_114_2 i) _)
      colCert_147_114_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_114_1 (hp : 1 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 1 (transLenTr ⟨114, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 1 (transLenTr ⟨114, by decide⟩ 1 hp)) T147_114
      hfix147_114 hinj147_114 hcardT147_114
      (fun i => conj_mem_of_fixedPoints _ _ (T147_114 i) (hfix147_114 i) _)
      ⟨147, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 1 hp) Q2.T147_114_2 Q2.hfix147_114_2 Q2.hinj147_114_2
      Q2.hcardT147_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_114_2 i) (Q2.hfix147_114_2 i) _)
      colCert_147_114_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_114_2 (hp : 2 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 2 (transLenTr ⟨114, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 2 (transLenTr ⟨114, by decide⟩ 2 hp)) T147_114
      hfix147_114 hinj147_114 hcardT147_114
      (fun i => conj_mem_of_fixedPoints _ _ (T147_114 i) (hfix147_114 i) _)
      ⟨147, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 2 hp) Q2.T147_114_2 Q2.hfix147_114_2 Q2.hinj147_114_2
      Q2.hcardT147_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_114_2 i) (Q2.hfix147_114_2 i) _)
      colCert_147_114_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_114_3 (hp : 3 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 3 (transLenTr ⟨114, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 3 (transLenTr ⟨114, by decide⟩ 3 hp)) T147_114
      hfix147_114 hinj147_114 hcardT147_114
      (fun i => conj_mem_of_fixedPoints _ _ (T147_114 i) (hfix147_114 i) _)
      ⟨147, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 3 hp) Q2.T147_114_2 Q2.hfix147_114_2 Q2.hinj147_114_2
      Q2.hcardT147_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_114_2 i) (Q2.hfix147_114_2 i) _)
      colCert_147_114_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_114_4 (hp : 4 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 4 (transLenTr ⟨114, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 4 (transLenTr ⟨114, by decide⟩ 4 hp)) T147_114
      hfix147_114 hinj147_114 hcardT147_114
      (fun i => conj_mem_of_fixedPoints _ _ (T147_114 i) (hfix147_114 i) _)
      ⟨147, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 4 hp) Q2.T147_114_2 Q2.hfix147_114_2 Q2.hinj147_114_2
      Q2.hcardT147_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_114_2 i) (Q2.hfix147_114_2 i) _)
      colCert_147_114_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_114_5 (hp : 5 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 5 (transLenTr ⟨114, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 5 (transLenTr ⟨114, by decide⟩ 5 hp)) T147_114
      hfix147_114 hinj147_114 hcardT147_114
      (fun i => conj_mem_of_fixedPoints _ _ (T147_114 i) (hfix147_114 i) _)
      ⟨147, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 5 hp) Q2.T147_114_2 Q2.hfix147_114_2 Q2.hinj147_114_2
      Q2.hcardT147_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_114_2 i) (Q2.hfix147_114_2 i) _)
      colCert_147_114_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_114_10 (hp : 10 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 10 (transLenTr ⟨114, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 10 (transLenTr ⟨114, by decide⟩ 10 hp)) T147_114
      hfix147_114 hinj147_114 hcardT147_114
      (fun i => conj_mem_of_fixedPoints _ _ (T147_114 i) (hfix147_114 i) _)
      ⟨147, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 10 hp) Q2.T147_114_2 Q2.hfix147_114_2 Q2.hinj147_114_2
      Q2.hcardT147_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_114_2 i) (Q2.hfix147_114_2 i) _)
      colCert_147_114_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_114_15 (hp : 15 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 15 (transLenTr ⟨114, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 15 (transLenTr ⟨114, by decide⟩ 15 hp)) T147_114
      hfix147_114 hinj147_114 hcardT147_114
      (fun i => conj_mem_of_fixedPoints _ _ (T147_114 i) (hfix147_114 i) _)
      ⟨147, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 15 hp) Q2.T147_114_2 Q2.hfix147_114_2 Q2.hinj147_114_2
      Q2.hcardT147_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_114_2 i) (Q2.hfix147_114_2 i) _)
      colCert_147_114_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_114_20 (hp : 20 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 20 (transLenTr ⟨114, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 20 (transLenTr ⟨114, by decide⟩ 20 hp)) T147_114
      hfix147_114 hinj147_114 hcardT147_114
      (fun i => conj_mem_of_fixedPoints _ _ (T147_114 i) (hfix147_114 i) _)
      ⟨147, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 20 hp) Q2.T147_114_2 Q2.hfix147_114_2 Q2.hinj147_114_2
      Q2.hcardT147_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_114_2 i) (Q2.hfix147_114_2 i) _)
      colCert_147_114_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_115_0 (hp : 0 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 0 (transLenTr ⟨115, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 0 (transLenTr ⟨115, by decide⟩ 0 hp)) T147_115
      hfix147_115 hinj147_115 hcardT147_115
      (fun i => conj_mem_of_fixedPoints _ _ (T147_115 i) (hfix147_115 i) _)
      ⟨147, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 0 hp) Q2.T147_115_2 Q2.hfix147_115_2 Q2.hinj147_115_2
      Q2.hcardT147_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_115_2 i) (Q2.hfix147_115_2 i) _)
      colCert_147_115_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_115_1 (hp : 1 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 1 (transLenTr ⟨115, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 1 (transLenTr ⟨115, by decide⟩ 1 hp)) T147_115
      hfix147_115 hinj147_115 hcardT147_115
      (fun i => conj_mem_of_fixedPoints _ _ (T147_115 i) (hfix147_115 i) _)
      ⟨147, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 1 hp) Q2.T147_115_2 Q2.hfix147_115_2 Q2.hinj147_115_2
      Q2.hcardT147_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_115_2 i) (Q2.hfix147_115_2 i) _)
      colCert_147_115_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_115_2 (hp : 2 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 2 (transLenTr ⟨115, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 2 (transLenTr ⟨115, by decide⟩ 2 hp)) T147_115
      hfix147_115 hinj147_115 hcardT147_115
      (fun i => conj_mem_of_fixedPoints _ _ (T147_115 i) (hfix147_115 i) _)
      ⟨147, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 2 hp) Q2.T147_115_2 Q2.hfix147_115_2 Q2.hinj147_115_2
      Q2.hcardT147_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_115_2 i) (Q2.hfix147_115_2 i) _)
      colCert_147_115_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_115_3 (hp : 3 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 3 (transLenTr ⟨115, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 3 (transLenTr ⟨115, by decide⟩ 3 hp)) T147_115
      hfix147_115 hinj147_115 hcardT147_115
      (fun i => conj_mem_of_fixedPoints _ _ (T147_115 i) (hfix147_115 i) _)
      ⟨147, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 3 hp) Q2.T147_115_2 Q2.hfix147_115_2 Q2.hinj147_115_2
      Q2.hcardT147_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_115_2 i) (Q2.hfix147_115_2 i) _)
      colCert_147_115_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_115_4 (hp : 4 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 4 (transLenTr ⟨115, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 4 (transLenTr ⟨115, by decide⟩ 4 hp)) T147_115
      hfix147_115 hinj147_115 hcardT147_115
      (fun i => conj_mem_of_fixedPoints _ _ (T147_115 i) (hfix147_115 i) _)
      ⟨147, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 4 hp) Q2.T147_115_2 Q2.hfix147_115_2 Q2.hinj147_115_2
      Q2.hcardT147_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_115_2 i) (Q2.hfix147_115_2 i) _)
      colCert_147_115_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_115_5 (hp : 5 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 5 (transLenTr ⟨115, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 5 (transLenTr ⟨115, by decide⟩ 5 hp)) T147_115
      hfix147_115 hinj147_115 hcardT147_115
      (fun i => conj_mem_of_fixedPoints _ _ (T147_115 i) (hfix147_115 i) _)
      ⟨147, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 5 hp) Q2.T147_115_2 Q2.hfix147_115_2 Q2.hinj147_115_2
      Q2.hcardT147_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_115_2 i) (Q2.hfix147_115_2 i) _)
      colCert_147_115_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_115_10 (hp : 10 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 10 (transLenTr ⟨115, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 10 (transLenTr ⟨115, by decide⟩ 10 hp)) T147_115
      hfix147_115 hinj147_115 hcardT147_115
      (fun i => conj_mem_of_fixedPoints _ _ (T147_115 i) (hfix147_115 i) _)
      ⟨147, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 10 hp) Q2.T147_115_2 Q2.hfix147_115_2 Q2.hinj147_115_2
      Q2.hcardT147_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_115_2 i) (Q2.hfix147_115_2 i) _)
      colCert_147_115_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_115_15 (hp : 15 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 15 (transLenTr ⟨115, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 15 (transLenTr ⟨115, by decide⟩ 15 hp)) T147_115
      hfix147_115 hinj147_115 hcardT147_115
      (fun i => conj_mem_of_fixedPoints _ _ (T147_115 i) (hfix147_115 i) _)
      ⟨147, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 15 hp) Q2.T147_115_2 Q2.hfix147_115_2 Q2.hinj147_115_2
      Q2.hcardT147_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_115_2 i) (Q2.hfix147_115_2 i) _)
      colCert_147_115_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_115_20 (hp : 20 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 20 (transLenTr ⟨115, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 20 (transLenTr ⟨115, by decide⟩ 20 hp)) T147_115
      hfix147_115 hinj147_115 hcardT147_115
      (fun i => conj_mem_of_fixedPoints _ _ (T147_115 i) (hfix147_115 i) _)
      ⟨147, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 20 hp) Q2.T147_115_2 Q2.hfix147_115_2 Q2.hinj147_115_2
      Q2.hcardT147_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_115_2 i) (Q2.hfix147_115_2 i) _)
      colCert_147_115_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_0 (hp : 0 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 0 (transLenTr ⟨116, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 0 (transLenTr ⟨116, by decide⟩ 0 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 0 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_1 (hp : 1 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 1 (transLenTr ⟨116, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 1 (transLenTr ⟨116, by decide⟩ 1 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 1 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_2 (hp : 2 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 2 (transLenTr ⟨116, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 2 (transLenTr ⟨116, by decide⟩ 2 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 2 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_3 (hp : 3 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 3 (transLenTr ⟨116, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 3 (transLenTr ⟨116, by decide⟩ 3 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 3 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_4 (hp : 4 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 4 (transLenTr ⟨116, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 4 (transLenTr ⟨116, by decide⟩ 4 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 4 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_5 (hp : 5 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 5 (transLenTr ⟨116, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 5 (transLenTr ⟨116, by decide⟩ 5 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 5 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_6 (hp : 6 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 6 (transLenTr ⟨116, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 6 (transLenTr ⟨116, by decide⟩ 6 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 6 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_7 (hp : 7 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 7 (transLenTr ⟨116, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 7 (transLenTr ⟨116, by decide⟩ 7 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 7 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_8 (hp : 8 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 8 (transLenTr ⟨116, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 8 (transLenTr ⟨116, by decide⟩ 8 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 8 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_9 (hp : 9 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 9 (transLenTr ⟨116, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 9 (transLenTr ⟨116, by decide⟩ 9 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 9 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_10 (hp : 10 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 10 (transLenTr ⟨116, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 10 (transLenTr ⟨116, by decide⟩ 10 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 10 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_11 (hp : 11 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 11 (transLenTr ⟨116, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 11 (transLenTr ⟨116, by decide⟩ 11 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 11 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_12 (hp : 12 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 12 (transLenTr ⟨116, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 12 (transLenTr ⟨116, by decide⟩ 12 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 12 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_13 (hp : 13 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 13 (transLenTr ⟨116, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 13 (transLenTr ⟨116, by decide⟩ 13 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 13 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_14 (hp : 14 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 14 (transLenTr ⟨116, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 14 (transLenTr ⟨116, by decide⟩ 14 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 14 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_15 (hp : 15 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 15 (transLenTr ⟨116, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 15 (transLenTr ⟨116, by decide⟩ 15 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 15 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_16 (hp : 16 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 16 (transLenTr ⟨116, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 16 (transLenTr ⟨116, by decide⟩ 16 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 16 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_17 (hp : 17 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 17 (transLenTr ⟨116, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 17 (transLenTr ⟨116, by decide⟩ 17 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 17 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_18 (hp : 18 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 18 (transLenTr ⟨116, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 18 (transLenTr ⟨116, by decide⟩ 18 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 18 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_19 (hp : 19 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 19 (transLenTr ⟨116, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 19 (transLenTr ⟨116, by decide⟩ 19 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 19 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_20 (hp : 20 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 20 (transLenTr ⟨116, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 20 (transLenTr ⟨116, by decide⟩ 20 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 20 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_21 (hp : 21 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 21 (transLenTr ⟨116, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 21 (transLenTr ⟨116, by decide⟩ 21 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 21 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_22 (hp : 22 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 22 (transLenTr ⟨116, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 22 (transLenTr ⟨116, by decide⟩ 22 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 22 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_23 (hp : 23 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 23 (transLenTr ⟨116, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 23 (transLenTr ⟨116, by decide⟩ 23 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 23 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_24 (hp : 24 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 24 (transLenTr ⟨116, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 24 (transLenTr ⟨116, by decide⟩ 24 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 24 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_25 (hp : 25 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 25 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 25 (transLenTr ⟨116, by decide⟩ 25 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 25 (transLenTr ⟨116, by decide⟩ 25 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 25 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_25.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_30 (hp : 30 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 30 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 30 (transLenTr ⟨116, by decide⟩ 30 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 30 (transLenTr ⟨116, by decide⟩ 30 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 30 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_30.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_35 (hp : 35 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 35 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 35 (transLenTr ⟨116, by decide⟩ 35 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 35 (transLenTr ⟨116, by decide⟩ 35 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 35 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_35.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_40 (hp : 40 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 40 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 40 (transLenTr ⟨116, by decide⟩ 40 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 40 (transLenTr ⟨116, by decide⟩ 40 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 40 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_40.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_45 (hp : 45 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 45 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 45 (transLenTr ⟨116, by decide⟩ 45 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 45 (transLenTr ⟨116, by decide⟩ 45 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 45 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_45.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_50 (hp : 50 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 50 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 50 (transLenTr ⟨116, by decide⟩ 50 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 50 (transLenTr ⟨116, by decide⟩ 50 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 50 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_50.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_55 (hp : 55 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 55 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 55 (transLenTr ⟨116, by decide⟩ 55 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 55 (transLenTr ⟨116, by decide⟩ 55 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 55 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_55.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_60 (hp : 60 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 60 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 60 (transLenTr ⟨116, by decide⟩ 60 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 60 (transLenTr ⟨116, by decide⟩ 60 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 60 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_60.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_65 (hp : 65 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 65 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 65 (transLenTr ⟨116, by decide⟩ 65 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 65 (transLenTr ⟨116, by decide⟩ 65 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 65 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_65.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_70 (hp : 70 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 70 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 70 (transLenTr ⟨116, by decide⟩ 70 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 70 (transLenTr ⟨116, by decide⟩ 70 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 70 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_70.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_75 (hp : 75 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 75 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 75 (transLenTr ⟨116, by decide⟩ 75 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 75 (transLenTr ⟨116, by decide⟩ 75 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 75 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_75.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_80 (hp : 80 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 80 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 80 (transLenTr ⟨116, by decide⟩ 80 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 80 (transLenTr ⟨116, by decide⟩ 80 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 80 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_80.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_85 (hp : 85 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 85 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 85 (transLenTr ⟨116, by decide⟩ 85 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 85 (transLenTr ⟨116, by decide⟩ 85 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 85 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_85.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_90 (hp : 90 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 90 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 90 (transLenTr ⟨116, by decide⟩ 90 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 90 (transLenTr ⟨116, by decide⟩ 90 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 90 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_90.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_95 (hp : 95 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 95 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 95 (transLenTr ⟨116, by decide⟩ 95 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 95 (transLenTr ⟨116, by decide⟩ 95 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 95 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_95.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_100 (hp : 100 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 100 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 100 (transLenTr ⟨116, by decide⟩ 100 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 100 (transLenTr ⟨116, by decide⟩ 100 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 100 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_100.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_105 (hp : 105 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 105 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 105 (transLenTr ⟨116, by decide⟩ 105 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 105 (transLenTr ⟨116, by decide⟩ 105 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 105 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_105.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_110 (hp : 110 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 110 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 110 (transLenTr ⟨116, by decide⟩ 110 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 110 (transLenTr ⟨116, by decide⟩ 110 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 110 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_110.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_115 (hp : 115 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 115 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 115 (transLenTr ⟨116, by decide⟩ 115 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 115 (transLenTr ⟨116, by decide⟩ 115 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 115 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_115.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_116_120 (hp : 120 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 120 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 120 (transLenTr ⟨116, by decide⟩ 120 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 120 (transLenTr ⟨116, by decide⟩ 120 hp)) T147_116
      hfix147_116 hinj147_116 hcardT147_116
      (fun i => conj_mem_of_fixedPoints _ _ (T147_116 i) (hfix147_116 i) _)
      ⟨147, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 120 hp) Q2.T147_116_2 Q2.hfix147_116_2 Q2.hinj147_116_2
      Q2.hcardT147_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_116_2 i) (Q2.hfix147_116_2 i) _)
      colCert_147_116_120.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_0 (hp : 0 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 0 (transLenTr ⟨117, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 0 (transLenTr ⟨117, by decide⟩ 0 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 0 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_1 (hp : 1 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 1 (transLenTr ⟨117, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 1 (transLenTr ⟨117, by decide⟩ 1 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 1 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_2 (hp : 2 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 2 (transLenTr ⟨117, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 2 (transLenTr ⟨117, by decide⟩ 2 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 2 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_3 (hp : 3 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 3 (transLenTr ⟨117, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 3 (transLenTr ⟨117, by decide⟩ 3 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 3 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_4 (hp : 4 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 4 (transLenTr ⟨117, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 4 (transLenTr ⟨117, by decide⟩ 4 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 4 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_5 (hp : 5 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 5 (transLenTr ⟨117, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 5 (transLenTr ⟨117, by decide⟩ 5 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 5 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_6 (hp : 6 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 6 (transLenTr ⟨117, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 6 (transLenTr ⟨117, by decide⟩ 6 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 6 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_7 (hp : 7 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 7 (transLenTr ⟨117, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 7 (transLenTr ⟨117, by decide⟩ 7 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 7 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_8 (hp : 8 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 8 (transLenTr ⟨117, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 8 (transLenTr ⟨117, by decide⟩ 8 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 8 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_9 (hp : 9 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 9 (transLenTr ⟨117, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 9 (transLenTr ⟨117, by decide⟩ 9 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 9 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_10 (hp : 10 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 10 (transLenTr ⟨117, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 10 (transLenTr ⟨117, by decide⟩ 10 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 10 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_11 (hp : 11 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 11 (transLenTr ⟨117, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 11 (transLenTr ⟨117, by decide⟩ 11 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 11 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_12 (hp : 12 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 12 (transLenTr ⟨117, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 12 (transLenTr ⟨117, by decide⟩ 12 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 12 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_13 (hp : 13 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 13 (transLenTr ⟨117, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 13 (transLenTr ⟨117, by decide⟩ 13 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 13 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_14 (hp : 14 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 14 (transLenTr ⟨117, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 14 (transLenTr ⟨117, by decide⟩ 14 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 14 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_15 (hp : 15 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 15 (transLenTr ⟨117, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 15 (transLenTr ⟨117, by decide⟩ 15 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 15 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_16 (hp : 16 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 16 (transLenTr ⟨117, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 16 (transLenTr ⟨117, by decide⟩ 16 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 16 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_17 (hp : 17 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 17 (transLenTr ⟨117, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 17 (transLenTr ⟨117, by decide⟩ 17 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 17 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_18 (hp : 18 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 18 (transLenTr ⟨117, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 18 (transLenTr ⟨117, by decide⟩ 18 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 18 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_19 (hp : 19 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 19 (transLenTr ⟨117, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 19 (transLenTr ⟨117, by decide⟩ 19 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 19 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_20 (hp : 20 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 20 (transLenTr ⟨117, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 20 (transLenTr ⟨117, by decide⟩ 20 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 20 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_21 (hp : 21 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 21 (transLenTr ⟨117, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 21 (transLenTr ⟨117, by decide⟩ 21 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 21 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_21.hD ?_).symm
  rw [alnId_147 j hj]


end LeanDring.P5Presentation
