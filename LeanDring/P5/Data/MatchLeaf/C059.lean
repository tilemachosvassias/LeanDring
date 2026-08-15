/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C037
import LeanDring.P5.Data.ColRestCheap.C135
import LeanDring.P5.Data.ColRestCheap.C136
import LeanDring.P5.Data.ColRestCheap.C137
import LeanDring.P5.Data.ColRestCheap.C138
import LeanDring.P5.Data.EntryK.C044
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C043

/-! # Stage-5 leaves, chunk 58 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_147_143_22 (hp : 22 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 22 (transLenTr ⟨143, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 22 (transLenTr ⟨143, by decide⟩ 22 hp)) T147_143
      hfix147_143 hinj147_143 hcardT147_143
      (fun i => conj_mem_of_fixedPoints _ _ (T147_143 i) (hfix147_143 i) _)
      ⟨147, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 22 hp) Q2.T147_143_2 Q2.hfix147_143_2 Q2.hinj147_143_2
      Q2.hcardT147_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_143_2 i) (Q2.hfix147_143_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨143, by decide⟩ 22 (transLenTr ⟨143, by decide⟩ 22 hp) : ↥(reps ⟨143, by decide⟩)) : Coordinate 1)
        T147_143 = colFn colCertDiv_147_143_22.D1 (m := 1) from colCertDiv_147_143_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨143, by decide⟩ 22 hp : ↥(Q2.reps ⟨143, by decide⟩)) : Coordinate 2)
        Q2.T147_143_2 = colFn colCertDiv_147_143_22.D2 (m := 1) from colCertDiv_147_143_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_143_22_match


theorem leaf_147_143_23 (hp : 23 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 23 (transLenTr ⟨143, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 23 (transLenTr ⟨143, by decide⟩ 23 hp)) T147_143
      hfix147_143 hinj147_143 hcardT147_143
      (fun i => conj_mem_of_fixedPoints _ _ (T147_143 i) (hfix147_143 i) _)
      ⟨147, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 23 hp) Q2.T147_143_2 Q2.hfix147_143_2 Q2.hinj147_143_2
      Q2.hcardT147_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_143_2 i) (Q2.hfix147_143_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨143, by decide⟩ 23 (transLenTr ⟨143, by decide⟩ 23 hp) : ↥(reps ⟨143, by decide⟩)) : Coordinate 1)
        T147_143 = colFn colCertDiv_147_143_23.D1 (m := 1) from colCertDiv_147_143_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨143, by decide⟩ 23 hp : ↥(Q2.reps ⟨143, by decide⟩)) : Coordinate 2)
        Q2.T147_143_2 = colFn colCertDiv_147_143_23.D2 (m := 1) from colCertDiv_147_143_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_143_23_match


theorem leaf_147_143_24 (hp : 24 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 24 (transLenTr ⟨143, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 24 (transLenTr ⟨143, by decide⟩ 24 hp)) T147_143
      hfix147_143 hinj147_143 hcardT147_143
      (fun i => conj_mem_of_fixedPoints _ _ (T147_143 i) (hfix147_143 i) _)
      ⟨147, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 24 hp) Q2.T147_143_2 Q2.hfix147_143_2 Q2.hinj147_143_2
      Q2.hcardT147_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_143_2 i) (Q2.hfix147_143_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨143, by decide⟩ 24 (transLenTr ⟨143, by decide⟩ 24 hp) : ↥(reps ⟨143, by decide⟩)) : Coordinate 1)
        T147_143 = colFn colCertDiv_147_143_24.D1 (m := 1) from colCertDiv_147_143_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨143, by decide⟩ 24 hp : ↥(Q2.reps ⟨143, by decide⟩)) : Coordinate 2)
        Q2.T147_143_2 = colFn colCertDiv_147_143_24.D2 (m := 1) from colCertDiv_147_143_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_143_24_match


theorem leaf_147_144_0 (hp : 0 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 0 (transLenTr ⟨144, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 0 (transLenTr ⟨144, by decide⟩ 0 hp)) T147_144
      hfix147_144 hinj147_144 hcardT147_144
      (fun i => conj_mem_of_fixedPoints _ _ (T147_144 i) (hfix147_144 i) _)
      ⟨147, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 0 hp) Q2.T147_144_2 Q2.hfix147_144_2 Q2.hinj147_144_2
      Q2.hcardT147_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_144_2 i) (Q2.hfix147_144_2 i) _)
      colCert_147_144_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_144_1 (hp : 1 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 1 (transLenTr ⟨144, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 1 (transLenTr ⟨144, by decide⟩ 1 hp)) T147_144
      hfix147_144 hinj147_144 hcardT147_144
      (fun i => conj_mem_of_fixedPoints _ _ (T147_144 i) (hfix147_144 i) _)
      ⟨147, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 1 hp) Q2.T147_144_2 Q2.hfix147_144_2 Q2.hinj147_144_2
      Q2.hcardT147_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_144_2 i) (Q2.hfix147_144_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨144, by decide⟩ 1 (transLenTr ⟨144, by decide⟩ 1 hp) : ↥(reps ⟨144, by decide⟩)) : Coordinate 1)
        T147_144 = colFn colCertDiv_147_144_1.D1 (m := 1) from colCertDiv_147_144_1.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨144, by decide⟩ 1 hp : ↥(Q2.reps ⟨144, by decide⟩)) : Coordinate 2)
        Q2.T147_144_2 = colFn colCertDiv_147_144_1.D2 (m := 1) from colCertDiv_147_144_1.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_144_1_match


theorem leaf_147_144_2 (hp : 2 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 2 (transLenTr ⟨144, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 2 (transLenTr ⟨144, by decide⟩ 2 hp)) T147_144
      hfix147_144 hinj147_144 hcardT147_144
      (fun i => conj_mem_of_fixedPoints _ _ (T147_144 i) (hfix147_144 i) _)
      ⟨147, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 2 hp) Q2.T147_144_2 Q2.hfix147_144_2 Q2.hinj147_144_2
      Q2.hcardT147_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_144_2 i) (Q2.hfix147_144_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨144, by decide⟩ 2 (transLenTr ⟨144, by decide⟩ 2 hp) : ↥(reps ⟨144, by decide⟩)) : Coordinate 1)
        T147_144 = colFn colCertDiv_147_144_2.D1 (m := 1) from colCertDiv_147_144_2.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨144, by decide⟩ 2 hp : ↥(Q2.reps ⟨144, by decide⟩)) : Coordinate 2)
        Q2.T147_144_2 = colFn colCertDiv_147_144_2.D2 (m := 1) from colCertDiv_147_144_2.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_144_2_match


theorem leaf_147_144_3 (hp : 3 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 3 (transLenTr ⟨144, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 3 (transLenTr ⟨144, by decide⟩ 3 hp)) T147_144
      hfix147_144 hinj147_144 hcardT147_144
      (fun i => conj_mem_of_fixedPoints _ _ (T147_144 i) (hfix147_144 i) _)
      ⟨147, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 3 hp) Q2.T147_144_2 Q2.hfix147_144_2 Q2.hinj147_144_2
      Q2.hcardT147_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_144_2 i) (Q2.hfix147_144_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨144, by decide⟩ 3 (transLenTr ⟨144, by decide⟩ 3 hp) : ↥(reps ⟨144, by decide⟩)) : Coordinate 1)
        T147_144 = colFn colCertDiv_147_144_3.D1 (m := 1) from colCertDiv_147_144_3.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨144, by decide⟩ 3 hp : ↥(Q2.reps ⟨144, by decide⟩)) : Coordinate 2)
        Q2.T147_144_2 = colFn colCertDiv_147_144_3.D2 (m := 1) from colCertDiv_147_144_3.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_144_3_match


theorem leaf_147_144_4 (hp : 4 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 4 (transLenTr ⟨144, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 4 (transLenTr ⟨144, by decide⟩ 4 hp)) T147_144
      hfix147_144 hinj147_144 hcardT147_144
      (fun i => conj_mem_of_fixedPoints _ _ (T147_144 i) (hfix147_144 i) _)
      ⟨147, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 4 hp) Q2.T147_144_2 Q2.hfix147_144_2 Q2.hinj147_144_2
      Q2.hcardT147_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_144_2 i) (Q2.hfix147_144_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨144, by decide⟩ 4 (transLenTr ⟨144, by decide⟩ 4 hp) : ↥(reps ⟨144, by decide⟩)) : Coordinate 1)
        T147_144 = colFn colCertDiv_147_144_4.D1 (m := 1) from colCertDiv_147_144_4.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨144, by decide⟩ 4 hp : ↥(Q2.reps ⟨144, by decide⟩)) : Coordinate 2)
        Q2.T147_144_2 = colFn colCertDiv_147_144_4.D2 (m := 1) from colCertDiv_147_144_4.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_144_4_match


theorem leaf_147_144_5 (hp : 5 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 5 (transLenTr ⟨144, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 5 (transLenTr ⟨144, by decide⟩ 5 hp)) T147_144
      hfix147_144 hinj147_144 hcardT147_144
      (fun i => conj_mem_of_fixedPoints _ _ (T147_144 i) (hfix147_144 i) _)
      ⟨147, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 5 hp) Q2.T147_144_2 Q2.hfix147_144_2 Q2.hinj147_144_2
      Q2.hcardT147_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_144_2 i) (Q2.hfix147_144_2 i) _)
      colCert_147_144_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_144_6 (hp : 6 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 6 (transLenTr ⟨144, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 6 (transLenTr ⟨144, by decide⟩ 6 hp)) T147_144
      hfix147_144 hinj147_144 hcardT147_144
      (fun i => conj_mem_of_fixedPoints _ _ (T147_144 i) (hfix147_144 i) _)
      ⟨147, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 6 hp) Q2.T147_144_2 Q2.hfix147_144_2 Q2.hinj147_144_2
      Q2.hcardT147_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_144_2 i) (Q2.hfix147_144_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨144, by decide⟩ 6 (transLenTr ⟨144, by decide⟩ 6 hp) : ↥(reps ⟨144, by decide⟩)) : Coordinate 1)
        T147_144 = colFn colCertDiv_147_144_6.D1 (m := 1) from colCertDiv_147_144_6.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨144, by decide⟩ 6 hp : ↥(Q2.reps ⟨144, by decide⟩)) : Coordinate 2)
        Q2.T147_144_2 = colFn colCertDiv_147_144_6.D2 (m := 1) from colCertDiv_147_144_6.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_144_6_match


theorem leaf_147_144_7 (hp : 7 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 7 (transLenTr ⟨144, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 7 (transLenTr ⟨144, by decide⟩ 7 hp)) T147_144
      hfix147_144 hinj147_144 hcardT147_144
      (fun i => conj_mem_of_fixedPoints _ _ (T147_144 i) (hfix147_144 i) _)
      ⟨147, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 7 hp) Q2.T147_144_2 Q2.hfix147_144_2 Q2.hinj147_144_2
      Q2.hcardT147_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_144_2 i) (Q2.hfix147_144_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨144, by decide⟩ 7 (transLenTr ⟨144, by decide⟩ 7 hp) : ↥(reps ⟨144, by decide⟩)) : Coordinate 1)
        T147_144 = colFn colCertDiv_147_144_7.D1 (m := 1) from colCertDiv_147_144_7.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨144, by decide⟩ 7 hp : ↥(Q2.reps ⟨144, by decide⟩)) : Coordinate 2)
        Q2.T147_144_2 = colFn colCertDiv_147_144_7.D2 (m := 1) from colCertDiv_147_144_7.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_144_7_match


theorem leaf_147_144_8 (hp : 8 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 8 (transLenTr ⟨144, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 8 (transLenTr ⟨144, by decide⟩ 8 hp)) T147_144
      hfix147_144 hinj147_144 hcardT147_144
      (fun i => conj_mem_of_fixedPoints _ _ (T147_144 i) (hfix147_144 i) _)
      ⟨147, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 8 hp) Q2.T147_144_2 Q2.hfix147_144_2 Q2.hinj147_144_2
      Q2.hcardT147_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_144_2 i) (Q2.hfix147_144_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨144, by decide⟩ 8 (transLenTr ⟨144, by decide⟩ 8 hp) : ↥(reps ⟨144, by decide⟩)) : Coordinate 1)
        T147_144 = colFn colCertDiv_147_144_8.D1 (m := 1) from colCertDiv_147_144_8.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨144, by decide⟩ 8 hp : ↥(Q2.reps ⟨144, by decide⟩)) : Coordinate 2)
        Q2.T147_144_2 = colFn colCertDiv_147_144_8.D2 (m := 1) from colCertDiv_147_144_8.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_144_8_match


theorem leaf_147_144_9 (hp : 9 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 9 (transLenTr ⟨144, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 9 (transLenTr ⟨144, by decide⟩ 9 hp)) T147_144
      hfix147_144 hinj147_144 hcardT147_144
      (fun i => conj_mem_of_fixedPoints _ _ (T147_144 i) (hfix147_144 i) _)
      ⟨147, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 9 hp) Q2.T147_144_2 Q2.hfix147_144_2 Q2.hinj147_144_2
      Q2.hcardT147_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_144_2 i) (Q2.hfix147_144_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨144, by decide⟩ 9 (transLenTr ⟨144, by decide⟩ 9 hp) : ↥(reps ⟨144, by decide⟩)) : Coordinate 1)
        T147_144 = colFn colCertDiv_147_144_9.D1 (m := 1) from colCertDiv_147_144_9.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨144, by decide⟩ 9 hp : ↥(Q2.reps ⟨144, by decide⟩)) : Coordinate 2)
        Q2.T147_144_2 = colFn colCertDiv_147_144_9.D2 (m := 1) from colCertDiv_147_144_9.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_144_9_match


theorem leaf_147_144_10 (hp : 10 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 10 (transLenTr ⟨144, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 10 (transLenTr ⟨144, by decide⟩ 10 hp)) T147_144
      hfix147_144 hinj147_144 hcardT147_144
      (fun i => conj_mem_of_fixedPoints _ _ (T147_144 i) (hfix147_144 i) _)
      ⟨147, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 10 hp) Q2.T147_144_2 Q2.hfix147_144_2 Q2.hinj147_144_2
      Q2.hcardT147_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_144_2 i) (Q2.hfix147_144_2 i) _)
      colCert_147_144_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_144_11 (hp : 11 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 11 (transLenTr ⟨144, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 11 (transLenTr ⟨144, by decide⟩ 11 hp)) T147_144
      hfix147_144 hinj147_144 hcardT147_144
      (fun i => conj_mem_of_fixedPoints _ _ (T147_144 i) (hfix147_144 i) _)
      ⟨147, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 11 hp) Q2.T147_144_2 Q2.hfix147_144_2 Q2.hinj147_144_2
      Q2.hcardT147_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_144_2 i) (Q2.hfix147_144_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨144, by decide⟩ 11 (transLenTr ⟨144, by decide⟩ 11 hp) : ↥(reps ⟨144, by decide⟩)) : Coordinate 1)
        T147_144 = colFn colCertDiv_147_144_11.D1 (m := 1) from colCertDiv_147_144_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨144, by decide⟩ 11 hp : ↥(Q2.reps ⟨144, by decide⟩)) : Coordinate 2)
        Q2.T147_144_2 = colFn colCertDiv_147_144_11.D2 (m := 1) from colCertDiv_147_144_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_144_11_match


theorem leaf_147_144_12 (hp : 12 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 12 (transLenTr ⟨144, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 12 (transLenTr ⟨144, by decide⟩ 12 hp)) T147_144
      hfix147_144 hinj147_144 hcardT147_144
      (fun i => conj_mem_of_fixedPoints _ _ (T147_144 i) (hfix147_144 i) _)
      ⟨147, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 12 hp) Q2.T147_144_2 Q2.hfix147_144_2 Q2.hinj147_144_2
      Q2.hcardT147_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_144_2 i) (Q2.hfix147_144_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨144, by decide⟩ 12 (transLenTr ⟨144, by decide⟩ 12 hp) : ↥(reps ⟨144, by decide⟩)) : Coordinate 1)
        T147_144 = colFn colCertDiv_147_144_12.D1 (m := 1) from colCertDiv_147_144_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨144, by decide⟩ 12 hp : ↥(Q2.reps ⟨144, by decide⟩)) : Coordinate 2)
        Q2.T147_144_2 = colFn colCertDiv_147_144_12.D2 (m := 1) from colCertDiv_147_144_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_144_12_match


theorem leaf_147_144_13 (hp : 13 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 13 (transLenTr ⟨144, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 13 (transLenTr ⟨144, by decide⟩ 13 hp)) T147_144
      hfix147_144 hinj147_144 hcardT147_144
      (fun i => conj_mem_of_fixedPoints _ _ (T147_144 i) (hfix147_144 i) _)
      ⟨147, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 13 hp) Q2.T147_144_2 Q2.hfix147_144_2 Q2.hinj147_144_2
      Q2.hcardT147_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_144_2 i) (Q2.hfix147_144_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨144, by decide⟩ 13 (transLenTr ⟨144, by decide⟩ 13 hp) : ↥(reps ⟨144, by decide⟩)) : Coordinate 1)
        T147_144 = colFn colCertDiv_147_144_13.D1 (m := 1) from colCertDiv_147_144_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨144, by decide⟩ 13 hp : ↥(Q2.reps ⟨144, by decide⟩)) : Coordinate 2)
        Q2.T147_144_2 = colFn colCertDiv_147_144_13.D2 (m := 1) from colCertDiv_147_144_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_144_13_match


theorem leaf_147_144_14 (hp : 14 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 14 (transLenTr ⟨144, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 14 (transLenTr ⟨144, by decide⟩ 14 hp)) T147_144
      hfix147_144 hinj147_144 hcardT147_144
      (fun i => conj_mem_of_fixedPoints _ _ (T147_144 i) (hfix147_144 i) _)
      ⟨147, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 14 hp) Q2.T147_144_2 Q2.hfix147_144_2 Q2.hinj147_144_2
      Q2.hcardT147_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_144_2 i) (Q2.hfix147_144_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨144, by decide⟩ 14 (transLenTr ⟨144, by decide⟩ 14 hp) : ↥(reps ⟨144, by decide⟩)) : Coordinate 1)
        T147_144 = colFn colCertDiv_147_144_14.D1 (m := 1) from colCertDiv_147_144_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨144, by decide⟩ 14 hp : ↥(Q2.reps ⟨144, by decide⟩)) : Coordinate 2)
        Q2.T147_144_2 = colFn colCertDiv_147_144_14.D2 (m := 1) from colCertDiv_147_144_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_144_14_match


theorem leaf_147_144_15 (hp : 15 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 15 (transLenTr ⟨144, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 15 (transLenTr ⟨144, by decide⟩ 15 hp)) T147_144
      hfix147_144 hinj147_144 hcardT147_144
      (fun i => conj_mem_of_fixedPoints _ _ (T147_144 i) (hfix147_144 i) _)
      ⟨147, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 15 hp) Q2.T147_144_2 Q2.hfix147_144_2 Q2.hinj147_144_2
      Q2.hcardT147_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_144_2 i) (Q2.hfix147_144_2 i) _)
      colCert_147_144_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_144_16 (hp : 16 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 16 (transLenTr ⟨144, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 16 (transLenTr ⟨144, by decide⟩ 16 hp)) T147_144
      hfix147_144 hinj147_144 hcardT147_144
      (fun i => conj_mem_of_fixedPoints _ _ (T147_144 i) (hfix147_144 i) _)
      ⟨147, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 16 hp) Q2.T147_144_2 Q2.hfix147_144_2 Q2.hinj147_144_2
      Q2.hcardT147_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_144_2 i) (Q2.hfix147_144_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨144, by decide⟩ 16 (transLenTr ⟨144, by decide⟩ 16 hp) : ↥(reps ⟨144, by decide⟩)) : Coordinate 1)
        T147_144 = colFn colCertDiv_147_144_16.D1 (m := 1) from colCertDiv_147_144_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨144, by decide⟩ 16 hp : ↥(Q2.reps ⟨144, by decide⟩)) : Coordinate 2)
        Q2.T147_144_2 = colFn colCertDiv_147_144_16.D2 (m := 1) from colCertDiv_147_144_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_144_16_match


theorem leaf_147_144_17 (hp : 17 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 17 (transLenTr ⟨144, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 17 (transLenTr ⟨144, by decide⟩ 17 hp)) T147_144
      hfix147_144 hinj147_144 hcardT147_144
      (fun i => conj_mem_of_fixedPoints _ _ (T147_144 i) (hfix147_144 i) _)
      ⟨147, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 17 hp) Q2.T147_144_2 Q2.hfix147_144_2 Q2.hinj147_144_2
      Q2.hcardT147_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_144_2 i) (Q2.hfix147_144_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨144, by decide⟩ 17 (transLenTr ⟨144, by decide⟩ 17 hp) : ↥(reps ⟨144, by decide⟩)) : Coordinate 1)
        T147_144 = colFn colCertDiv_147_144_17.D1 (m := 1) from colCertDiv_147_144_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨144, by decide⟩ 17 hp : ↥(Q2.reps ⟨144, by decide⟩)) : Coordinate 2)
        Q2.T147_144_2 = colFn colCertDiv_147_144_17.D2 (m := 1) from colCertDiv_147_144_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_144_17_match


theorem leaf_147_144_18 (hp : 18 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 18 (transLenTr ⟨144, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 18 (transLenTr ⟨144, by decide⟩ 18 hp)) T147_144
      hfix147_144 hinj147_144 hcardT147_144
      (fun i => conj_mem_of_fixedPoints _ _ (T147_144 i) (hfix147_144 i) _)
      ⟨147, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 18 hp) Q2.T147_144_2 Q2.hfix147_144_2 Q2.hinj147_144_2
      Q2.hcardT147_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_144_2 i) (Q2.hfix147_144_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨144, by decide⟩ 18 (transLenTr ⟨144, by decide⟩ 18 hp) : ↥(reps ⟨144, by decide⟩)) : Coordinate 1)
        T147_144 = colFn colCertDiv_147_144_18.D1 (m := 1) from colCertDiv_147_144_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨144, by decide⟩ 18 hp : ↥(Q2.reps ⟨144, by decide⟩)) : Coordinate 2)
        Q2.T147_144_2 = colFn colCertDiv_147_144_18.D2 (m := 1) from colCertDiv_147_144_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_144_18_match


theorem leaf_147_144_19 (hp : 19 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 19 (transLenTr ⟨144, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 19 (transLenTr ⟨144, by decide⟩ 19 hp)) T147_144
      hfix147_144 hinj147_144 hcardT147_144
      (fun i => conj_mem_of_fixedPoints _ _ (T147_144 i) (hfix147_144 i) _)
      ⟨147, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 19 hp) Q2.T147_144_2 Q2.hfix147_144_2 Q2.hinj147_144_2
      Q2.hcardT147_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_144_2 i) (Q2.hfix147_144_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨144, by decide⟩ 19 (transLenTr ⟨144, by decide⟩ 19 hp) : ↥(reps ⟨144, by decide⟩)) : Coordinate 1)
        T147_144 = colFn colCertDiv_147_144_19.D1 (m := 1) from colCertDiv_147_144_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨144, by decide⟩ 19 hp : ↥(Q2.reps ⟨144, by decide⟩)) : Coordinate 2)
        Q2.T147_144_2 = colFn colCertDiv_147_144_19.D2 (m := 1) from colCertDiv_147_144_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_144_19_match


theorem leaf_147_144_20 (hp : 20 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 20 (transLenTr ⟨144, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 20 (transLenTr ⟨144, by decide⟩ 20 hp)) T147_144
      hfix147_144 hinj147_144 hcardT147_144
      (fun i => conj_mem_of_fixedPoints _ _ (T147_144 i) (hfix147_144 i) _)
      ⟨147, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 20 hp) Q2.T147_144_2 Q2.hfix147_144_2 Q2.hinj147_144_2
      Q2.hcardT147_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_144_2 i) (Q2.hfix147_144_2 i) _)
      colCert_147_144_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_144_21 (hp : 21 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 21 (transLenTr ⟨144, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 21 (transLenTr ⟨144, by decide⟩ 21 hp)) T147_144
      hfix147_144 hinj147_144 hcardT147_144
      (fun i => conj_mem_of_fixedPoints _ _ (T147_144 i) (hfix147_144 i) _)
      ⟨147, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 21 hp) Q2.T147_144_2 Q2.hfix147_144_2 Q2.hinj147_144_2
      Q2.hcardT147_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_144_2 i) (Q2.hfix147_144_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨144, by decide⟩ 21 (transLenTr ⟨144, by decide⟩ 21 hp) : ↥(reps ⟨144, by decide⟩)) : Coordinate 1)
        T147_144 = colFn colCertDiv_147_144_21.D1 (m := 1) from colCertDiv_147_144_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨144, by decide⟩ 21 hp : ↥(Q2.reps ⟨144, by decide⟩)) : Coordinate 2)
        Q2.T147_144_2 = colFn colCertDiv_147_144_21.D2 (m := 1) from colCertDiv_147_144_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_144_21_match


theorem leaf_147_144_22 (hp : 22 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 22 (transLenTr ⟨144, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 22 (transLenTr ⟨144, by decide⟩ 22 hp)) T147_144
      hfix147_144 hinj147_144 hcardT147_144
      (fun i => conj_mem_of_fixedPoints _ _ (T147_144 i) (hfix147_144 i) _)
      ⟨147, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 22 hp) Q2.T147_144_2 Q2.hfix147_144_2 Q2.hinj147_144_2
      Q2.hcardT147_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_144_2 i) (Q2.hfix147_144_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨144, by decide⟩ 22 (transLenTr ⟨144, by decide⟩ 22 hp) : ↥(reps ⟨144, by decide⟩)) : Coordinate 1)
        T147_144 = colFn colCertDiv_147_144_22.D1 (m := 1) from colCertDiv_147_144_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨144, by decide⟩ 22 hp : ↥(Q2.reps ⟨144, by decide⟩)) : Coordinate 2)
        Q2.T147_144_2 = colFn colCertDiv_147_144_22.D2 (m := 1) from colCertDiv_147_144_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_144_22_match


theorem leaf_147_144_23 (hp : 23 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 23 (transLenTr ⟨144, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 23 (transLenTr ⟨144, by decide⟩ 23 hp)) T147_144
      hfix147_144 hinj147_144 hcardT147_144
      (fun i => conj_mem_of_fixedPoints _ _ (T147_144 i) (hfix147_144 i) _)
      ⟨147, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 23 hp) Q2.T147_144_2 Q2.hfix147_144_2 Q2.hinj147_144_2
      Q2.hcardT147_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_144_2 i) (Q2.hfix147_144_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨144, by decide⟩ 23 (transLenTr ⟨144, by decide⟩ 23 hp) : ↥(reps ⟨144, by decide⟩)) : Coordinate 1)
        T147_144 = colFn colCertDiv_147_144_23.D1 (m := 1) from colCertDiv_147_144_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨144, by decide⟩ 23 hp : ↥(Q2.reps ⟨144, by decide⟩)) : Coordinate 2)
        Q2.T147_144_2 = colFn colCertDiv_147_144_23.D2 (m := 1) from colCertDiv_147_144_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_144_23_match


theorem leaf_147_144_24 (hp : 24 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 24 (transLenTr ⟨144, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 24 (transLenTr ⟨144, by decide⟩ 24 hp)) T147_144
      hfix147_144 hinj147_144 hcardT147_144
      (fun i => conj_mem_of_fixedPoints _ _ (T147_144 i) (hfix147_144 i) _)
      ⟨147, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 24 hp) Q2.T147_144_2 Q2.hfix147_144_2 Q2.hinj147_144_2
      Q2.hcardT147_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_144_2 i) (Q2.hfix147_144_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨144, by decide⟩ 24 (transLenTr ⟨144, by decide⟩ 24 hp) : ↥(reps ⟨144, by decide⟩)) : Coordinate 1)
        T147_144 = colFn colCertDiv_147_144_24.D1 (m := 1) from colCertDiv_147_144_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨144, by decide⟩ 24 hp : ↥(Q2.reps ⟨144, by decide⟩)) : Coordinate 2)
        Q2.T147_144_2 = colFn colCertDiv_147_144_24.D2 (m := 1) from colCertDiv_147_144_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_144_24_match


theorem leaf_147_145_0 (hp : 0 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 0 (transLenTr ⟨145, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 0 (transLenTr ⟨145, by decide⟩ 0 hp)) T147_145
      hfix147_145 hinj147_145 hcardT147_145
      (fun i => conj_mem_of_fixedPoints _ _ (T147_145 i) (hfix147_145 i) _)
      ⟨147, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 0 hp) Q2.T147_145_2 Q2.hfix147_145_2 Q2.hinj147_145_2
      Q2.hcardT147_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_145_2 i) (Q2.hfix147_145_2 i) _)
      colCert_147_145_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_145_1 (hp : 1 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 1 (transLenTr ⟨145, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 1 (transLenTr ⟨145, by decide⟩ 1 hp)) T147_145
      hfix147_145 hinj147_145 hcardT147_145
      (fun i => conj_mem_of_fixedPoints _ _ (T147_145 i) (hfix147_145 i) _)
      ⟨147, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 1 hp) Q2.T147_145_2 Q2.hfix147_145_2 Q2.hinj147_145_2
      Q2.hcardT147_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_145_2 i) (Q2.hfix147_145_2 i) _)
      colCert_147_145_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_145_2 (hp : 2 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 2 (transLenTr ⟨145, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 2 (transLenTr ⟨145, by decide⟩ 2 hp)) T147_145
      hfix147_145 hinj147_145 hcardT147_145
      (fun i => conj_mem_of_fixedPoints _ _ (T147_145 i) (hfix147_145 i) _)
      ⟨147, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 2 hp) Q2.T147_145_2 Q2.hfix147_145_2 Q2.hinj147_145_2
      Q2.hcardT147_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_145_2 i) (Q2.hfix147_145_2 i) _)
      colCert_147_145_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_145_3 (hp : 3 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 3 (transLenTr ⟨145, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 3 (transLenTr ⟨145, by decide⟩ 3 hp)) T147_145
      hfix147_145 hinj147_145 hcardT147_145
      (fun i => conj_mem_of_fixedPoints _ _ (T147_145 i) (hfix147_145 i) _)
      ⟨147, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 3 hp) Q2.T147_145_2 Q2.hfix147_145_2 Q2.hinj147_145_2
      Q2.hcardT147_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_145_2 i) (Q2.hfix147_145_2 i) _)
      colCert_147_145_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_145_4 (hp : 4 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 4 (transLenTr ⟨145, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 4 (transLenTr ⟨145, by decide⟩ 4 hp)) T147_145
      hfix147_145 hinj147_145 hcardT147_145
      (fun i => conj_mem_of_fixedPoints _ _ (T147_145 i) (hfix147_145 i) _)
      ⟨147, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 4 hp) Q2.T147_145_2 Q2.hfix147_145_2 Q2.hinj147_145_2
      Q2.hcardT147_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_145_2 i) (Q2.hfix147_145_2 i) _)
      colCert_147_145_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_145_5 (hp : 5 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 5 (transLenTr ⟨145, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 5 (transLenTr ⟨145, by decide⟩ 5 hp)) T147_145
      hfix147_145 hinj147_145 hcardT147_145
      (fun i => conj_mem_of_fixedPoints _ _ (T147_145 i) (hfix147_145 i) _)
      ⟨147, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 5 hp) Q2.T147_145_2 Q2.hfix147_145_2 Q2.hinj147_145_2
      Q2.hcardT147_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_145_2 i) (Q2.hfix147_145_2 i) _)
      colCert_147_145_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_145_6 (hp : 6 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 6 (transLenTr ⟨145, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 6 (transLenTr ⟨145, by decide⟩ 6 hp)) T147_145
      hfix147_145 hinj147_145 hcardT147_145
      (fun i => conj_mem_of_fixedPoints _ _ (T147_145 i) (hfix147_145 i) _)
      ⟨147, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 6 hp) Q2.T147_145_2 Q2.hfix147_145_2 Q2.hinj147_145_2
      Q2.hcardT147_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_145_2 i) (Q2.hfix147_145_2 i) _)
      colCert_147_145_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_145_7 (hp : 7 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 7 (transLenTr ⟨145, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 7 (transLenTr ⟨145, by decide⟩ 7 hp)) T147_145
      hfix147_145 hinj147_145 hcardT147_145
      (fun i => conj_mem_of_fixedPoints _ _ (T147_145 i) (hfix147_145 i) _)
      ⟨147, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 7 hp) Q2.T147_145_2 Q2.hfix147_145_2 Q2.hinj147_145_2
      Q2.hcardT147_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_145_2 i) (Q2.hfix147_145_2 i) _)
      colCert_147_145_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_145_8 (hp : 8 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 8 (transLenTr ⟨145, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 8 (transLenTr ⟨145, by decide⟩ 8 hp)) T147_145
      hfix147_145 hinj147_145 hcardT147_145
      (fun i => conj_mem_of_fixedPoints _ _ (T147_145 i) (hfix147_145 i) _)
      ⟨147, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 8 hp) Q2.T147_145_2 Q2.hfix147_145_2 Q2.hinj147_145_2
      Q2.hcardT147_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_145_2 i) (Q2.hfix147_145_2 i) _)
      colCert_147_145_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_145_9 (hp : 9 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 9 (transLenTr ⟨145, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 9 (transLenTr ⟨145, by decide⟩ 9 hp)) T147_145
      hfix147_145 hinj147_145 hcardT147_145
      (fun i => conj_mem_of_fixedPoints _ _ (T147_145 i) (hfix147_145 i) _)
      ⟨147, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 9 hp) Q2.T147_145_2 Q2.hfix147_145_2 Q2.hinj147_145_2
      Q2.hcardT147_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_145_2 i) (Q2.hfix147_145_2 i) _)
      colCert_147_145_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_145_10 (hp : 10 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 10 (transLenTr ⟨145, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 10 (transLenTr ⟨145, by decide⟩ 10 hp)) T147_145
      hfix147_145 hinj147_145 hcardT147_145
      (fun i => conj_mem_of_fixedPoints _ _ (T147_145 i) (hfix147_145 i) _)
      ⟨147, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 10 hp) Q2.T147_145_2 Q2.hfix147_145_2 Q2.hinj147_145_2
      Q2.hcardT147_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_145_2 i) (Q2.hfix147_145_2 i) _)
      colCert_147_145_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_145_11 (hp : 11 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 11 (transLenTr ⟨145, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 11 (transLenTr ⟨145, by decide⟩ 11 hp)) T147_145
      hfix147_145 hinj147_145 hcardT147_145
      (fun i => conj_mem_of_fixedPoints _ _ (T147_145 i) (hfix147_145 i) _)
      ⟨147, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 11 hp) Q2.T147_145_2 Q2.hfix147_145_2 Q2.hinj147_145_2
      Q2.hcardT147_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_145_2 i) (Q2.hfix147_145_2 i) _)
      colCert_147_145_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_145_12 (hp : 12 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 12 (transLenTr ⟨145, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 12 (transLenTr ⟨145, by decide⟩ 12 hp)) T147_145
      hfix147_145 hinj147_145 hcardT147_145
      (fun i => conj_mem_of_fixedPoints _ _ (T147_145 i) (hfix147_145 i) _)
      ⟨147, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 12 hp) Q2.T147_145_2 Q2.hfix147_145_2 Q2.hinj147_145_2
      Q2.hcardT147_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_145_2 i) (Q2.hfix147_145_2 i) _)
      colCert_147_145_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_145_13 (hp : 13 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 13 (transLenTr ⟨145, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 13 (transLenTr ⟨145, by decide⟩ 13 hp)) T147_145
      hfix147_145 hinj147_145 hcardT147_145
      (fun i => conj_mem_of_fixedPoints _ _ (T147_145 i) (hfix147_145 i) _)
      ⟨147, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 13 hp) Q2.T147_145_2 Q2.hfix147_145_2 Q2.hinj147_145_2
      Q2.hcardT147_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_145_2 i) (Q2.hfix147_145_2 i) _)
      colCert_147_145_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_145_14 (hp : 14 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 14 (transLenTr ⟨145, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 14 (transLenTr ⟨145, by decide⟩ 14 hp)) T147_145
      hfix147_145 hinj147_145 hcardT147_145
      (fun i => conj_mem_of_fixedPoints _ _ (T147_145 i) (hfix147_145 i) _)
      ⟨147, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 14 hp) Q2.T147_145_2 Q2.hfix147_145_2 Q2.hinj147_145_2
      Q2.hcardT147_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_145_2 i) (Q2.hfix147_145_2 i) _)
      colCert_147_145_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_145_15 (hp : 15 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 15 (transLenTr ⟨145, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 15 (transLenTr ⟨145, by decide⟩ 15 hp)) T147_145
      hfix147_145 hinj147_145 hcardT147_145
      (fun i => conj_mem_of_fixedPoints _ _ (T147_145 i) (hfix147_145 i) _)
      ⟨147, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 15 hp) Q2.T147_145_2 Q2.hfix147_145_2 Q2.hinj147_145_2
      Q2.hcardT147_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_145_2 i) (Q2.hfix147_145_2 i) _)
      colCert_147_145_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_145_16 (hp : 16 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 16 (transLenTr ⟨145, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 16 (transLenTr ⟨145, by decide⟩ 16 hp)) T147_145
      hfix147_145 hinj147_145 hcardT147_145
      (fun i => conj_mem_of_fixedPoints _ _ (T147_145 i) (hfix147_145 i) _)
      ⟨147, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 16 hp) Q2.T147_145_2 Q2.hfix147_145_2 Q2.hinj147_145_2
      Q2.hcardT147_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_145_2 i) (Q2.hfix147_145_2 i) _)
      colCert_147_145_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_145_17 (hp : 17 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 17 (transLenTr ⟨145, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 17 (transLenTr ⟨145, by decide⟩ 17 hp)) T147_145
      hfix147_145 hinj147_145 hcardT147_145
      (fun i => conj_mem_of_fixedPoints _ _ (T147_145 i) (hfix147_145 i) _)
      ⟨147, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 17 hp) Q2.T147_145_2 Q2.hfix147_145_2 Q2.hinj147_145_2
      Q2.hcardT147_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_145_2 i) (Q2.hfix147_145_2 i) _)
      colCert_147_145_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_145_18 (hp : 18 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 18 (transLenTr ⟨145, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 18 (transLenTr ⟨145, by decide⟩ 18 hp)) T147_145
      hfix147_145 hinj147_145 hcardT147_145
      (fun i => conj_mem_of_fixedPoints _ _ (T147_145 i) (hfix147_145 i) _)
      ⟨147, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 18 hp) Q2.T147_145_2 Q2.hfix147_145_2 Q2.hinj147_145_2
      Q2.hcardT147_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_145_2 i) (Q2.hfix147_145_2 i) _)
      colCert_147_145_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_145_19 (hp : 19 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 19 (transLenTr ⟨145, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 19 (transLenTr ⟨145, by decide⟩ 19 hp)) T147_145
      hfix147_145 hinj147_145 hcardT147_145
      (fun i => conj_mem_of_fixedPoints _ _ (T147_145 i) (hfix147_145 i) _)
      ⟨147, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 19 hp) Q2.T147_145_2 Q2.hfix147_145_2 Q2.hinj147_145_2
      Q2.hcardT147_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_145_2 i) (Q2.hfix147_145_2 i) _)
      colCert_147_145_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_145_20 (hp : 20 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 20 (transLenTr ⟨145, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 20 (transLenTr ⟨145, by decide⟩ 20 hp)) T147_145
      hfix147_145 hinj147_145 hcardT147_145
      (fun i => conj_mem_of_fixedPoints _ _ (T147_145 i) (hfix147_145 i) _)
      ⟨147, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 20 hp) Q2.T147_145_2 Q2.hfix147_145_2 Q2.hinj147_145_2
      Q2.hcardT147_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_145_2 i) (Q2.hfix147_145_2 i) _)
      colCert_147_145_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_145_21 (hp : 21 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 21 (transLenTr ⟨145, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 21 (transLenTr ⟨145, by decide⟩ 21 hp)) T147_145
      hfix147_145 hinj147_145 hcardT147_145
      (fun i => conj_mem_of_fixedPoints _ _ (T147_145 i) (hfix147_145 i) _)
      ⟨147, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 21 hp) Q2.T147_145_2 Q2.hfix147_145_2 Q2.hinj147_145_2
      Q2.hcardT147_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_145_2 i) (Q2.hfix147_145_2 i) _)
      colCert_147_145_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_145_22 (hp : 22 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 22 (transLenTr ⟨145, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 22 (transLenTr ⟨145, by decide⟩ 22 hp)) T147_145
      hfix147_145 hinj147_145 hcardT147_145
      (fun i => conj_mem_of_fixedPoints _ _ (T147_145 i) (hfix147_145 i) _)
      ⟨147, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 22 hp) Q2.T147_145_2 Q2.hfix147_145_2 Q2.hinj147_145_2
      Q2.hcardT147_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_145_2 i) (Q2.hfix147_145_2 i) _)
      colCert_147_145_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_145_23 (hp : 23 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 23 (transLenTr ⟨145, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 23 (transLenTr ⟨145, by decide⟩ 23 hp)) T147_145
      hfix147_145 hinj147_145 hcardT147_145
      (fun i => conj_mem_of_fixedPoints _ _ (T147_145 i) (hfix147_145 i) _)
      ⟨147, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 23 hp) Q2.T147_145_2 Q2.hfix147_145_2 Q2.hinj147_145_2
      Q2.hcardT147_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_145_2 i) (Q2.hfix147_145_2 i) _)
      colCert_147_145_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_145_24 (hp : 24 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 24 (transLenTr ⟨145, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 24 (transLenTr ⟨145, by decide⟩ 24 hp)) T147_145
      hfix147_145 hinj147_145 hcardT147_145
      (fun i => conj_mem_of_fixedPoints _ _ (T147_145 i) (hfix147_145 i) _)
      ⟨147, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 24 hp) Q2.T147_145_2 Q2.hfix147_145_2 Q2.hinj147_145_2
      Q2.hcardT147_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_145_2 i) (Q2.hfix147_145_2 i) _)
      colCert_147_145_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_146_0 (hp : 0 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 0 (transLenTr ⟨146, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 0 (transLenTr ⟨146, by decide⟩ 0 hp)) T147_146
      hfix147_146 hinj147_146 hcardT147_146
      (fun i => conj_mem_of_fixedPoints _ _ (T147_146 i) (hfix147_146 i) _)
      ⟨147, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 0 hp) Q2.T147_146_2 Q2.hfix147_146_2 Q2.hinj147_146_2
      Q2.hcardT147_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_146_2 i) (Q2.hfix147_146_2 i) _)
      colCert_147_146_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_146_1 (hp : 1 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 1 (transLenTr ⟨146, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 1 (transLenTr ⟨146, by decide⟩ 1 hp)) T147_146
      hfix147_146 hinj147_146 hcardT147_146
      (fun i => conj_mem_of_fixedPoints _ _ (T147_146 i) (hfix147_146 i) _)
      ⟨147, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 1 hp) Q2.T147_146_2 Q2.hfix147_146_2 Q2.hinj147_146_2
      Q2.hcardT147_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_146_2 i) (Q2.hfix147_146_2 i) _)
      colCert_147_146_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_146_2 (hp : 2 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 2 (transLenTr ⟨146, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 2 (transLenTr ⟨146, by decide⟩ 2 hp)) T147_146
      hfix147_146 hinj147_146 hcardT147_146
      (fun i => conj_mem_of_fixedPoints _ _ (T147_146 i) (hfix147_146 i) _)
      ⟨147, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 2 hp) Q2.T147_146_2 Q2.hfix147_146_2 Q2.hinj147_146_2
      Q2.hcardT147_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_146_2 i) (Q2.hfix147_146_2 i) _)
      colCert_147_146_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_146_3 (hp : 3 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 3 (transLenTr ⟨146, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 3 (transLenTr ⟨146, by decide⟩ 3 hp)) T147_146
      hfix147_146 hinj147_146 hcardT147_146
      (fun i => conj_mem_of_fixedPoints _ _ (T147_146 i) (hfix147_146 i) _)
      ⟨147, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 3 hp) Q2.T147_146_2 Q2.hfix147_146_2 Q2.hinj147_146_2
      Q2.hcardT147_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_146_2 i) (Q2.hfix147_146_2 i) _)
      colCert_147_146_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_146_4 (hp : 4 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 4 (transLenTr ⟨146, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 4 (transLenTr ⟨146, by decide⟩ 4 hp)) T147_146
      hfix147_146 hinj147_146 hcardT147_146
      (fun i => conj_mem_of_fixedPoints _ _ (T147_146 i) (hfix147_146 i) _)
      ⟨147, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 4 hp) Q2.T147_146_2 Q2.hfix147_146_2 Q2.hinj147_146_2
      Q2.hcardT147_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_146_2 i) (Q2.hfix147_146_2 i) _)
      colCert_147_146_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_146_5 (hp : 5 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 5 (transLenTr ⟨146, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 5 (transLenTr ⟨146, by decide⟩ 5 hp)) T147_146
      hfix147_146 hinj147_146 hcardT147_146
      (fun i => conj_mem_of_fixedPoints _ _ (T147_146 i) (hfix147_146 i) _)
      ⟨147, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 5 hp) Q2.T147_146_2 Q2.hfix147_146_2 Q2.hinj147_146_2
      Q2.hcardT147_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_146_2 i) (Q2.hfix147_146_2 i) _)
      colCert_147_146_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_146_6 (hp : 6 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 6 (transLenTr ⟨146, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 6 (transLenTr ⟨146, by decide⟩ 6 hp)) T147_146
      hfix147_146 hinj147_146 hcardT147_146
      (fun i => conj_mem_of_fixedPoints _ _ (T147_146 i) (hfix147_146 i) _)
      ⟨147, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 6 hp) Q2.T147_146_2 Q2.hfix147_146_2 Q2.hinj147_146_2
      Q2.hcardT147_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_146_2 i) (Q2.hfix147_146_2 i) _)
      colCert_147_146_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_146_7 (hp : 7 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 7 (transLenTr ⟨146, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 7 (transLenTr ⟨146, by decide⟩ 7 hp)) T147_146
      hfix147_146 hinj147_146 hcardT147_146
      (fun i => conj_mem_of_fixedPoints _ _ (T147_146 i) (hfix147_146 i) _)
      ⟨147, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 7 hp) Q2.T147_146_2 Q2.hfix147_146_2 Q2.hinj147_146_2
      Q2.hcardT147_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_146_2 i) (Q2.hfix147_146_2 i) _)
      colCert_147_146_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_146_8 (hp : 8 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 8 (transLenTr ⟨146, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 8 (transLenTr ⟨146, by decide⟩ 8 hp)) T147_146
      hfix147_146 hinj147_146 hcardT147_146
      (fun i => conj_mem_of_fixedPoints _ _ (T147_146 i) (hfix147_146 i) _)
      ⟨147, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 8 hp) Q2.T147_146_2 Q2.hfix147_146_2 Q2.hinj147_146_2
      Q2.hcardT147_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_146_2 i) (Q2.hfix147_146_2 i) _)
      colCert_147_146_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_146_9 (hp : 9 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 9 (transLenTr ⟨146, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 9 (transLenTr ⟨146, by decide⟩ 9 hp)) T147_146
      hfix147_146 hinj147_146 hcardT147_146
      (fun i => conj_mem_of_fixedPoints _ _ (T147_146 i) (hfix147_146 i) _)
      ⟨147, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 9 hp) Q2.T147_146_2 Q2.hfix147_146_2 Q2.hinj147_146_2
      Q2.hcardT147_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_146_2 i) (Q2.hfix147_146_2 i) _)
      colCert_147_146_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_146_10 (hp : 10 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 10 (transLenTr ⟨146, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 10 (transLenTr ⟨146, by decide⟩ 10 hp)) T147_146
      hfix147_146 hinj147_146 hcardT147_146
      (fun i => conj_mem_of_fixedPoints _ _ (T147_146 i) (hfix147_146 i) _)
      ⟨147, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 10 hp) Q2.T147_146_2 Q2.hfix147_146_2 Q2.hinj147_146_2
      Q2.hcardT147_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_146_2 i) (Q2.hfix147_146_2 i) _)
      colCert_147_146_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_146_11 (hp : 11 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 11 (transLenTr ⟨146, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 11 (transLenTr ⟨146, by decide⟩ 11 hp)) T147_146
      hfix147_146 hinj147_146 hcardT147_146
      (fun i => conj_mem_of_fixedPoints _ _ (T147_146 i) (hfix147_146 i) _)
      ⟨147, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 11 hp) Q2.T147_146_2 Q2.hfix147_146_2 Q2.hinj147_146_2
      Q2.hcardT147_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_146_2 i) (Q2.hfix147_146_2 i) _)
      colCert_147_146_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_146_12 (hp : 12 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 12 (transLenTr ⟨146, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 12 (transLenTr ⟨146, by decide⟩ 12 hp)) T147_146
      hfix147_146 hinj147_146 hcardT147_146
      (fun i => conj_mem_of_fixedPoints _ _ (T147_146 i) (hfix147_146 i) _)
      ⟨147, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 12 hp) Q2.T147_146_2 Q2.hfix147_146_2 Q2.hinj147_146_2
      Q2.hcardT147_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_146_2 i) (Q2.hfix147_146_2 i) _)
      colCert_147_146_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_146_13 (hp : 13 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 13 (transLenTr ⟨146, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 13 (transLenTr ⟨146, by decide⟩ 13 hp)) T147_146
      hfix147_146 hinj147_146 hcardT147_146
      (fun i => conj_mem_of_fixedPoints _ _ (T147_146 i) (hfix147_146 i) _)
      ⟨147, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 13 hp) Q2.T147_146_2 Q2.hfix147_146_2 Q2.hinj147_146_2
      Q2.hcardT147_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_146_2 i) (Q2.hfix147_146_2 i) _)
      colCert_147_146_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_146_14 (hp : 14 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 14 (transLenTr ⟨146, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 14 (transLenTr ⟨146, by decide⟩ 14 hp)) T147_146
      hfix147_146 hinj147_146 hcardT147_146
      (fun i => conj_mem_of_fixedPoints _ _ (T147_146 i) (hfix147_146 i) _)
      ⟨147, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 14 hp) Q2.T147_146_2 Q2.hfix147_146_2 Q2.hinj147_146_2
      Q2.hcardT147_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_146_2 i) (Q2.hfix147_146_2 i) _)
      colCert_147_146_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_146_15 (hp : 15 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 15 (transLenTr ⟨146, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 15 (transLenTr ⟨146, by decide⟩ 15 hp)) T147_146
      hfix147_146 hinj147_146 hcardT147_146
      (fun i => conj_mem_of_fixedPoints _ _ (T147_146 i) (hfix147_146 i) _)
      ⟨147, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 15 hp) Q2.T147_146_2 Q2.hfix147_146_2 Q2.hinj147_146_2
      Q2.hcardT147_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_146_2 i) (Q2.hfix147_146_2 i) _)
      colCert_147_146_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_146_16 (hp : 16 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 16 (transLenTr ⟨146, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 16 (transLenTr ⟨146, by decide⟩ 16 hp)) T147_146
      hfix147_146 hinj147_146 hcardT147_146
      (fun i => conj_mem_of_fixedPoints _ _ (T147_146 i) (hfix147_146 i) _)
      ⟨147, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 16 hp) Q2.T147_146_2 Q2.hfix147_146_2 Q2.hinj147_146_2
      Q2.hcardT147_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_146_2 i) (Q2.hfix147_146_2 i) _)
      colCert_147_146_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_146_17 (hp : 17 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 17 (transLenTr ⟨146, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 17 (transLenTr ⟨146, by decide⟩ 17 hp)) T147_146
      hfix147_146 hinj147_146 hcardT147_146
      (fun i => conj_mem_of_fixedPoints _ _ (T147_146 i) (hfix147_146 i) _)
      ⟨147, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 17 hp) Q2.T147_146_2 Q2.hfix147_146_2 Q2.hinj147_146_2
      Q2.hcardT147_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_146_2 i) (Q2.hfix147_146_2 i) _)
      colCert_147_146_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_146_18 (hp : 18 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 18 (transLenTr ⟨146, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 18 (transLenTr ⟨146, by decide⟩ 18 hp)) T147_146
      hfix147_146 hinj147_146 hcardT147_146
      (fun i => conj_mem_of_fixedPoints _ _ (T147_146 i) (hfix147_146 i) _)
      ⟨147, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 18 hp) Q2.T147_146_2 Q2.hfix147_146_2 Q2.hinj147_146_2
      Q2.hcardT147_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_146_2 i) (Q2.hfix147_146_2 i) _)
      colCert_147_146_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_146_19 (hp : 19 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 19 (transLenTr ⟨146, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 19 (transLenTr ⟨146, by decide⟩ 19 hp)) T147_146
      hfix147_146 hinj147_146 hcardT147_146
      (fun i => conj_mem_of_fixedPoints _ _ (T147_146 i) (hfix147_146 i) _)
      ⟨147, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 19 hp) Q2.T147_146_2 Q2.hfix147_146_2 Q2.hinj147_146_2
      Q2.hcardT147_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_146_2 i) (Q2.hfix147_146_2 i) _)
      colCert_147_146_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_146_20 (hp : 20 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 20 (transLenTr ⟨146, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 20 (transLenTr ⟨146, by decide⟩ 20 hp)) T147_146
      hfix147_146 hinj147_146 hcardT147_146
      (fun i => conj_mem_of_fixedPoints _ _ (T147_146 i) (hfix147_146 i) _)
      ⟨147, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 20 hp) Q2.T147_146_2 Q2.hfix147_146_2 Q2.hinj147_146_2
      Q2.hcardT147_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_146_2 i) (Q2.hfix147_146_2 i) _)
      colCert_147_146_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_146_21 (hp : 21 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 21 (transLenTr ⟨146, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 21 (transLenTr ⟨146, by decide⟩ 21 hp)) T147_146
      hfix147_146 hinj147_146 hcardT147_146
      (fun i => conj_mem_of_fixedPoints _ _ (T147_146 i) (hfix147_146 i) _)
      ⟨147, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 21 hp) Q2.T147_146_2 Q2.hfix147_146_2 Q2.hinj147_146_2
      Q2.hcardT147_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_146_2 i) (Q2.hfix147_146_2 i) _)
      colCert_147_146_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_146_22 (hp : 22 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 22 (transLenTr ⟨146, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 22 (transLenTr ⟨146, by decide⟩ 22 hp)) T147_146
      hfix147_146 hinj147_146 hcardT147_146
      (fun i => conj_mem_of_fixedPoints _ _ (T147_146 i) (hfix147_146 i) _)
      ⟨147, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 22 hp) Q2.T147_146_2 Q2.hfix147_146_2 Q2.hinj147_146_2
      Q2.hcardT147_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_146_2 i) (Q2.hfix147_146_2 i) _)
      colCert_147_146_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_146_23 (hp : 23 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 23 (transLenTr ⟨146, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 23 (transLenTr ⟨146, by decide⟩ 23 hp)) T147_146
      hfix147_146 hinj147_146 hcardT147_146
      (fun i => conj_mem_of_fixedPoints _ _ (T147_146 i) (hfix147_146 i) _)
      ⟨147, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 23 hp) Q2.T147_146_2 Q2.hfix147_146_2 Q2.hinj147_146_2
      Q2.hcardT147_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_146_2 i) (Q2.hfix147_146_2 i) _)
      colCert_147_146_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_146_24 (hp : 24 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 24 (transLenTr ⟨146, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 24 (transLenTr ⟨146, by decide⟩ 24 hp)) T147_146
      hfix147_146 hinj147_146 hcardT147_146
      (fun i => conj_mem_of_fixedPoints _ _ (T147_146 i) (hfix147_146 i) _)
      ⟨147, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 24 hp) Q2.T147_146_2 Q2.hfix147_146_2 Q2.hinj147_146_2
      Q2.hcardT147_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_146_2 i) (Q2.hfix147_146_2 i) _)
      colCert_147_146_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_0 (hp : 0 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 0 (transLenTr ⟨147, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 0 (transLenTr ⟨147, by decide⟩ 0 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 0 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_1 (hp : 1 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 1 (transLenTr ⟨147, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 1 (transLenTr ⟨147, by decide⟩ 1 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 1 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_2 (hp : 2 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 2 (transLenTr ⟨147, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 2 (transLenTr ⟨147, by decide⟩ 2 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 2 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_3 (hp : 3 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 3 (transLenTr ⟨147, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 3 (transLenTr ⟨147, by decide⟩ 3 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 3 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_4 (hp : 4 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 4 (transLenTr ⟨147, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 4 (transLenTr ⟨147, by decide⟩ 4 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 4 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_5 (hp : 5 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 5 (transLenTr ⟨147, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 5 (transLenTr ⟨147, by decide⟩ 5 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 5 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_6 (hp : 6 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 6 (transLenTr ⟨147, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 6 (transLenTr ⟨147, by decide⟩ 6 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 6 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_7 (hp : 7 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 7 (transLenTr ⟨147, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 7 (transLenTr ⟨147, by decide⟩ 7 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 7 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_8 (hp : 8 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 8 (transLenTr ⟨147, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 8 (transLenTr ⟨147, by decide⟩ 8 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 8 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_9 (hp : 9 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 9 (transLenTr ⟨147, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 9 (transLenTr ⟨147, by decide⟩ 9 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 9 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_10 (hp : 10 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 10 (transLenTr ⟨147, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 10 (transLenTr ⟨147, by decide⟩ 10 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 10 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_11 (hp : 11 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 11 (transLenTr ⟨147, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 11 (transLenTr ⟨147, by decide⟩ 11 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 11 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_12 (hp : 12 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 12 (transLenTr ⟨147, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 12 (transLenTr ⟨147, by decide⟩ 12 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 12 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_13 (hp : 13 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 13 (transLenTr ⟨147, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 13 (transLenTr ⟨147, by decide⟩ 13 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 13 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_14 (hp : 14 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 14 (transLenTr ⟨147, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 14 (transLenTr ⟨147, by decide⟩ 14 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 14 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_15 (hp : 15 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 15 (transLenTr ⟨147, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 15 (transLenTr ⟨147, by decide⟩ 15 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 15 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_16 (hp : 16 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 16 (transLenTr ⟨147, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 16 (transLenTr ⟨147, by decide⟩ 16 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 16 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_17 (hp : 17 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 17 (transLenTr ⟨147, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 17 (transLenTr ⟨147, by decide⟩ 17 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 17 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_18 (hp : 18 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 18 (transLenTr ⟨147, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 18 (transLenTr ⟨147, by decide⟩ 18 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 18 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_19 (hp : 19 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 19 (transLenTr ⟨147, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 19 (transLenTr ⟨147, by decide⟩ 19 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 19 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_20 (hp : 20 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 20 (transLenTr ⟨147, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 20 (transLenTr ⟨147, by decide⟩ 20 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 20 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_21 (hp : 21 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 21 (transLenTr ⟨147, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 21 (transLenTr ⟨147, by decide⟩ 21 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 21 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_22 (hp : 22 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 22 (transLenTr ⟨147, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 22 (transLenTr ⟨147, by decide⟩ 22 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 22 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_23 (hp : 23 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 23 (transLenTr ⟨147, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 23 (transLenTr ⟨147, by decide⟩ 23 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 23 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_24 (hp : 24 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 24 (transLenTr ⟨147, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 24 (transLenTr ⟨147, by decide⟩ 24 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 24 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_25 (hp : 25 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 25 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 25 (transLenTr ⟨147, by decide⟩ 25 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 25 (transLenTr ⟨147, by decide⟩ 25 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 25 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_25.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_26 (hp : 26 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 26 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 26 (transLenTr ⟨147, by decide⟩ 26 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 26 (transLenTr ⟨147, by decide⟩ 26 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 26 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_26.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_27 (hp : 27 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 27 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 27 (transLenTr ⟨147, by decide⟩ 27 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 27 (transLenTr ⟨147, by decide⟩ 27 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 27 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_27.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_28 (hp : 28 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 28 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 28 (transLenTr ⟨147, by decide⟩ 28 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 28 (transLenTr ⟨147, by decide⟩ 28 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 28 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_28.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_29 (hp : 29 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 29 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 29 (transLenTr ⟨147, by decide⟩ 29 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 29 (transLenTr ⟨147, by decide⟩ 29 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 29 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_29.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_30 (hp : 30 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 30 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 30 (transLenTr ⟨147, by decide⟩ 30 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 30 (transLenTr ⟨147, by decide⟩ 30 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 30 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_30.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_31 (hp : 31 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 31 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 31 (transLenTr ⟨147, by decide⟩ 31 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 31 (transLenTr ⟨147, by decide⟩ 31 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 31 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_31.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_32 (hp : 32 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 32 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 32 (transLenTr ⟨147, by decide⟩ 32 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 32 (transLenTr ⟨147, by decide⟩ 32 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 32 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_32.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_33 (hp : 33 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 33 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 33 (transLenTr ⟨147, by decide⟩ 33 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 33 (transLenTr ⟨147, by decide⟩ 33 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 33 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_33.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_34 (hp : 34 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 34 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 34 (transLenTr ⟨147, by decide⟩ 34 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 34 (transLenTr ⟨147, by decide⟩ 34 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 34 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_34.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_35 (hp : 35 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 35 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 35 (transLenTr ⟨147, by decide⟩ 35 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 35 (transLenTr ⟨147, by decide⟩ 35 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 35 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_35.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_36 (hp : 36 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 36 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 36 (transLenTr ⟨147, by decide⟩ 36 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 36 (transLenTr ⟨147, by decide⟩ 36 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 36 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_36.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_37 (hp : 37 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 37 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 37 (transLenTr ⟨147, by decide⟩ 37 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 37 (transLenTr ⟨147, by decide⟩ 37 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 37 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_37.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_38 (hp : 38 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 38 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 38 (transLenTr ⟨147, by decide⟩ 38 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 38 (transLenTr ⟨147, by decide⟩ 38 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 38 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_38.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_39 (hp : 39 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 39 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 39 (transLenTr ⟨147, by decide⟩ 39 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 39 (transLenTr ⟨147, by decide⟩ 39 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 39 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_39.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_40 (hp : 40 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 40 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 40 (transLenTr ⟨147, by decide⟩ 40 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 40 (transLenTr ⟨147, by decide⟩ 40 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 40 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_40.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_41 (hp : 41 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 41 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 41 (transLenTr ⟨147, by decide⟩ 41 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 41 (transLenTr ⟨147, by decide⟩ 41 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 41 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_41.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_42 (hp : 42 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 42 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 42 (transLenTr ⟨147, by decide⟩ 42 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 42 (transLenTr ⟨147, by decide⟩ 42 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 42 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_42.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_43 (hp : 43 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 43 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 43 (transLenTr ⟨147, by decide⟩ 43 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 43 (transLenTr ⟨147, by decide⟩ 43 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 43 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_43.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_44 (hp : 44 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 44 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 44 (transLenTr ⟨147, by decide⟩ 44 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 44 (transLenTr ⟨147, by decide⟩ 44 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 44 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_44.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_45 (hp : 45 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 45 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 45 (transLenTr ⟨147, by decide⟩ 45 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 45 (transLenTr ⟨147, by decide⟩ 45 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 45 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_45.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_46 (hp : 46 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 46 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 46 (transLenTr ⟨147, by decide⟩ 46 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 46 (transLenTr ⟨147, by decide⟩ 46 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 46 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_46.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_47 (hp : 47 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 47 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 47 (transLenTr ⟨147, by decide⟩ 47 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 47 (transLenTr ⟨147, by decide⟩ 47 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 47 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_47.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_48 (hp : 48 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 48 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 48 (transLenTr ⟨147, by decide⟩ 48 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 48 (transLenTr ⟨147, by decide⟩ 48 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 48 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_48.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_49 (hp : 49 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 49 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 49 (transLenTr ⟨147, by decide⟩ 49 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 49 (transLenTr ⟨147, by decide⟩ 49 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 49 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_49.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_50 (hp : 50 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 50 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 50 (transLenTr ⟨147, by decide⟩ 50 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 50 (transLenTr ⟨147, by decide⟩ 50 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 50 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_50.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_51 (hp : 51 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 51 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 51 (transLenTr ⟨147, by decide⟩ 51 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 51 (transLenTr ⟨147, by decide⟩ 51 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 51 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_51.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_52 (hp : 52 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 52 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 52 (transLenTr ⟨147, by decide⟩ 52 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 52 (transLenTr ⟨147, by decide⟩ 52 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 52 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_52.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_53 (hp : 53 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 53 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 53 (transLenTr ⟨147, by decide⟩ 53 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 53 (transLenTr ⟨147, by decide⟩ 53 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 53 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_53.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_54 (hp : 54 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 54 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 54 (transLenTr ⟨147, by decide⟩ 54 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 54 (transLenTr ⟨147, by decide⟩ 54 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 54 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_54.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_55 (hp : 55 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 55 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 55 (transLenTr ⟨147, by decide⟩ 55 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 55 (transLenTr ⟨147, by decide⟩ 55 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 55 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_55.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_56 (hp : 56 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 56 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 56 (transLenTr ⟨147, by decide⟩ 56 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 56 (transLenTr ⟨147, by decide⟩ 56 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 56 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_56.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_57 (hp : 57 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 57 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 57 (transLenTr ⟨147, by decide⟩ 57 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 57 (transLenTr ⟨147, by decide⟩ 57 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 57 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_57.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_58 (hp : 58 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 58 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 58 (transLenTr ⟨147, by decide⟩ 58 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 58 (transLenTr ⟨147, by decide⟩ 58 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 58 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_58.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_59 (hp : 59 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 59 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 59 (transLenTr ⟨147, by decide⟩ 59 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 59 (transLenTr ⟨147, by decide⟩ 59 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 59 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_59.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_60 (hp : 60 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 60 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 60 (transLenTr ⟨147, by decide⟩ 60 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 60 (transLenTr ⟨147, by decide⟩ 60 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 60 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_60.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_61 (hp : 61 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 61 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 61 (transLenTr ⟨147, by decide⟩ 61 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 61 (transLenTr ⟨147, by decide⟩ 61 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 61 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_61.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_62 (hp : 62 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 62 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 62 (transLenTr ⟨147, by decide⟩ 62 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 62 (transLenTr ⟨147, by decide⟩ 62 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 62 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_62.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_63 (hp : 63 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 63 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 63 (transLenTr ⟨147, by decide⟩ 63 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 63 (transLenTr ⟨147, by decide⟩ 63 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 63 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_63.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_64 (hp : 64 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 64 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 64 (transLenTr ⟨147, by decide⟩ 64 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 64 (transLenTr ⟨147, by decide⟩ 64 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 64 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_64.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_65 (hp : 65 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 65 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 65 (transLenTr ⟨147, by decide⟩ 65 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 65 (transLenTr ⟨147, by decide⟩ 65 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 65 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_65.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_66 (hp : 66 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 66 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 66 (transLenTr ⟨147, by decide⟩ 66 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 66 (transLenTr ⟨147, by decide⟩ 66 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 66 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_66.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_67 (hp : 67 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 67 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 67 (transLenTr ⟨147, by decide⟩ 67 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 67 (transLenTr ⟨147, by decide⟩ 67 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 67 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_67.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_68 (hp : 68 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 68 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 68 (transLenTr ⟨147, by decide⟩ 68 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 68 (transLenTr ⟨147, by decide⟩ 68 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 68 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_68.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_69 (hp : 69 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 69 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 69 (transLenTr ⟨147, by decide⟩ 69 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 69 (transLenTr ⟨147, by decide⟩ 69 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 69 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_69.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_70 (hp : 70 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 70 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 70 (transLenTr ⟨147, by decide⟩ 70 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 70 (transLenTr ⟨147, by decide⟩ 70 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 70 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_70.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_71 (hp : 71 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 71 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 71 (transLenTr ⟨147, by decide⟩ 71 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 71 (transLenTr ⟨147, by decide⟩ 71 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 71 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_71.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_72 (hp : 72 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 72 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 72 (transLenTr ⟨147, by decide⟩ 72 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 72 (transLenTr ⟨147, by decide⟩ 72 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 72 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_72.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_73 (hp : 73 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 73 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 73 (transLenTr ⟨147, by decide⟩ 73 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 73 (transLenTr ⟨147, by decide⟩ 73 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 73 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_73.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_74 (hp : 74 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 74 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 74 (transLenTr ⟨147, by decide⟩ 74 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 74 (transLenTr ⟨147, by decide⟩ 74 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 74 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_74.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_75 (hp : 75 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 75 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 75 (transLenTr ⟨147, by decide⟩ 75 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 75 (transLenTr ⟨147, by decide⟩ 75 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 75 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_75.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_76 (hp : 76 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 76 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 76 (transLenTr ⟨147, by decide⟩ 76 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 76 (transLenTr ⟨147, by decide⟩ 76 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 76 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_76.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_77 (hp : 77 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 77 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 77 (transLenTr ⟨147, by decide⟩ 77 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 77 (transLenTr ⟨147, by decide⟩ 77 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 77 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_77.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_78 (hp : 78 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 78 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 78 (transLenTr ⟨147, by decide⟩ 78 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 78 (transLenTr ⟨147, by decide⟩ 78 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 78 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_78.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_79 (hp : 79 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 79 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 79 (transLenTr ⟨147, by decide⟩ 79 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 79 (transLenTr ⟨147, by decide⟩ 79 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 79 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_79.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_80 (hp : 80 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 80 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 80 (transLenTr ⟨147, by decide⟩ 80 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 80 (transLenTr ⟨147, by decide⟩ 80 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 80 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_80.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_81 (hp : 81 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 81 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 81 (transLenTr ⟨147, by decide⟩ 81 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 81 (transLenTr ⟨147, by decide⟩ 81 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 81 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_81.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_82 (hp : 82 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 82 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 82 (transLenTr ⟨147, by decide⟩ 82 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 82 (transLenTr ⟨147, by decide⟩ 82 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 82 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_82.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_83 (hp : 83 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 83 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 83 (transLenTr ⟨147, by decide⟩ 83 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 83 (transLenTr ⟨147, by decide⟩ 83 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 83 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_83.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_84 (hp : 84 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 84 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 84 (transLenTr ⟨147, by decide⟩ 84 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 84 (transLenTr ⟨147, by decide⟩ 84 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 84 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_84.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_85 (hp : 85 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 85 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 85 (transLenTr ⟨147, by decide⟩ 85 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 85 (transLenTr ⟨147, by decide⟩ 85 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 85 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_85.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_86 (hp : 86 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 86 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 86 (transLenTr ⟨147, by decide⟩ 86 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 86 (transLenTr ⟨147, by decide⟩ 86 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 86 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_86.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_87 (hp : 87 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 87 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 87 (transLenTr ⟨147, by decide⟩ 87 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 87 (transLenTr ⟨147, by decide⟩ 87 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 87 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_87.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_88 (hp : 88 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 88 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 88 (transLenTr ⟨147, by decide⟩ 88 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 88 (transLenTr ⟨147, by decide⟩ 88 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 88 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_88.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_89 (hp : 89 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 89 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 89 (transLenTr ⟨147, by decide⟩ 89 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 89 (transLenTr ⟨147, by decide⟩ 89 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 89 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_89.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_90 (hp : 90 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 90 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 90 (transLenTr ⟨147, by decide⟩ 90 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 90 (transLenTr ⟨147, by decide⟩ 90 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 90 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_90.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_91 (hp : 91 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 91 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 91 (transLenTr ⟨147, by decide⟩ 91 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 91 (transLenTr ⟨147, by decide⟩ 91 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 91 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_91.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_92 (hp : 92 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 92 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 92 (transLenTr ⟨147, by decide⟩ 92 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 92 (transLenTr ⟨147, by decide⟩ 92 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 92 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_92.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_93 (hp : 93 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 93 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 93 (transLenTr ⟨147, by decide⟩ 93 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 93 (transLenTr ⟨147, by decide⟩ 93 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 93 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_93.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_94 (hp : 94 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 94 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 94 (transLenTr ⟨147, by decide⟩ 94 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 94 (transLenTr ⟨147, by decide⟩ 94 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 94 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_94.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_95 (hp : 95 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 95 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 95 (transLenTr ⟨147, by decide⟩ 95 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 95 (transLenTr ⟨147, by decide⟩ 95 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 95 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_95.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_96 (hp : 96 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 96 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 96 (transLenTr ⟨147, by decide⟩ 96 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 96 (transLenTr ⟨147, by decide⟩ 96 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 96 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_96.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_97 (hp : 97 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 97 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 97 (transLenTr ⟨147, by decide⟩ 97 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 97 (transLenTr ⟨147, by decide⟩ 97 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 97 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_97.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_98 (hp : 98 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 98 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 98 (transLenTr ⟨147, by decide⟩ 98 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 98 (transLenTr ⟨147, by decide⟩ 98 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 98 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_98.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_99 (hp : 99 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 99 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 99 (transLenTr ⟨147, by decide⟩ 99 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 99 (transLenTr ⟨147, by decide⟩ 99 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 99 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_99.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_100 (hp : 100 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 100 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 100 (transLenTr ⟨147, by decide⟩ 100 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 100 (transLenTr ⟨147, by decide⟩ 100 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 100 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_100.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_101 (hp : 101 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 101 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 101 (transLenTr ⟨147, by decide⟩ 101 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 101 (transLenTr ⟨147, by decide⟩ 101 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 101 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_101.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_102 (hp : 102 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 102 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 102 (transLenTr ⟨147, by decide⟩ 102 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 102 (transLenTr ⟨147, by decide⟩ 102 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 102 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_102.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_103 (hp : 103 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 103 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 103 (transLenTr ⟨147, by decide⟩ 103 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 103 (transLenTr ⟨147, by decide⟩ 103 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 103 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_103.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_104 (hp : 104 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 104 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 104 (transLenTr ⟨147, by decide⟩ 104 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 104 (transLenTr ⟨147, by decide⟩ 104 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 104 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_104.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_105 (hp : 105 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 105 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 105 (transLenTr ⟨147, by decide⟩ 105 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 105 (transLenTr ⟨147, by decide⟩ 105 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 105 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_105.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_106 (hp : 106 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 106 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 106 (transLenTr ⟨147, by decide⟩ 106 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 106 (transLenTr ⟨147, by decide⟩ 106 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 106 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_106.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_107 (hp : 107 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 107 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 107 (transLenTr ⟨147, by decide⟩ 107 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 107 (transLenTr ⟨147, by decide⟩ 107 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 107 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_107.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_108 (hp : 108 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 108 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 108 (transLenTr ⟨147, by decide⟩ 108 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 108 (transLenTr ⟨147, by decide⟩ 108 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 108 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_108.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_109 (hp : 109 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 109 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 109 (transLenTr ⟨147, by decide⟩ 109 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 109 (transLenTr ⟨147, by decide⟩ 109 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 109 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_109.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_110 (hp : 110 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 110 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 110 (transLenTr ⟨147, by decide⟩ 110 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 110 (transLenTr ⟨147, by decide⟩ 110 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 110 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_110.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_111 (hp : 111 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 111 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 111 (transLenTr ⟨147, by decide⟩ 111 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 111 (transLenTr ⟨147, by decide⟩ 111 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 111 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_111.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_112 (hp : 112 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 112 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 112 (transLenTr ⟨147, by decide⟩ 112 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 112 (transLenTr ⟨147, by decide⟩ 112 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 112 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_112.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_113 (hp : 113 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 113 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 113 (transLenTr ⟨147, by decide⟩ 113 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 113 (transLenTr ⟨147, by decide⟩ 113 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 113 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_113.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_114 (hp : 114 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 114 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 114 (transLenTr ⟨147, by decide⟩ 114 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 114 (transLenTr ⟨147, by decide⟩ 114 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 114 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_114.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_115 (hp : 115 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 115 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 115 (transLenTr ⟨147, by decide⟩ 115 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 115 (transLenTr ⟨147, by decide⟩ 115 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 115 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_115.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_116 (hp : 116 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 116 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 116 (transLenTr ⟨147, by decide⟩ 116 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 116 (transLenTr ⟨147, by decide⟩ 116 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 116 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_116.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_117 (hp : 117 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 117 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 117 (transLenTr ⟨147, by decide⟩ 117 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 117 (transLenTr ⟨147, by decide⟩ 117 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 117 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_117.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_118 (hp : 118 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 118 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 118 (transLenTr ⟨147, by decide⟩ 118 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 118 (transLenTr ⟨147, by decide⟩ 118 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 118 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_118.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_119 (hp : 119 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 119 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 119 (transLenTr ⟨147, by decide⟩ 119 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 119 (transLenTr ⟨147, by decide⟩ 119 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 119 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_119.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_120 (hp : 120 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 120 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 120 (transLenTr ⟨147, by decide⟩ 120 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 120 (transLenTr ⟨147, by decide⟩ 120 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 120 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_120.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_121 (hp : 121 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 121 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 121 (transLenTr ⟨147, by decide⟩ 121 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 121 (transLenTr ⟨147, by decide⟩ 121 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 121 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_121.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_122 (hp : 122 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 122 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 122 (transLenTr ⟨147, by decide⟩ 122 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 122 (transLenTr ⟨147, by decide⟩ 122 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 122 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_122.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_123 (hp : 123 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 123 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 123 (transLenTr ⟨147, by decide⟩ 123 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 123 (transLenTr ⟨147, by decide⟩ 123 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 123 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_123.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_147_124 (hp : 124 < (Q2.transData.getD 147 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ 124 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ 124 (transLenTr ⟨147, by decide⟩ 124 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨147, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨147, by decide⟩ 124 (transLenTr ⟨147, by decide⟩ 124 hp)) T147_147
      hfix147_147 hinj147_147 hcardT147_147
      (fun i => conj_mem_of_fixedPoints _ _ (T147_147 i) (hfix147_147 i) _)
      ⟨147, by decide⟩ ⟨147, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨147, by decide⟩ 124 hp) Q2.T147_147_2 Q2.hfix147_147_2 Q2.hinj147_147_2
      Q2.hcardT147_147_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_147_2 i) (Q2.hfix147_147_2 i) _)
      colCert_147_147_124.hD ?_).symm
  rw [alnId_147 j hj]


end LeanDring.P5Presentation
