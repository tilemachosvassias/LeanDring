/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C033
import LeanDring.P5.Data.ColCdd.C034
import LeanDring.P5.Data.ColCdd.C035
import LeanDring.P5.Data.ColRestCheap.C131
import LeanDring.P5.Data.ColRestCheap.C132
import LeanDring.P5.Data.ColRestCheap.C133
import LeanDring.P5.Data.EntryK.C044
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C042

/-! # Stage-5 leaves, chunk 56 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_147_124_17 (hp : 17 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 17 (transLenTr ⟨124, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 17 (transLenTr ⟨124, by decide⟩ 17 hp)) T147_124
      hfix147_124 hinj147_124 hcardT147_124
      (fun i => conj_mem_of_fixedPoints _ _ (T147_124 i) (hfix147_124 i) _)
      ⟨147, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 17 hp) Q2.T147_124_2 Q2.hfix147_124_2 Q2.hinj147_124_2
      Q2.hcardT147_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_124_2 i) (Q2.hfix147_124_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨124, by decide⟩ 17 (transLenTr ⟨124, by decide⟩ 17 hp) : ↥(reps ⟨124, by decide⟩)) : Coordinate 1)
        T147_124 = colFn colCertDiv_147_124_17.D1 (m := 1) from colCertDiv_147_124_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨124, by decide⟩ 17 hp : ↥(Q2.reps ⟨124, by decide⟩)) : Coordinate 2)
        Q2.T147_124_2 = colFn colCertDiv_147_124_17.D2 (m := 1) from colCertDiv_147_124_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_124_17_match


theorem leaf_147_124_18 (hp : 18 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 18 (transLenTr ⟨124, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 18 (transLenTr ⟨124, by decide⟩ 18 hp)) T147_124
      hfix147_124 hinj147_124 hcardT147_124
      (fun i => conj_mem_of_fixedPoints _ _ (T147_124 i) (hfix147_124 i) _)
      ⟨147, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 18 hp) Q2.T147_124_2 Q2.hfix147_124_2 Q2.hinj147_124_2
      Q2.hcardT147_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_124_2 i) (Q2.hfix147_124_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨124, by decide⟩ 18 (transLenTr ⟨124, by decide⟩ 18 hp) : ↥(reps ⟨124, by decide⟩)) : Coordinate 1)
        T147_124 = colFn colCertDiv_147_124_18.D1 (m := 1) from colCertDiv_147_124_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨124, by decide⟩ 18 hp : ↥(Q2.reps ⟨124, by decide⟩)) : Coordinate 2)
        Q2.T147_124_2 = colFn colCertDiv_147_124_18.D2 (m := 1) from colCertDiv_147_124_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_124_18_match


theorem leaf_147_124_19 (hp : 19 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 19 (transLenTr ⟨124, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 19 (transLenTr ⟨124, by decide⟩ 19 hp)) T147_124
      hfix147_124 hinj147_124 hcardT147_124
      (fun i => conj_mem_of_fixedPoints _ _ (T147_124 i) (hfix147_124 i) _)
      ⟨147, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 19 hp) Q2.T147_124_2 Q2.hfix147_124_2 Q2.hinj147_124_2
      Q2.hcardT147_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_124_2 i) (Q2.hfix147_124_2 i) _)
      colCert_147_124_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_124_20 (hp : 20 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 20 (transLenTr ⟨124, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 20 (transLenTr ⟨124, by decide⟩ 20 hp)) T147_124
      hfix147_124 hinj147_124 hcardT147_124
      (fun i => conj_mem_of_fixedPoints _ _ (T147_124 i) (hfix147_124 i) _)
      ⟨147, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 20 hp) Q2.T147_124_2 Q2.hfix147_124_2 Q2.hinj147_124_2
      Q2.hcardT147_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_124_2 i) (Q2.hfix147_124_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨124, by decide⟩ 20 (transLenTr ⟨124, by decide⟩ 20 hp) : ↥(reps ⟨124, by decide⟩)) : Coordinate 1)
        T147_124 = colFn colCertDiv_147_124_20.D1 (m := 1) from colCertDiv_147_124_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨124, by decide⟩ 20 hp : ↥(Q2.reps ⟨124, by decide⟩)) : Coordinate 2)
        Q2.T147_124_2 = colFn colCertDiv_147_124_20.D2 (m := 1) from colCertDiv_147_124_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_124_20_match


theorem leaf_147_124_21 (hp : 21 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 21 (transLenTr ⟨124, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 21 (transLenTr ⟨124, by decide⟩ 21 hp)) T147_124
      hfix147_124 hinj147_124 hcardT147_124
      (fun i => conj_mem_of_fixedPoints _ _ (T147_124 i) (hfix147_124 i) _)
      ⟨147, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 21 hp) Q2.T147_124_2 Q2.hfix147_124_2 Q2.hinj147_124_2
      Q2.hcardT147_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_124_2 i) (Q2.hfix147_124_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨124, by decide⟩ 21 (transLenTr ⟨124, by decide⟩ 21 hp) : ↥(reps ⟨124, by decide⟩)) : Coordinate 1)
        T147_124 = colFn colCertDiv_147_124_21.D1 (m := 1) from colCertDiv_147_124_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨124, by decide⟩ 21 hp : ↥(Q2.reps ⟨124, by decide⟩)) : Coordinate 2)
        Q2.T147_124_2 = colFn colCertDiv_147_124_21.D2 (m := 1) from colCertDiv_147_124_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_124_21_match


theorem leaf_147_124_22 (hp : 22 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 22 (transLenTr ⟨124, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 22 (transLenTr ⟨124, by decide⟩ 22 hp)) T147_124
      hfix147_124 hinj147_124 hcardT147_124
      (fun i => conj_mem_of_fixedPoints _ _ (T147_124 i) (hfix147_124 i) _)
      ⟨147, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 22 hp) Q2.T147_124_2 Q2.hfix147_124_2 Q2.hinj147_124_2
      Q2.hcardT147_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_124_2 i) (Q2.hfix147_124_2 i) _)
      colCert_147_124_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_124_23 (hp : 23 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 23 (transLenTr ⟨124, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 23 (transLenTr ⟨124, by decide⟩ 23 hp)) T147_124
      hfix147_124 hinj147_124 hcardT147_124
      (fun i => conj_mem_of_fixedPoints _ _ (T147_124 i) (hfix147_124 i) _)
      ⟨147, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 23 hp) Q2.T147_124_2 Q2.hfix147_124_2 Q2.hinj147_124_2
      Q2.hcardT147_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_124_2 i) (Q2.hfix147_124_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨124, by decide⟩ 23 (transLenTr ⟨124, by decide⟩ 23 hp) : ↥(reps ⟨124, by decide⟩)) : Coordinate 1)
        T147_124 = colFn colCertDiv_147_124_23.D1 (m := 1) from colCertDiv_147_124_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨124, by decide⟩ 23 hp : ↥(Q2.reps ⟨124, by decide⟩)) : Coordinate 2)
        Q2.T147_124_2 = colFn colCertDiv_147_124_23.D2 (m := 1) from colCertDiv_147_124_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_124_23_match


theorem leaf_147_124_24 (hp : 24 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 24 (transLenTr ⟨124, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 24 (transLenTr ⟨124, by decide⟩ 24 hp)) T147_124
      hfix147_124 hinj147_124 hcardT147_124
      (fun i => conj_mem_of_fixedPoints _ _ (T147_124 i) (hfix147_124 i) _)
      ⟨147, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 24 hp) Q2.T147_124_2 Q2.hfix147_124_2 Q2.hinj147_124_2
      Q2.hcardT147_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_124_2 i) (Q2.hfix147_124_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨124, by decide⟩ 24 (transLenTr ⟨124, by decide⟩ 24 hp) : ↥(reps ⟨124, by decide⟩)) : Coordinate 1)
        T147_124 = colFn colCertDiv_147_124_24.D1 (m := 1) from colCertDiv_147_124_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨124, by decide⟩ 24 hp : ↥(Q2.reps ⟨124, by decide⟩)) : Coordinate 2)
        Q2.T147_124_2 = colFn colCertDiv_147_124_24.D2 (m := 1) from colCertDiv_147_124_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_124_24_match


theorem leaf_147_125_0 (hp : 0 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 0 (transLenTr ⟨125, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 0 (transLenTr ⟨125, by decide⟩ 0 hp)) T147_125
      hfix147_125 hinj147_125 hcardT147_125
      (fun i => conj_mem_of_fixedPoints _ _ (T147_125 i) (hfix147_125 i) _)
      ⟨147, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 0 hp) Q2.T147_125_2 Q2.hfix147_125_2 Q2.hinj147_125_2
      Q2.hcardT147_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_125_2 i) (Q2.hfix147_125_2 i) _)
      colCert_147_125_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_125_1 (hp : 1 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 1 (transLenTr ⟨125, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 1 (transLenTr ⟨125, by decide⟩ 1 hp)) T147_125
      hfix147_125 hinj147_125 hcardT147_125
      (fun i => conj_mem_of_fixedPoints _ _ (T147_125 i) (hfix147_125 i) _)
      ⟨147, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 1 hp) Q2.T147_125_2 Q2.hfix147_125_2 Q2.hinj147_125_2
      Q2.hcardT147_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_125_2 i) (Q2.hfix147_125_2 i) _)
      colCert_147_125_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_125_2 (hp : 2 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 2 (transLenTr ⟨125, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 2 (transLenTr ⟨125, by decide⟩ 2 hp)) T147_125
      hfix147_125 hinj147_125 hcardT147_125
      (fun i => conj_mem_of_fixedPoints _ _ (T147_125 i) (hfix147_125 i) _)
      ⟨147, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 2 hp) Q2.T147_125_2 Q2.hfix147_125_2 Q2.hinj147_125_2
      Q2.hcardT147_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_125_2 i) (Q2.hfix147_125_2 i) _)
      colCert_147_125_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_125_3 (hp : 3 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 3 (transLenTr ⟨125, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 3 (transLenTr ⟨125, by decide⟩ 3 hp)) T147_125
      hfix147_125 hinj147_125 hcardT147_125
      (fun i => conj_mem_of_fixedPoints _ _ (T147_125 i) (hfix147_125 i) _)
      ⟨147, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 3 hp) Q2.T147_125_2 Q2.hfix147_125_2 Q2.hinj147_125_2
      Q2.hcardT147_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_125_2 i) (Q2.hfix147_125_2 i) _)
      colCert_147_125_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_125_4 (hp : 4 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 4 (transLenTr ⟨125, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 4 (transLenTr ⟨125, by decide⟩ 4 hp)) T147_125
      hfix147_125 hinj147_125 hcardT147_125
      (fun i => conj_mem_of_fixedPoints _ _ (T147_125 i) (hfix147_125 i) _)
      ⟨147, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 4 hp) Q2.T147_125_2 Q2.hfix147_125_2 Q2.hinj147_125_2
      Q2.hcardT147_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_125_2 i) (Q2.hfix147_125_2 i) _)
      colCert_147_125_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_125_5 (hp : 5 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 5 (transLenTr ⟨125, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 5 (transLenTr ⟨125, by decide⟩ 5 hp)) T147_125
      hfix147_125 hinj147_125 hcardT147_125
      (fun i => conj_mem_of_fixedPoints _ _ (T147_125 i) (hfix147_125 i) _)
      ⟨147, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 5 hp) Q2.T147_125_2 Q2.hfix147_125_2 Q2.hinj147_125_2
      Q2.hcardT147_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_125_2 i) (Q2.hfix147_125_2 i) _)
      colCert_147_125_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_125_6 (hp : 6 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 6 (transLenTr ⟨125, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 6 (transLenTr ⟨125, by decide⟩ 6 hp)) T147_125
      hfix147_125 hinj147_125 hcardT147_125
      (fun i => conj_mem_of_fixedPoints _ _ (T147_125 i) (hfix147_125 i) _)
      ⟨147, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 6 hp) Q2.T147_125_2 Q2.hfix147_125_2 Q2.hinj147_125_2
      Q2.hcardT147_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_125_2 i) (Q2.hfix147_125_2 i) _)
      colCert_147_125_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_125_7 (hp : 7 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 7 (transLenTr ⟨125, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 7 (transLenTr ⟨125, by decide⟩ 7 hp)) T147_125
      hfix147_125 hinj147_125 hcardT147_125
      (fun i => conj_mem_of_fixedPoints _ _ (T147_125 i) (hfix147_125 i) _)
      ⟨147, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 7 hp) Q2.T147_125_2 Q2.hfix147_125_2 Q2.hinj147_125_2
      Q2.hcardT147_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_125_2 i) (Q2.hfix147_125_2 i) _)
      colCert_147_125_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_125_8 (hp : 8 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 8 (transLenTr ⟨125, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 8 (transLenTr ⟨125, by decide⟩ 8 hp)) T147_125
      hfix147_125 hinj147_125 hcardT147_125
      (fun i => conj_mem_of_fixedPoints _ _ (T147_125 i) (hfix147_125 i) _)
      ⟨147, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 8 hp) Q2.T147_125_2 Q2.hfix147_125_2 Q2.hinj147_125_2
      Q2.hcardT147_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_125_2 i) (Q2.hfix147_125_2 i) _)
      colCert_147_125_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_125_9 (hp : 9 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 9 (transLenTr ⟨125, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 9 (transLenTr ⟨125, by decide⟩ 9 hp)) T147_125
      hfix147_125 hinj147_125 hcardT147_125
      (fun i => conj_mem_of_fixedPoints _ _ (T147_125 i) (hfix147_125 i) _)
      ⟨147, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 9 hp) Q2.T147_125_2 Q2.hfix147_125_2 Q2.hinj147_125_2
      Q2.hcardT147_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_125_2 i) (Q2.hfix147_125_2 i) _)
      colCert_147_125_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_125_10 (hp : 10 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 10 (transLenTr ⟨125, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 10 (transLenTr ⟨125, by decide⟩ 10 hp)) T147_125
      hfix147_125 hinj147_125 hcardT147_125
      (fun i => conj_mem_of_fixedPoints _ _ (T147_125 i) (hfix147_125 i) _)
      ⟨147, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 10 hp) Q2.T147_125_2 Q2.hfix147_125_2 Q2.hinj147_125_2
      Q2.hcardT147_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_125_2 i) (Q2.hfix147_125_2 i) _)
      colCert_147_125_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_125_11 (hp : 11 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 11 (transLenTr ⟨125, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 11 (transLenTr ⟨125, by decide⟩ 11 hp)) T147_125
      hfix147_125 hinj147_125 hcardT147_125
      (fun i => conj_mem_of_fixedPoints _ _ (T147_125 i) (hfix147_125 i) _)
      ⟨147, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 11 hp) Q2.T147_125_2 Q2.hfix147_125_2 Q2.hinj147_125_2
      Q2.hcardT147_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_125_2 i) (Q2.hfix147_125_2 i) _)
      colCert_147_125_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_125_12 (hp : 12 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 12 (transLenTr ⟨125, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 12 (transLenTr ⟨125, by decide⟩ 12 hp)) T147_125
      hfix147_125 hinj147_125 hcardT147_125
      (fun i => conj_mem_of_fixedPoints _ _ (T147_125 i) (hfix147_125 i) _)
      ⟨147, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 12 hp) Q2.T147_125_2 Q2.hfix147_125_2 Q2.hinj147_125_2
      Q2.hcardT147_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_125_2 i) (Q2.hfix147_125_2 i) _)
      colCert_147_125_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_125_13 (hp : 13 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 13 (transLenTr ⟨125, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 13 (transLenTr ⟨125, by decide⟩ 13 hp)) T147_125
      hfix147_125 hinj147_125 hcardT147_125
      (fun i => conj_mem_of_fixedPoints _ _ (T147_125 i) (hfix147_125 i) _)
      ⟨147, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 13 hp) Q2.T147_125_2 Q2.hfix147_125_2 Q2.hinj147_125_2
      Q2.hcardT147_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_125_2 i) (Q2.hfix147_125_2 i) _)
      colCert_147_125_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_125_14 (hp : 14 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 14 (transLenTr ⟨125, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 14 (transLenTr ⟨125, by decide⟩ 14 hp)) T147_125
      hfix147_125 hinj147_125 hcardT147_125
      (fun i => conj_mem_of_fixedPoints _ _ (T147_125 i) (hfix147_125 i) _)
      ⟨147, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 14 hp) Q2.T147_125_2 Q2.hfix147_125_2 Q2.hinj147_125_2
      Q2.hcardT147_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_125_2 i) (Q2.hfix147_125_2 i) _)
      colCert_147_125_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_125_15 (hp : 15 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 15 (transLenTr ⟨125, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 15 (transLenTr ⟨125, by decide⟩ 15 hp)) T147_125
      hfix147_125 hinj147_125 hcardT147_125
      (fun i => conj_mem_of_fixedPoints _ _ (T147_125 i) (hfix147_125 i) _)
      ⟨147, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 15 hp) Q2.T147_125_2 Q2.hfix147_125_2 Q2.hinj147_125_2
      Q2.hcardT147_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_125_2 i) (Q2.hfix147_125_2 i) _)
      colCert_147_125_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_125_16 (hp : 16 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 16 (transLenTr ⟨125, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 16 (transLenTr ⟨125, by decide⟩ 16 hp)) T147_125
      hfix147_125 hinj147_125 hcardT147_125
      (fun i => conj_mem_of_fixedPoints _ _ (T147_125 i) (hfix147_125 i) _)
      ⟨147, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 16 hp) Q2.T147_125_2 Q2.hfix147_125_2 Q2.hinj147_125_2
      Q2.hcardT147_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_125_2 i) (Q2.hfix147_125_2 i) _)
      colCert_147_125_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_125_17 (hp : 17 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 17 (transLenTr ⟨125, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 17 (transLenTr ⟨125, by decide⟩ 17 hp)) T147_125
      hfix147_125 hinj147_125 hcardT147_125
      (fun i => conj_mem_of_fixedPoints _ _ (T147_125 i) (hfix147_125 i) _)
      ⟨147, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 17 hp) Q2.T147_125_2 Q2.hfix147_125_2 Q2.hinj147_125_2
      Q2.hcardT147_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_125_2 i) (Q2.hfix147_125_2 i) _)
      colCert_147_125_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_125_18 (hp : 18 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 18 (transLenTr ⟨125, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 18 (transLenTr ⟨125, by decide⟩ 18 hp)) T147_125
      hfix147_125 hinj147_125 hcardT147_125
      (fun i => conj_mem_of_fixedPoints _ _ (T147_125 i) (hfix147_125 i) _)
      ⟨147, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 18 hp) Q2.T147_125_2 Q2.hfix147_125_2 Q2.hinj147_125_2
      Q2.hcardT147_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_125_2 i) (Q2.hfix147_125_2 i) _)
      colCert_147_125_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_125_19 (hp : 19 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 19 (transLenTr ⟨125, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 19 (transLenTr ⟨125, by decide⟩ 19 hp)) T147_125
      hfix147_125 hinj147_125 hcardT147_125
      (fun i => conj_mem_of_fixedPoints _ _ (T147_125 i) (hfix147_125 i) _)
      ⟨147, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 19 hp) Q2.T147_125_2 Q2.hfix147_125_2 Q2.hinj147_125_2
      Q2.hcardT147_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_125_2 i) (Q2.hfix147_125_2 i) _)
      colCert_147_125_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_125_20 (hp : 20 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 20 (transLenTr ⟨125, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 20 (transLenTr ⟨125, by decide⟩ 20 hp)) T147_125
      hfix147_125 hinj147_125 hcardT147_125
      (fun i => conj_mem_of_fixedPoints _ _ (T147_125 i) (hfix147_125 i) _)
      ⟨147, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 20 hp) Q2.T147_125_2 Q2.hfix147_125_2 Q2.hinj147_125_2
      Q2.hcardT147_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_125_2 i) (Q2.hfix147_125_2 i) _)
      colCert_147_125_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_125_21 (hp : 21 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 21 (transLenTr ⟨125, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 21 (transLenTr ⟨125, by decide⟩ 21 hp)) T147_125
      hfix147_125 hinj147_125 hcardT147_125
      (fun i => conj_mem_of_fixedPoints _ _ (T147_125 i) (hfix147_125 i) _)
      ⟨147, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 21 hp) Q2.T147_125_2 Q2.hfix147_125_2 Q2.hinj147_125_2
      Q2.hcardT147_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_125_2 i) (Q2.hfix147_125_2 i) _)
      colCert_147_125_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_125_22 (hp : 22 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 22 (transLenTr ⟨125, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 22 (transLenTr ⟨125, by decide⟩ 22 hp)) T147_125
      hfix147_125 hinj147_125 hcardT147_125
      (fun i => conj_mem_of_fixedPoints _ _ (T147_125 i) (hfix147_125 i) _)
      ⟨147, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 22 hp) Q2.T147_125_2 Q2.hfix147_125_2 Q2.hinj147_125_2
      Q2.hcardT147_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_125_2 i) (Q2.hfix147_125_2 i) _)
      colCert_147_125_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_125_23 (hp : 23 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 23 (transLenTr ⟨125, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 23 (transLenTr ⟨125, by decide⟩ 23 hp)) T147_125
      hfix147_125 hinj147_125 hcardT147_125
      (fun i => conj_mem_of_fixedPoints _ _ (T147_125 i) (hfix147_125 i) _)
      ⟨147, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 23 hp) Q2.T147_125_2 Q2.hfix147_125_2 Q2.hinj147_125_2
      Q2.hcardT147_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_125_2 i) (Q2.hfix147_125_2 i) _)
      colCert_147_125_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_125_24 (hp : 24 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 24 (transLenTr ⟨125, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 24 (transLenTr ⟨125, by decide⟩ 24 hp)) T147_125
      hfix147_125 hinj147_125 hcardT147_125
      (fun i => conj_mem_of_fixedPoints _ _ (T147_125 i) (hfix147_125 i) _)
      ⟨147, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 24 hp) Q2.T147_125_2 Q2.hfix147_125_2 Q2.hinj147_125_2
      Q2.hcardT147_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_125_2 i) (Q2.hfix147_125_2 i) _)
      colCert_147_125_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_126_0 (hp : 0 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 0 (transLenTr ⟨126, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 0 (transLenTr ⟨126, by decide⟩ 0 hp)) T147_126
      hfix147_126 hinj147_126 hcardT147_126
      (fun i => conj_mem_of_fixedPoints _ _ (T147_126 i) (hfix147_126 i) _)
      ⟨147, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 0 hp) Q2.T147_126_2 Q2.hfix147_126_2 Q2.hinj147_126_2
      Q2.hcardT147_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_126_2 i) (Q2.hfix147_126_2 i) _)
      colCert_147_126_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_126_1 (hp : 1 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 1 (transLenTr ⟨126, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 1 (transLenTr ⟨126, by decide⟩ 1 hp)) T147_126
      hfix147_126 hinj147_126 hcardT147_126
      (fun i => conj_mem_of_fixedPoints _ _ (T147_126 i) (hfix147_126 i) _)
      ⟨147, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 1 hp) Q2.T147_126_2 Q2.hfix147_126_2 Q2.hinj147_126_2
      Q2.hcardT147_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_126_2 i) (Q2.hfix147_126_2 i) _)
      colCert_147_126_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_126_2 (hp : 2 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 2 (transLenTr ⟨126, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 2 (transLenTr ⟨126, by decide⟩ 2 hp)) T147_126
      hfix147_126 hinj147_126 hcardT147_126
      (fun i => conj_mem_of_fixedPoints _ _ (T147_126 i) (hfix147_126 i) _)
      ⟨147, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 2 hp) Q2.T147_126_2 Q2.hfix147_126_2 Q2.hinj147_126_2
      Q2.hcardT147_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_126_2 i) (Q2.hfix147_126_2 i) _)
      colCert_147_126_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_126_3 (hp : 3 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 3 (transLenTr ⟨126, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 3 (transLenTr ⟨126, by decide⟩ 3 hp)) T147_126
      hfix147_126 hinj147_126 hcardT147_126
      (fun i => conj_mem_of_fixedPoints _ _ (T147_126 i) (hfix147_126 i) _)
      ⟨147, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 3 hp) Q2.T147_126_2 Q2.hfix147_126_2 Q2.hinj147_126_2
      Q2.hcardT147_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_126_2 i) (Q2.hfix147_126_2 i) _)
      colCert_147_126_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_126_4 (hp : 4 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 4 (transLenTr ⟨126, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 4 (transLenTr ⟨126, by decide⟩ 4 hp)) T147_126
      hfix147_126 hinj147_126 hcardT147_126
      (fun i => conj_mem_of_fixedPoints _ _ (T147_126 i) (hfix147_126 i) _)
      ⟨147, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 4 hp) Q2.T147_126_2 Q2.hfix147_126_2 Q2.hinj147_126_2
      Q2.hcardT147_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_126_2 i) (Q2.hfix147_126_2 i) _)
      colCert_147_126_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_126_5 (hp : 5 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 5 (transLenTr ⟨126, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 5 (transLenTr ⟨126, by decide⟩ 5 hp)) T147_126
      hfix147_126 hinj147_126 hcardT147_126
      (fun i => conj_mem_of_fixedPoints _ _ (T147_126 i) (hfix147_126 i) _)
      ⟨147, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 5 hp) Q2.T147_126_2 Q2.hfix147_126_2 Q2.hinj147_126_2
      Q2.hcardT147_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_126_2 i) (Q2.hfix147_126_2 i) _)
      colCert_147_126_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_126_6 (hp : 6 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 6 (transLenTr ⟨126, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 6 (transLenTr ⟨126, by decide⟩ 6 hp)) T147_126
      hfix147_126 hinj147_126 hcardT147_126
      (fun i => conj_mem_of_fixedPoints _ _ (T147_126 i) (hfix147_126 i) _)
      ⟨147, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 6 hp) Q2.T147_126_2 Q2.hfix147_126_2 Q2.hinj147_126_2
      Q2.hcardT147_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_126_2 i) (Q2.hfix147_126_2 i) _)
      colCert_147_126_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_126_7 (hp : 7 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 7 (transLenTr ⟨126, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 7 (transLenTr ⟨126, by decide⟩ 7 hp)) T147_126
      hfix147_126 hinj147_126 hcardT147_126
      (fun i => conj_mem_of_fixedPoints _ _ (T147_126 i) (hfix147_126 i) _)
      ⟨147, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 7 hp) Q2.T147_126_2 Q2.hfix147_126_2 Q2.hinj147_126_2
      Q2.hcardT147_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_126_2 i) (Q2.hfix147_126_2 i) _)
      colCert_147_126_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_126_8 (hp : 8 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 8 (transLenTr ⟨126, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 8 (transLenTr ⟨126, by decide⟩ 8 hp)) T147_126
      hfix147_126 hinj147_126 hcardT147_126
      (fun i => conj_mem_of_fixedPoints _ _ (T147_126 i) (hfix147_126 i) _)
      ⟨147, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 8 hp) Q2.T147_126_2 Q2.hfix147_126_2 Q2.hinj147_126_2
      Q2.hcardT147_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_126_2 i) (Q2.hfix147_126_2 i) _)
      colCert_147_126_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_126_9 (hp : 9 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 9 (transLenTr ⟨126, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 9 (transLenTr ⟨126, by decide⟩ 9 hp)) T147_126
      hfix147_126 hinj147_126 hcardT147_126
      (fun i => conj_mem_of_fixedPoints _ _ (T147_126 i) (hfix147_126 i) _)
      ⟨147, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 9 hp) Q2.T147_126_2 Q2.hfix147_126_2 Q2.hinj147_126_2
      Q2.hcardT147_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_126_2 i) (Q2.hfix147_126_2 i) _)
      colCert_147_126_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_126_10 (hp : 10 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 10 (transLenTr ⟨126, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 10 (transLenTr ⟨126, by decide⟩ 10 hp)) T147_126
      hfix147_126 hinj147_126 hcardT147_126
      (fun i => conj_mem_of_fixedPoints _ _ (T147_126 i) (hfix147_126 i) _)
      ⟨147, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 10 hp) Q2.T147_126_2 Q2.hfix147_126_2 Q2.hinj147_126_2
      Q2.hcardT147_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_126_2 i) (Q2.hfix147_126_2 i) _)
      colCert_147_126_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_126_11 (hp : 11 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 11 (transLenTr ⟨126, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 11 (transLenTr ⟨126, by decide⟩ 11 hp)) T147_126
      hfix147_126 hinj147_126 hcardT147_126
      (fun i => conj_mem_of_fixedPoints _ _ (T147_126 i) (hfix147_126 i) _)
      ⟨147, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 11 hp) Q2.T147_126_2 Q2.hfix147_126_2 Q2.hinj147_126_2
      Q2.hcardT147_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_126_2 i) (Q2.hfix147_126_2 i) _)
      colCert_147_126_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_126_12 (hp : 12 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 12 (transLenTr ⟨126, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 12 (transLenTr ⟨126, by decide⟩ 12 hp)) T147_126
      hfix147_126 hinj147_126 hcardT147_126
      (fun i => conj_mem_of_fixedPoints _ _ (T147_126 i) (hfix147_126 i) _)
      ⟨147, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 12 hp) Q2.T147_126_2 Q2.hfix147_126_2 Q2.hinj147_126_2
      Q2.hcardT147_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_126_2 i) (Q2.hfix147_126_2 i) _)
      colCert_147_126_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_126_13 (hp : 13 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 13 (transLenTr ⟨126, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 13 (transLenTr ⟨126, by decide⟩ 13 hp)) T147_126
      hfix147_126 hinj147_126 hcardT147_126
      (fun i => conj_mem_of_fixedPoints _ _ (T147_126 i) (hfix147_126 i) _)
      ⟨147, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 13 hp) Q2.T147_126_2 Q2.hfix147_126_2 Q2.hinj147_126_2
      Q2.hcardT147_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_126_2 i) (Q2.hfix147_126_2 i) _)
      colCert_147_126_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_126_14 (hp : 14 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 14 (transLenTr ⟨126, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 14 (transLenTr ⟨126, by decide⟩ 14 hp)) T147_126
      hfix147_126 hinj147_126 hcardT147_126
      (fun i => conj_mem_of_fixedPoints _ _ (T147_126 i) (hfix147_126 i) _)
      ⟨147, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 14 hp) Q2.T147_126_2 Q2.hfix147_126_2 Q2.hinj147_126_2
      Q2.hcardT147_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_126_2 i) (Q2.hfix147_126_2 i) _)
      colCert_147_126_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_126_15 (hp : 15 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 15 (transLenTr ⟨126, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 15 (transLenTr ⟨126, by decide⟩ 15 hp)) T147_126
      hfix147_126 hinj147_126 hcardT147_126
      (fun i => conj_mem_of_fixedPoints _ _ (T147_126 i) (hfix147_126 i) _)
      ⟨147, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 15 hp) Q2.T147_126_2 Q2.hfix147_126_2 Q2.hinj147_126_2
      Q2.hcardT147_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_126_2 i) (Q2.hfix147_126_2 i) _)
      colCert_147_126_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_126_16 (hp : 16 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 16 (transLenTr ⟨126, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 16 (transLenTr ⟨126, by decide⟩ 16 hp)) T147_126
      hfix147_126 hinj147_126 hcardT147_126
      (fun i => conj_mem_of_fixedPoints _ _ (T147_126 i) (hfix147_126 i) _)
      ⟨147, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 16 hp) Q2.T147_126_2 Q2.hfix147_126_2 Q2.hinj147_126_2
      Q2.hcardT147_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_126_2 i) (Q2.hfix147_126_2 i) _)
      colCert_147_126_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_126_17 (hp : 17 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 17 (transLenTr ⟨126, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 17 (transLenTr ⟨126, by decide⟩ 17 hp)) T147_126
      hfix147_126 hinj147_126 hcardT147_126
      (fun i => conj_mem_of_fixedPoints _ _ (T147_126 i) (hfix147_126 i) _)
      ⟨147, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 17 hp) Q2.T147_126_2 Q2.hfix147_126_2 Q2.hinj147_126_2
      Q2.hcardT147_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_126_2 i) (Q2.hfix147_126_2 i) _)
      colCert_147_126_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_126_18 (hp : 18 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 18 (transLenTr ⟨126, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 18 (transLenTr ⟨126, by decide⟩ 18 hp)) T147_126
      hfix147_126 hinj147_126 hcardT147_126
      (fun i => conj_mem_of_fixedPoints _ _ (T147_126 i) (hfix147_126 i) _)
      ⟨147, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 18 hp) Q2.T147_126_2 Q2.hfix147_126_2 Q2.hinj147_126_2
      Q2.hcardT147_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_126_2 i) (Q2.hfix147_126_2 i) _)
      colCert_147_126_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_126_19 (hp : 19 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 19 (transLenTr ⟨126, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 19 (transLenTr ⟨126, by decide⟩ 19 hp)) T147_126
      hfix147_126 hinj147_126 hcardT147_126
      (fun i => conj_mem_of_fixedPoints _ _ (T147_126 i) (hfix147_126 i) _)
      ⟨147, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 19 hp) Q2.T147_126_2 Q2.hfix147_126_2 Q2.hinj147_126_2
      Q2.hcardT147_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_126_2 i) (Q2.hfix147_126_2 i) _)
      colCert_147_126_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_126_20 (hp : 20 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 20 (transLenTr ⟨126, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 20 (transLenTr ⟨126, by decide⟩ 20 hp)) T147_126
      hfix147_126 hinj147_126 hcardT147_126
      (fun i => conj_mem_of_fixedPoints _ _ (T147_126 i) (hfix147_126 i) _)
      ⟨147, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 20 hp) Q2.T147_126_2 Q2.hfix147_126_2 Q2.hinj147_126_2
      Q2.hcardT147_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_126_2 i) (Q2.hfix147_126_2 i) _)
      colCert_147_126_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_126_21 (hp : 21 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 21 (transLenTr ⟨126, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 21 (transLenTr ⟨126, by decide⟩ 21 hp)) T147_126
      hfix147_126 hinj147_126 hcardT147_126
      (fun i => conj_mem_of_fixedPoints _ _ (T147_126 i) (hfix147_126 i) _)
      ⟨147, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 21 hp) Q2.T147_126_2 Q2.hfix147_126_2 Q2.hinj147_126_2
      Q2.hcardT147_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_126_2 i) (Q2.hfix147_126_2 i) _)
      colCert_147_126_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_126_22 (hp : 22 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 22 (transLenTr ⟨126, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 22 (transLenTr ⟨126, by decide⟩ 22 hp)) T147_126
      hfix147_126 hinj147_126 hcardT147_126
      (fun i => conj_mem_of_fixedPoints _ _ (T147_126 i) (hfix147_126 i) _)
      ⟨147, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 22 hp) Q2.T147_126_2 Q2.hfix147_126_2 Q2.hinj147_126_2
      Q2.hcardT147_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_126_2 i) (Q2.hfix147_126_2 i) _)
      colCert_147_126_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_126_23 (hp : 23 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 23 (transLenTr ⟨126, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 23 (transLenTr ⟨126, by decide⟩ 23 hp)) T147_126
      hfix147_126 hinj147_126 hcardT147_126
      (fun i => conj_mem_of_fixedPoints _ _ (T147_126 i) (hfix147_126 i) _)
      ⟨147, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 23 hp) Q2.T147_126_2 Q2.hfix147_126_2 Q2.hinj147_126_2
      Q2.hcardT147_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_126_2 i) (Q2.hfix147_126_2 i) _)
      colCert_147_126_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_126_24 (hp : 24 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 24 (transLenTr ⟨126, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 24 (transLenTr ⟨126, by decide⟩ 24 hp)) T147_126
      hfix147_126 hinj147_126 hcardT147_126
      (fun i => conj_mem_of_fixedPoints _ _ (T147_126 i) (hfix147_126 i) _)
      ⟨147, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 24 hp) Q2.T147_126_2 Q2.hfix147_126_2 Q2.hinj147_126_2
      Q2.hcardT147_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_126_2 i) (Q2.hfix147_126_2 i) _)
      colCert_147_126_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_127_0 (hp : 0 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 0 (transLenTr ⟨127, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 0 (transLenTr ⟨127, by decide⟩ 0 hp)) T147_127
      hfix147_127 hinj147_127 hcardT147_127
      (fun i => conj_mem_of_fixedPoints _ _ (T147_127 i) (hfix147_127 i) _)
      ⟨147, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 0 hp) Q2.T147_127_2 Q2.hfix147_127_2 Q2.hinj147_127_2
      Q2.hcardT147_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_127_2 i) (Q2.hfix147_127_2 i) _)
      colCert_147_127_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_127_1 (hp : 1 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 1 (transLenTr ⟨127, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 1 (transLenTr ⟨127, by decide⟩ 1 hp)) T147_127
      hfix147_127 hinj147_127 hcardT147_127
      (fun i => conj_mem_of_fixedPoints _ _ (T147_127 i) (hfix147_127 i) _)
      ⟨147, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 1 hp) Q2.T147_127_2 Q2.hfix147_127_2 Q2.hinj147_127_2
      Q2.hcardT147_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_127_2 i) (Q2.hfix147_127_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨127, by decide⟩ 1 (transLenTr ⟨127, by decide⟩ 1 hp) : ↥(reps ⟨127, by decide⟩)) : Coordinate 1)
        T147_127 = colFn colCertDiv_147_127_1.D1 (m := 1) from colCertDiv_147_127_1.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨127, by decide⟩ 1 hp : ↥(Q2.reps ⟨127, by decide⟩)) : Coordinate 2)
        Q2.T147_127_2 = colFn colCertDiv_147_127_1.D2 (m := 1) from colCertDiv_147_127_1.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_127_1_match


theorem leaf_147_127_2 (hp : 2 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 2 (transLenTr ⟨127, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 2 (transLenTr ⟨127, by decide⟩ 2 hp)) T147_127
      hfix147_127 hinj147_127 hcardT147_127
      (fun i => conj_mem_of_fixedPoints _ _ (T147_127 i) (hfix147_127 i) _)
      ⟨147, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 2 hp) Q2.T147_127_2 Q2.hfix147_127_2 Q2.hinj147_127_2
      Q2.hcardT147_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_127_2 i) (Q2.hfix147_127_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨127, by decide⟩ 2 (transLenTr ⟨127, by decide⟩ 2 hp) : ↥(reps ⟨127, by decide⟩)) : Coordinate 1)
        T147_127 = colFn colCertDiv_147_127_2.D1 (m := 1) from colCertDiv_147_127_2.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨127, by decide⟩ 2 hp : ↥(Q2.reps ⟨127, by decide⟩)) : Coordinate 2)
        Q2.T147_127_2 = colFn colCertDiv_147_127_2.D2 (m := 1) from colCertDiv_147_127_2.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_127_2_match


theorem leaf_147_127_3 (hp : 3 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 3 (transLenTr ⟨127, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 3 (transLenTr ⟨127, by decide⟩ 3 hp)) T147_127
      hfix147_127 hinj147_127 hcardT147_127
      (fun i => conj_mem_of_fixedPoints _ _ (T147_127 i) (hfix147_127 i) _)
      ⟨147, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 3 hp) Q2.T147_127_2 Q2.hfix147_127_2 Q2.hinj147_127_2
      Q2.hcardT147_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_127_2 i) (Q2.hfix147_127_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨127, by decide⟩ 3 (transLenTr ⟨127, by decide⟩ 3 hp) : ↥(reps ⟨127, by decide⟩)) : Coordinate 1)
        T147_127 = colFn colCertDiv_147_127_3.D1 (m := 1) from colCertDiv_147_127_3.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨127, by decide⟩ 3 hp : ↥(Q2.reps ⟨127, by decide⟩)) : Coordinate 2)
        Q2.T147_127_2 = colFn colCertDiv_147_127_3.D2 (m := 1) from colCertDiv_147_127_3.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_127_3_match


theorem leaf_147_127_4 (hp : 4 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 4 (transLenTr ⟨127, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 4 (transLenTr ⟨127, by decide⟩ 4 hp)) T147_127
      hfix147_127 hinj147_127 hcardT147_127
      (fun i => conj_mem_of_fixedPoints _ _ (T147_127 i) (hfix147_127 i) _)
      ⟨147, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 4 hp) Q2.T147_127_2 Q2.hfix147_127_2 Q2.hinj147_127_2
      Q2.hcardT147_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_127_2 i) (Q2.hfix147_127_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨127, by decide⟩ 4 (transLenTr ⟨127, by decide⟩ 4 hp) : ↥(reps ⟨127, by decide⟩)) : Coordinate 1)
        T147_127 = colFn colCertDiv_147_127_4.D1 (m := 1) from colCertDiv_147_127_4.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨127, by decide⟩ 4 hp : ↥(Q2.reps ⟨127, by decide⟩)) : Coordinate 2)
        Q2.T147_127_2 = colFn colCertDiv_147_127_4.D2 (m := 1) from colCertDiv_147_127_4.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_127_4_match


theorem leaf_147_127_5 (hp : 5 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 5 (transLenTr ⟨127, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 5 (transLenTr ⟨127, by decide⟩ 5 hp)) T147_127
      hfix147_127 hinj147_127 hcardT147_127
      (fun i => conj_mem_of_fixedPoints _ _ (T147_127 i) (hfix147_127 i) _)
      ⟨147, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 5 hp) Q2.T147_127_2 Q2.hfix147_127_2 Q2.hinj147_127_2
      Q2.hcardT147_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_127_2 i) (Q2.hfix147_127_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨127, by decide⟩ 5 (transLenTr ⟨127, by decide⟩ 5 hp) : ↥(reps ⟨127, by decide⟩)) : Coordinate 1)
        T147_127 = colFn colCertDiv_147_127_5.D1 (m := 1) from colCertDiv_147_127_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨127, by decide⟩ 5 hp : ↥(Q2.reps ⟨127, by decide⟩)) : Coordinate 2)
        Q2.T147_127_2 = colFn colCertDiv_147_127_5.D2 (m := 1) from colCertDiv_147_127_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_127_5_match


theorem leaf_147_127_6 (hp : 6 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 6 (transLenTr ⟨127, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 6 (transLenTr ⟨127, by decide⟩ 6 hp)) T147_127
      hfix147_127 hinj147_127 hcardT147_127
      (fun i => conj_mem_of_fixedPoints _ _ (T147_127 i) (hfix147_127 i) _)
      ⟨147, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 6 hp) Q2.T147_127_2 Q2.hfix147_127_2 Q2.hinj147_127_2
      Q2.hcardT147_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_127_2 i) (Q2.hfix147_127_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨127, by decide⟩ 6 (transLenTr ⟨127, by decide⟩ 6 hp) : ↥(reps ⟨127, by decide⟩)) : Coordinate 1)
        T147_127 = colFn colCertDiv_147_127_6.D1 (m := 1) from colCertDiv_147_127_6.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨127, by decide⟩ 6 hp : ↥(Q2.reps ⟨127, by decide⟩)) : Coordinate 2)
        Q2.T147_127_2 = colFn colCertDiv_147_127_6.D2 (m := 1) from colCertDiv_147_127_6.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_127_6_match


theorem leaf_147_127_7 (hp : 7 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 7 (transLenTr ⟨127, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 7 (transLenTr ⟨127, by decide⟩ 7 hp)) T147_127
      hfix147_127 hinj147_127 hcardT147_127
      (fun i => conj_mem_of_fixedPoints _ _ (T147_127 i) (hfix147_127 i) _)
      ⟨147, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 7 hp) Q2.T147_127_2 Q2.hfix147_127_2 Q2.hinj147_127_2
      Q2.hcardT147_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_127_2 i) (Q2.hfix147_127_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨127, by decide⟩ 7 (transLenTr ⟨127, by decide⟩ 7 hp) : ↥(reps ⟨127, by decide⟩)) : Coordinate 1)
        T147_127 = colFn colCertDiv_147_127_7.D1 (m := 1) from colCertDiv_147_127_7.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨127, by decide⟩ 7 hp : ↥(Q2.reps ⟨127, by decide⟩)) : Coordinate 2)
        Q2.T147_127_2 = colFn colCertDiv_147_127_7.D2 (m := 1) from colCertDiv_147_127_7.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_127_7_match


theorem leaf_147_127_8 (hp : 8 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 8 (transLenTr ⟨127, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 8 (transLenTr ⟨127, by decide⟩ 8 hp)) T147_127
      hfix147_127 hinj147_127 hcardT147_127
      (fun i => conj_mem_of_fixedPoints _ _ (T147_127 i) (hfix147_127 i) _)
      ⟨147, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 8 hp) Q2.T147_127_2 Q2.hfix147_127_2 Q2.hinj147_127_2
      Q2.hcardT147_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_127_2 i) (Q2.hfix147_127_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨127, by decide⟩ 8 (transLenTr ⟨127, by decide⟩ 8 hp) : ↥(reps ⟨127, by decide⟩)) : Coordinate 1)
        T147_127 = colFn colCertDiv_147_127_8.D1 (m := 1) from colCertDiv_147_127_8.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨127, by decide⟩ 8 hp : ↥(Q2.reps ⟨127, by decide⟩)) : Coordinate 2)
        Q2.T147_127_2 = colFn colCertDiv_147_127_8.D2 (m := 1) from colCertDiv_147_127_8.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_127_8_match


theorem leaf_147_127_9 (hp : 9 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 9 (transLenTr ⟨127, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 9 (transLenTr ⟨127, by decide⟩ 9 hp)) T147_127
      hfix147_127 hinj147_127 hcardT147_127
      (fun i => conj_mem_of_fixedPoints _ _ (T147_127 i) (hfix147_127 i) _)
      ⟨147, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 9 hp) Q2.T147_127_2 Q2.hfix147_127_2 Q2.hinj147_127_2
      Q2.hcardT147_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_127_2 i) (Q2.hfix147_127_2 i) _)
      colCert_147_127_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_127_10 (hp : 10 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 10 (transLenTr ⟨127, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 10 (transLenTr ⟨127, by decide⟩ 10 hp)) T147_127
      hfix147_127 hinj147_127 hcardT147_127
      (fun i => conj_mem_of_fixedPoints _ _ (T147_127 i) (hfix147_127 i) _)
      ⟨147, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 10 hp) Q2.T147_127_2 Q2.hfix147_127_2 Q2.hinj147_127_2
      Q2.hcardT147_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_127_2 i) (Q2.hfix147_127_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨127, by decide⟩ 10 (transLenTr ⟨127, by decide⟩ 10 hp) : ↥(reps ⟨127, by decide⟩)) : Coordinate 1)
        T147_127 = colFn colCertDiv_147_127_10.D1 (m := 1) from colCertDiv_147_127_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨127, by decide⟩ 10 hp : ↥(Q2.reps ⟨127, by decide⟩)) : Coordinate 2)
        Q2.T147_127_2 = colFn colCertDiv_147_127_10.D2 (m := 1) from colCertDiv_147_127_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_127_10_match


theorem leaf_147_127_11 (hp : 11 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 11 (transLenTr ⟨127, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 11 (transLenTr ⟨127, by decide⟩ 11 hp)) T147_127
      hfix147_127 hinj147_127 hcardT147_127
      (fun i => conj_mem_of_fixedPoints _ _ (T147_127 i) (hfix147_127 i) _)
      ⟨147, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 11 hp) Q2.T147_127_2 Q2.hfix147_127_2 Q2.hinj147_127_2
      Q2.hcardT147_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_127_2 i) (Q2.hfix147_127_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨127, by decide⟩ 11 (transLenTr ⟨127, by decide⟩ 11 hp) : ↥(reps ⟨127, by decide⟩)) : Coordinate 1)
        T147_127 = colFn colCertDiv_147_127_11.D1 (m := 1) from colCertDiv_147_127_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨127, by decide⟩ 11 hp : ↥(Q2.reps ⟨127, by decide⟩)) : Coordinate 2)
        Q2.T147_127_2 = colFn colCertDiv_147_127_11.D2 (m := 1) from colCertDiv_147_127_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_127_11_match


theorem leaf_147_127_12 (hp : 12 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 12 (transLenTr ⟨127, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 12 (transLenTr ⟨127, by decide⟩ 12 hp)) T147_127
      hfix147_127 hinj147_127 hcardT147_127
      (fun i => conj_mem_of_fixedPoints _ _ (T147_127 i) (hfix147_127 i) _)
      ⟨147, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 12 hp) Q2.T147_127_2 Q2.hfix147_127_2 Q2.hinj147_127_2
      Q2.hcardT147_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_127_2 i) (Q2.hfix147_127_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨127, by decide⟩ 12 (transLenTr ⟨127, by decide⟩ 12 hp) : ↥(reps ⟨127, by decide⟩)) : Coordinate 1)
        T147_127 = colFn colCertDiv_147_127_12.D1 (m := 1) from colCertDiv_147_127_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨127, by decide⟩ 12 hp : ↥(Q2.reps ⟨127, by decide⟩)) : Coordinate 2)
        Q2.T147_127_2 = colFn colCertDiv_147_127_12.D2 (m := 1) from colCertDiv_147_127_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_127_12_match


theorem leaf_147_127_13 (hp : 13 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 13 (transLenTr ⟨127, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 13 (transLenTr ⟨127, by decide⟩ 13 hp)) T147_127
      hfix147_127 hinj147_127 hcardT147_127
      (fun i => conj_mem_of_fixedPoints _ _ (T147_127 i) (hfix147_127 i) _)
      ⟨147, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 13 hp) Q2.T147_127_2 Q2.hfix147_127_2 Q2.hinj147_127_2
      Q2.hcardT147_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_127_2 i) (Q2.hfix147_127_2 i) _)
      colCert_147_127_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_127_14 (hp : 14 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 14 (transLenTr ⟨127, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 14 (transLenTr ⟨127, by decide⟩ 14 hp)) T147_127
      hfix147_127 hinj147_127 hcardT147_127
      (fun i => conj_mem_of_fixedPoints _ _ (T147_127 i) (hfix147_127 i) _)
      ⟨147, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 14 hp) Q2.T147_127_2 Q2.hfix147_127_2 Q2.hinj147_127_2
      Q2.hcardT147_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_127_2 i) (Q2.hfix147_127_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨127, by decide⟩ 14 (transLenTr ⟨127, by decide⟩ 14 hp) : ↥(reps ⟨127, by decide⟩)) : Coordinate 1)
        T147_127 = colFn colCertDiv_147_127_14.D1 (m := 1) from colCertDiv_147_127_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨127, by decide⟩ 14 hp : ↥(Q2.reps ⟨127, by decide⟩)) : Coordinate 2)
        Q2.T147_127_2 = colFn colCertDiv_147_127_14.D2 (m := 1) from colCertDiv_147_127_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_127_14_match


theorem leaf_147_127_15 (hp : 15 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 15 (transLenTr ⟨127, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 15 (transLenTr ⟨127, by decide⟩ 15 hp)) T147_127
      hfix147_127 hinj147_127 hcardT147_127
      (fun i => conj_mem_of_fixedPoints _ _ (T147_127 i) (hfix147_127 i) _)
      ⟨147, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 15 hp) Q2.T147_127_2 Q2.hfix147_127_2 Q2.hinj147_127_2
      Q2.hcardT147_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_127_2 i) (Q2.hfix147_127_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨127, by decide⟩ 15 (transLenTr ⟨127, by decide⟩ 15 hp) : ↥(reps ⟨127, by decide⟩)) : Coordinate 1)
        T147_127 = colFn colCertDiv_147_127_15.D1 (m := 1) from colCertDiv_147_127_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨127, by decide⟩ 15 hp : ↥(Q2.reps ⟨127, by decide⟩)) : Coordinate 2)
        Q2.T147_127_2 = colFn colCertDiv_147_127_15.D2 (m := 1) from colCertDiv_147_127_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_127_15_match


theorem leaf_147_127_16 (hp : 16 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 16 (transLenTr ⟨127, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 16 (transLenTr ⟨127, by decide⟩ 16 hp)) T147_127
      hfix147_127 hinj147_127 hcardT147_127
      (fun i => conj_mem_of_fixedPoints _ _ (T147_127 i) (hfix147_127 i) _)
      ⟨147, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 16 hp) Q2.T147_127_2 Q2.hfix147_127_2 Q2.hinj147_127_2
      Q2.hcardT147_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_127_2 i) (Q2.hfix147_127_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨127, by decide⟩ 16 (transLenTr ⟨127, by decide⟩ 16 hp) : ↥(reps ⟨127, by decide⟩)) : Coordinate 1)
        T147_127 = colFn colCertDiv_147_127_16.D1 (m := 1) from colCertDiv_147_127_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨127, by decide⟩ 16 hp : ↥(Q2.reps ⟨127, by decide⟩)) : Coordinate 2)
        Q2.T147_127_2 = colFn colCertDiv_147_127_16.D2 (m := 1) from colCertDiv_147_127_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_127_16_match


theorem leaf_147_127_17 (hp : 17 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 17 (transLenTr ⟨127, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 17 (transLenTr ⟨127, by decide⟩ 17 hp)) T147_127
      hfix147_127 hinj147_127 hcardT147_127
      (fun i => conj_mem_of_fixedPoints _ _ (T147_127 i) (hfix147_127 i) _)
      ⟨147, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 17 hp) Q2.T147_127_2 Q2.hfix147_127_2 Q2.hinj147_127_2
      Q2.hcardT147_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_127_2 i) (Q2.hfix147_127_2 i) _)
      colCert_147_127_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_127_18 (hp : 18 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 18 (transLenTr ⟨127, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 18 (transLenTr ⟨127, by decide⟩ 18 hp)) T147_127
      hfix147_127 hinj147_127 hcardT147_127
      (fun i => conj_mem_of_fixedPoints _ _ (T147_127 i) (hfix147_127 i) _)
      ⟨147, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 18 hp) Q2.T147_127_2 Q2.hfix147_127_2 Q2.hinj147_127_2
      Q2.hcardT147_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_127_2 i) (Q2.hfix147_127_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨127, by decide⟩ 18 (transLenTr ⟨127, by decide⟩ 18 hp) : ↥(reps ⟨127, by decide⟩)) : Coordinate 1)
        T147_127 = colFn colCertDiv_147_127_18.D1 (m := 1) from colCertDiv_147_127_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨127, by decide⟩ 18 hp : ↥(Q2.reps ⟨127, by decide⟩)) : Coordinate 2)
        Q2.T147_127_2 = colFn colCertDiv_147_127_18.D2 (m := 1) from colCertDiv_147_127_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_127_18_match


theorem leaf_147_127_19 (hp : 19 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 19 (transLenTr ⟨127, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 19 (transLenTr ⟨127, by decide⟩ 19 hp)) T147_127
      hfix147_127 hinj147_127 hcardT147_127
      (fun i => conj_mem_of_fixedPoints _ _ (T147_127 i) (hfix147_127 i) _)
      ⟨147, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 19 hp) Q2.T147_127_2 Q2.hfix147_127_2 Q2.hinj147_127_2
      Q2.hcardT147_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_127_2 i) (Q2.hfix147_127_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨127, by decide⟩ 19 (transLenTr ⟨127, by decide⟩ 19 hp) : ↥(reps ⟨127, by decide⟩)) : Coordinate 1)
        T147_127 = colFn colCertDiv_147_127_19.D1 (m := 1) from colCertDiv_147_127_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨127, by decide⟩ 19 hp : ↥(Q2.reps ⟨127, by decide⟩)) : Coordinate 2)
        Q2.T147_127_2 = colFn colCertDiv_147_127_19.D2 (m := 1) from colCertDiv_147_127_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_127_19_match


theorem leaf_147_127_20 (hp : 20 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 20 (transLenTr ⟨127, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 20 (transLenTr ⟨127, by decide⟩ 20 hp)) T147_127
      hfix147_127 hinj147_127 hcardT147_127
      (fun i => conj_mem_of_fixedPoints _ _ (T147_127 i) (hfix147_127 i) _)
      ⟨147, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 20 hp) Q2.T147_127_2 Q2.hfix147_127_2 Q2.hinj147_127_2
      Q2.hcardT147_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_127_2 i) (Q2.hfix147_127_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨127, by decide⟩ 20 (transLenTr ⟨127, by decide⟩ 20 hp) : ↥(reps ⟨127, by decide⟩)) : Coordinate 1)
        T147_127 = colFn colCertDiv_147_127_20.D1 (m := 1) from colCertDiv_147_127_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨127, by decide⟩ 20 hp : ↥(Q2.reps ⟨127, by decide⟩)) : Coordinate 2)
        Q2.T147_127_2 = colFn colCertDiv_147_127_20.D2 (m := 1) from colCertDiv_147_127_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_127_20_match


theorem leaf_147_127_21 (hp : 21 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 21 (transLenTr ⟨127, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 21 (transLenTr ⟨127, by decide⟩ 21 hp)) T147_127
      hfix147_127 hinj147_127 hcardT147_127
      (fun i => conj_mem_of_fixedPoints _ _ (T147_127 i) (hfix147_127 i) _)
      ⟨147, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 21 hp) Q2.T147_127_2 Q2.hfix147_127_2 Q2.hinj147_127_2
      Q2.hcardT147_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_127_2 i) (Q2.hfix147_127_2 i) _)
      colCert_147_127_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_127_22 (hp : 22 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 22 (transLenTr ⟨127, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 22 (transLenTr ⟨127, by decide⟩ 22 hp)) T147_127
      hfix147_127 hinj147_127 hcardT147_127
      (fun i => conj_mem_of_fixedPoints _ _ (T147_127 i) (hfix147_127 i) _)
      ⟨147, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 22 hp) Q2.T147_127_2 Q2.hfix147_127_2 Q2.hinj147_127_2
      Q2.hcardT147_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_127_2 i) (Q2.hfix147_127_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨127, by decide⟩ 22 (transLenTr ⟨127, by decide⟩ 22 hp) : ↥(reps ⟨127, by decide⟩)) : Coordinate 1)
        T147_127 = colFn colCertDiv_147_127_22.D1 (m := 1) from colCertDiv_147_127_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨127, by decide⟩ 22 hp : ↥(Q2.reps ⟨127, by decide⟩)) : Coordinate 2)
        Q2.T147_127_2 = colFn colCertDiv_147_127_22.D2 (m := 1) from colCertDiv_147_127_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_127_22_match


theorem leaf_147_127_23 (hp : 23 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 23 (transLenTr ⟨127, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 23 (transLenTr ⟨127, by decide⟩ 23 hp)) T147_127
      hfix147_127 hinj147_127 hcardT147_127
      (fun i => conj_mem_of_fixedPoints _ _ (T147_127 i) (hfix147_127 i) _)
      ⟨147, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 23 hp) Q2.T147_127_2 Q2.hfix147_127_2 Q2.hinj147_127_2
      Q2.hcardT147_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_127_2 i) (Q2.hfix147_127_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨127, by decide⟩ 23 (transLenTr ⟨127, by decide⟩ 23 hp) : ↥(reps ⟨127, by decide⟩)) : Coordinate 1)
        T147_127 = colFn colCertDiv_147_127_23.D1 (m := 1) from colCertDiv_147_127_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨127, by decide⟩ 23 hp : ↥(Q2.reps ⟨127, by decide⟩)) : Coordinate 2)
        Q2.T147_127_2 = colFn colCertDiv_147_127_23.D2 (m := 1) from colCertDiv_147_127_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_127_23_match


theorem leaf_147_127_24 (hp : 24 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 24 (transLenTr ⟨127, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 24 (transLenTr ⟨127, by decide⟩ 24 hp)) T147_127
      hfix147_127 hinj147_127 hcardT147_127
      (fun i => conj_mem_of_fixedPoints _ _ (T147_127 i) (hfix147_127 i) _)
      ⟨147, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 24 hp) Q2.T147_127_2 Q2.hfix147_127_2 Q2.hinj147_127_2
      Q2.hcardT147_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_127_2 i) (Q2.hfix147_127_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨127, by decide⟩ 24 (transLenTr ⟨127, by decide⟩ 24 hp) : ↥(reps ⟨127, by decide⟩)) : Coordinate 1)
        T147_127 = colFn colCertDiv_147_127_24.D1 (m := 1) from colCertDiv_147_127_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨127, by decide⟩ 24 hp : ↥(Q2.reps ⟨127, by decide⟩)) : Coordinate 2)
        Q2.T147_127_2 = colFn colCertDiv_147_127_24.D2 (m := 1) from colCertDiv_147_127_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_127_24_match


theorem leaf_147_128_0 (hp : 0 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 0 (transLenTr ⟨128, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 0 (transLenTr ⟨128, by decide⟩ 0 hp)) T147_128
      hfix147_128 hinj147_128 hcardT147_128
      (fun i => conj_mem_of_fixedPoints _ _ (T147_128 i) (hfix147_128 i) _)
      ⟨147, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 0 hp) Q2.T147_128_2 Q2.hfix147_128_2 Q2.hinj147_128_2
      Q2.hcardT147_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_128_2 i) (Q2.hfix147_128_2 i) _)
      colCert_147_128_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_128_1 (hp : 1 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 1 (transLenTr ⟨128, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 1 (transLenTr ⟨128, by decide⟩ 1 hp)) T147_128
      hfix147_128 hinj147_128 hcardT147_128
      (fun i => conj_mem_of_fixedPoints _ _ (T147_128 i) (hfix147_128 i) _)
      ⟨147, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 1 hp) Q2.T147_128_2 Q2.hfix147_128_2 Q2.hinj147_128_2
      Q2.hcardT147_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_128_2 i) (Q2.hfix147_128_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨128, by decide⟩ 1 (transLenTr ⟨128, by decide⟩ 1 hp) : ↥(reps ⟨128, by decide⟩)) : Coordinate 1)
        T147_128 = colFn colCertDiv_147_128_1.D1 (m := 1) from colCertDiv_147_128_1.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨128, by decide⟩ 1 hp : ↥(Q2.reps ⟨128, by decide⟩)) : Coordinate 2)
        Q2.T147_128_2 = colFn colCertDiv_147_128_1.D2 (m := 1) from colCertDiv_147_128_1.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_128_1_match


theorem leaf_147_128_2 (hp : 2 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 2 (transLenTr ⟨128, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 2 (transLenTr ⟨128, by decide⟩ 2 hp)) T147_128
      hfix147_128 hinj147_128 hcardT147_128
      (fun i => conj_mem_of_fixedPoints _ _ (T147_128 i) (hfix147_128 i) _)
      ⟨147, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 2 hp) Q2.T147_128_2 Q2.hfix147_128_2 Q2.hinj147_128_2
      Q2.hcardT147_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_128_2 i) (Q2.hfix147_128_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨128, by decide⟩ 2 (transLenTr ⟨128, by decide⟩ 2 hp) : ↥(reps ⟨128, by decide⟩)) : Coordinate 1)
        T147_128 = colFn colCertDiv_147_128_2.D1 (m := 1) from colCertDiv_147_128_2.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨128, by decide⟩ 2 hp : ↥(Q2.reps ⟨128, by decide⟩)) : Coordinate 2)
        Q2.T147_128_2 = colFn colCertDiv_147_128_2.D2 (m := 1) from colCertDiv_147_128_2.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_128_2_match


theorem leaf_147_128_3 (hp : 3 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 3 (transLenTr ⟨128, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 3 (transLenTr ⟨128, by decide⟩ 3 hp)) T147_128
      hfix147_128 hinj147_128 hcardT147_128
      (fun i => conj_mem_of_fixedPoints _ _ (T147_128 i) (hfix147_128 i) _)
      ⟨147, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 3 hp) Q2.T147_128_2 Q2.hfix147_128_2 Q2.hinj147_128_2
      Q2.hcardT147_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_128_2 i) (Q2.hfix147_128_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨128, by decide⟩ 3 (transLenTr ⟨128, by decide⟩ 3 hp) : ↥(reps ⟨128, by decide⟩)) : Coordinate 1)
        T147_128 = colFn colCertDiv_147_128_3.D1 (m := 1) from colCertDiv_147_128_3.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨128, by decide⟩ 3 hp : ↥(Q2.reps ⟨128, by decide⟩)) : Coordinate 2)
        Q2.T147_128_2 = colFn colCertDiv_147_128_3.D2 (m := 1) from colCertDiv_147_128_3.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_128_3_match


theorem leaf_147_128_4 (hp : 4 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 4 (transLenTr ⟨128, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 4 (transLenTr ⟨128, by decide⟩ 4 hp)) T147_128
      hfix147_128 hinj147_128 hcardT147_128
      (fun i => conj_mem_of_fixedPoints _ _ (T147_128 i) (hfix147_128 i) _)
      ⟨147, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 4 hp) Q2.T147_128_2 Q2.hfix147_128_2 Q2.hinj147_128_2
      Q2.hcardT147_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_128_2 i) (Q2.hfix147_128_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨128, by decide⟩ 4 (transLenTr ⟨128, by decide⟩ 4 hp) : ↥(reps ⟨128, by decide⟩)) : Coordinate 1)
        T147_128 = colFn colCertDiv_147_128_4.D1 (m := 1) from colCertDiv_147_128_4.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨128, by decide⟩ 4 hp : ↥(Q2.reps ⟨128, by decide⟩)) : Coordinate 2)
        Q2.T147_128_2 = colFn colCertDiv_147_128_4.D2 (m := 1) from colCertDiv_147_128_4.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_128_4_match


theorem leaf_147_128_5 (hp : 5 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 5 (transLenTr ⟨128, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 5 (transLenTr ⟨128, by decide⟩ 5 hp)) T147_128
      hfix147_128 hinj147_128 hcardT147_128
      (fun i => conj_mem_of_fixedPoints _ _ (T147_128 i) (hfix147_128 i) _)
      ⟨147, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 5 hp) Q2.T147_128_2 Q2.hfix147_128_2 Q2.hinj147_128_2
      Q2.hcardT147_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_128_2 i) (Q2.hfix147_128_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨128, by decide⟩ 5 (transLenTr ⟨128, by decide⟩ 5 hp) : ↥(reps ⟨128, by decide⟩)) : Coordinate 1)
        T147_128 = colFn colCertDiv_147_128_5.D1 (m := 1) from colCertDiv_147_128_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨128, by decide⟩ 5 hp : ↥(Q2.reps ⟨128, by decide⟩)) : Coordinate 2)
        Q2.T147_128_2 = colFn colCertDiv_147_128_5.D2 (m := 1) from colCertDiv_147_128_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_128_5_match


theorem leaf_147_128_6 (hp : 6 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 6 (transLenTr ⟨128, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 6 (transLenTr ⟨128, by decide⟩ 6 hp)) T147_128
      hfix147_128 hinj147_128 hcardT147_128
      (fun i => conj_mem_of_fixedPoints _ _ (T147_128 i) (hfix147_128 i) _)
      ⟨147, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 6 hp) Q2.T147_128_2 Q2.hfix147_128_2 Q2.hinj147_128_2
      Q2.hcardT147_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_128_2 i) (Q2.hfix147_128_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨128, by decide⟩ 6 (transLenTr ⟨128, by decide⟩ 6 hp) : ↥(reps ⟨128, by decide⟩)) : Coordinate 1)
        T147_128 = colFn colCertDiv_147_128_6.D1 (m := 1) from colCertDiv_147_128_6.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨128, by decide⟩ 6 hp : ↥(Q2.reps ⟨128, by decide⟩)) : Coordinate 2)
        Q2.T147_128_2 = colFn colCertDiv_147_128_6.D2 (m := 1) from colCertDiv_147_128_6.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_128_6_match


theorem leaf_147_128_7 (hp : 7 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 7 (transLenTr ⟨128, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 7 (transLenTr ⟨128, by decide⟩ 7 hp)) T147_128
      hfix147_128 hinj147_128 hcardT147_128
      (fun i => conj_mem_of_fixedPoints _ _ (T147_128 i) (hfix147_128 i) _)
      ⟨147, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 7 hp) Q2.T147_128_2 Q2.hfix147_128_2 Q2.hinj147_128_2
      Q2.hcardT147_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_128_2 i) (Q2.hfix147_128_2 i) _)
      colCert_147_128_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_128_8 (hp : 8 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 8 (transLenTr ⟨128, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 8 (transLenTr ⟨128, by decide⟩ 8 hp)) T147_128
      hfix147_128 hinj147_128 hcardT147_128
      (fun i => conj_mem_of_fixedPoints _ _ (T147_128 i) (hfix147_128 i) _)
      ⟨147, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 8 hp) Q2.T147_128_2 Q2.hfix147_128_2 Q2.hinj147_128_2
      Q2.hcardT147_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_128_2 i) (Q2.hfix147_128_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨128, by decide⟩ 8 (transLenTr ⟨128, by decide⟩ 8 hp) : ↥(reps ⟨128, by decide⟩)) : Coordinate 1)
        T147_128 = colFn colCertDiv_147_128_8.D1 (m := 1) from colCertDiv_147_128_8.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨128, by decide⟩ 8 hp : ↥(Q2.reps ⟨128, by decide⟩)) : Coordinate 2)
        Q2.T147_128_2 = colFn colCertDiv_147_128_8.D2 (m := 1) from colCertDiv_147_128_8.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_128_8_match


theorem leaf_147_128_9 (hp : 9 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 9 (transLenTr ⟨128, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 9 (transLenTr ⟨128, by decide⟩ 9 hp)) T147_128
      hfix147_128 hinj147_128 hcardT147_128
      (fun i => conj_mem_of_fixedPoints _ _ (T147_128 i) (hfix147_128 i) _)
      ⟨147, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 9 hp) Q2.T147_128_2 Q2.hfix147_128_2 Q2.hinj147_128_2
      Q2.hcardT147_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_128_2 i) (Q2.hfix147_128_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨128, by decide⟩ 9 (transLenTr ⟨128, by decide⟩ 9 hp) : ↥(reps ⟨128, by decide⟩)) : Coordinate 1)
        T147_128 = colFn colCertDiv_147_128_9.D1 (m := 1) from colCertDiv_147_128_9.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨128, by decide⟩ 9 hp : ↥(Q2.reps ⟨128, by decide⟩)) : Coordinate 2)
        Q2.T147_128_2 = colFn colCertDiv_147_128_9.D2 (m := 1) from colCertDiv_147_128_9.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_128_9_match


theorem leaf_147_128_10 (hp : 10 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 10 (transLenTr ⟨128, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 10 (transLenTr ⟨128, by decide⟩ 10 hp)) T147_128
      hfix147_128 hinj147_128 hcardT147_128
      (fun i => conj_mem_of_fixedPoints _ _ (T147_128 i) (hfix147_128 i) _)
      ⟨147, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 10 hp) Q2.T147_128_2 Q2.hfix147_128_2 Q2.hinj147_128_2
      Q2.hcardT147_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_128_2 i) (Q2.hfix147_128_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨128, by decide⟩ 10 (transLenTr ⟨128, by decide⟩ 10 hp) : ↥(reps ⟨128, by decide⟩)) : Coordinate 1)
        T147_128 = colFn colCertDiv_147_128_10.D1 (m := 1) from colCertDiv_147_128_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨128, by decide⟩ 10 hp : ↥(Q2.reps ⟨128, by decide⟩)) : Coordinate 2)
        Q2.T147_128_2 = colFn colCertDiv_147_128_10.D2 (m := 1) from colCertDiv_147_128_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_128_10_match


theorem leaf_147_128_11 (hp : 11 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 11 (transLenTr ⟨128, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 11 (transLenTr ⟨128, by decide⟩ 11 hp)) T147_128
      hfix147_128 hinj147_128 hcardT147_128
      (fun i => conj_mem_of_fixedPoints _ _ (T147_128 i) (hfix147_128 i) _)
      ⟨147, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 11 hp) Q2.T147_128_2 Q2.hfix147_128_2 Q2.hinj147_128_2
      Q2.hcardT147_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_128_2 i) (Q2.hfix147_128_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨128, by decide⟩ 11 (transLenTr ⟨128, by decide⟩ 11 hp) : ↥(reps ⟨128, by decide⟩)) : Coordinate 1)
        T147_128 = colFn colCertDiv_147_128_11.D1 (m := 1) from colCertDiv_147_128_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨128, by decide⟩ 11 hp : ↥(Q2.reps ⟨128, by decide⟩)) : Coordinate 2)
        Q2.T147_128_2 = colFn colCertDiv_147_128_11.D2 (m := 1) from colCertDiv_147_128_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_128_11_match


theorem leaf_147_128_12 (hp : 12 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 12 (transLenTr ⟨128, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 12 (transLenTr ⟨128, by decide⟩ 12 hp)) T147_128
      hfix147_128 hinj147_128 hcardT147_128
      (fun i => conj_mem_of_fixedPoints _ _ (T147_128 i) (hfix147_128 i) _)
      ⟨147, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 12 hp) Q2.T147_128_2 Q2.hfix147_128_2 Q2.hinj147_128_2
      Q2.hcardT147_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_128_2 i) (Q2.hfix147_128_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨128, by decide⟩ 12 (transLenTr ⟨128, by decide⟩ 12 hp) : ↥(reps ⟨128, by decide⟩)) : Coordinate 1)
        T147_128 = colFn colCertDiv_147_128_12.D1 (m := 1) from colCertDiv_147_128_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨128, by decide⟩ 12 hp : ↥(Q2.reps ⟨128, by decide⟩)) : Coordinate 2)
        Q2.T147_128_2 = colFn colCertDiv_147_128_12.D2 (m := 1) from colCertDiv_147_128_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_128_12_match


theorem leaf_147_128_13 (hp : 13 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 13 (transLenTr ⟨128, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 13 (transLenTr ⟨128, by decide⟩ 13 hp)) T147_128
      hfix147_128 hinj147_128 hcardT147_128
      (fun i => conj_mem_of_fixedPoints _ _ (T147_128 i) (hfix147_128 i) _)
      ⟨147, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 13 hp) Q2.T147_128_2 Q2.hfix147_128_2 Q2.hinj147_128_2
      Q2.hcardT147_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_128_2 i) (Q2.hfix147_128_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨128, by decide⟩ 13 (transLenTr ⟨128, by decide⟩ 13 hp) : ↥(reps ⟨128, by decide⟩)) : Coordinate 1)
        T147_128 = colFn colCertDiv_147_128_13.D1 (m := 1) from colCertDiv_147_128_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨128, by decide⟩ 13 hp : ↥(Q2.reps ⟨128, by decide⟩)) : Coordinate 2)
        Q2.T147_128_2 = colFn colCertDiv_147_128_13.D2 (m := 1) from colCertDiv_147_128_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_128_13_match


theorem leaf_147_128_14 (hp : 14 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 14 (transLenTr ⟨128, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 14 (transLenTr ⟨128, by decide⟩ 14 hp)) T147_128
      hfix147_128 hinj147_128 hcardT147_128
      (fun i => conj_mem_of_fixedPoints _ _ (T147_128 i) (hfix147_128 i) _)
      ⟨147, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 14 hp) Q2.T147_128_2 Q2.hfix147_128_2 Q2.hinj147_128_2
      Q2.hcardT147_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_128_2 i) (Q2.hfix147_128_2 i) _)
      colCert_147_128_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_128_15 (hp : 15 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 15 (transLenTr ⟨128, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 15 (transLenTr ⟨128, by decide⟩ 15 hp)) T147_128
      hfix147_128 hinj147_128 hcardT147_128
      (fun i => conj_mem_of_fixedPoints _ _ (T147_128 i) (hfix147_128 i) _)
      ⟨147, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 15 hp) Q2.T147_128_2 Q2.hfix147_128_2 Q2.hinj147_128_2
      Q2.hcardT147_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_128_2 i) (Q2.hfix147_128_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨128, by decide⟩ 15 (transLenTr ⟨128, by decide⟩ 15 hp) : ↥(reps ⟨128, by decide⟩)) : Coordinate 1)
        T147_128 = colFn colCertDiv_147_128_15.D1 (m := 1) from colCertDiv_147_128_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨128, by decide⟩ 15 hp : ↥(Q2.reps ⟨128, by decide⟩)) : Coordinate 2)
        Q2.T147_128_2 = colFn colCertDiv_147_128_15.D2 (m := 1) from colCertDiv_147_128_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_128_15_match


theorem leaf_147_128_16 (hp : 16 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 16 (transLenTr ⟨128, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 16 (transLenTr ⟨128, by decide⟩ 16 hp)) T147_128
      hfix147_128 hinj147_128 hcardT147_128
      (fun i => conj_mem_of_fixedPoints _ _ (T147_128 i) (hfix147_128 i) _)
      ⟨147, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 16 hp) Q2.T147_128_2 Q2.hfix147_128_2 Q2.hinj147_128_2
      Q2.hcardT147_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_128_2 i) (Q2.hfix147_128_2 i) _)
      colCert_147_128_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_128_17 (hp : 17 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 17 (transLenTr ⟨128, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 17 (transLenTr ⟨128, by decide⟩ 17 hp)) T147_128
      hfix147_128 hinj147_128 hcardT147_128
      (fun i => conj_mem_of_fixedPoints _ _ (T147_128 i) (hfix147_128 i) _)
      ⟨147, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 17 hp) Q2.T147_128_2 Q2.hfix147_128_2 Q2.hinj147_128_2
      Q2.hcardT147_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_128_2 i) (Q2.hfix147_128_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨128, by decide⟩ 17 (transLenTr ⟨128, by decide⟩ 17 hp) : ↥(reps ⟨128, by decide⟩)) : Coordinate 1)
        T147_128 = colFn colCertDiv_147_128_17.D1 (m := 1) from colCertDiv_147_128_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨128, by decide⟩ 17 hp : ↥(Q2.reps ⟨128, by decide⟩)) : Coordinate 2)
        Q2.T147_128_2 = colFn colCertDiv_147_128_17.D2 (m := 1) from colCertDiv_147_128_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_128_17_match


theorem leaf_147_128_18 (hp : 18 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 18 (transLenTr ⟨128, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 18 (transLenTr ⟨128, by decide⟩ 18 hp)) T147_128
      hfix147_128 hinj147_128 hcardT147_128
      (fun i => conj_mem_of_fixedPoints _ _ (T147_128 i) (hfix147_128 i) _)
      ⟨147, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 18 hp) Q2.T147_128_2 Q2.hfix147_128_2 Q2.hinj147_128_2
      Q2.hcardT147_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_128_2 i) (Q2.hfix147_128_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨128, by decide⟩ 18 (transLenTr ⟨128, by decide⟩ 18 hp) : ↥(reps ⟨128, by decide⟩)) : Coordinate 1)
        T147_128 = colFn colCertDiv_147_128_18.D1 (m := 1) from colCertDiv_147_128_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨128, by decide⟩ 18 hp : ↥(Q2.reps ⟨128, by decide⟩)) : Coordinate 2)
        Q2.T147_128_2 = colFn colCertDiv_147_128_18.D2 (m := 1) from colCertDiv_147_128_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_128_18_match


theorem leaf_147_128_19 (hp : 19 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 19 (transLenTr ⟨128, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 19 (transLenTr ⟨128, by decide⟩ 19 hp)) T147_128
      hfix147_128 hinj147_128 hcardT147_128
      (fun i => conj_mem_of_fixedPoints _ _ (T147_128 i) (hfix147_128 i) _)
      ⟨147, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 19 hp) Q2.T147_128_2 Q2.hfix147_128_2 Q2.hinj147_128_2
      Q2.hcardT147_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_128_2 i) (Q2.hfix147_128_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨128, by decide⟩ 19 (transLenTr ⟨128, by decide⟩ 19 hp) : ↥(reps ⟨128, by decide⟩)) : Coordinate 1)
        T147_128 = colFn colCertDiv_147_128_19.D1 (m := 1) from colCertDiv_147_128_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨128, by decide⟩ 19 hp : ↥(Q2.reps ⟨128, by decide⟩)) : Coordinate 2)
        Q2.T147_128_2 = colFn colCertDiv_147_128_19.D2 (m := 1) from colCertDiv_147_128_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_128_19_match


theorem leaf_147_128_20 (hp : 20 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 20 (transLenTr ⟨128, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 20 (transLenTr ⟨128, by decide⟩ 20 hp)) T147_128
      hfix147_128 hinj147_128 hcardT147_128
      (fun i => conj_mem_of_fixedPoints _ _ (T147_128 i) (hfix147_128 i) _)
      ⟨147, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 20 hp) Q2.T147_128_2 Q2.hfix147_128_2 Q2.hinj147_128_2
      Q2.hcardT147_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_128_2 i) (Q2.hfix147_128_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨128, by decide⟩ 20 (transLenTr ⟨128, by decide⟩ 20 hp) : ↥(reps ⟨128, by decide⟩)) : Coordinate 1)
        T147_128 = colFn colCertDiv_147_128_20.D1 (m := 1) from colCertDiv_147_128_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨128, by decide⟩ 20 hp : ↥(Q2.reps ⟨128, by decide⟩)) : Coordinate 2)
        Q2.T147_128_2 = colFn colCertDiv_147_128_20.D2 (m := 1) from colCertDiv_147_128_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_128_20_match


theorem leaf_147_128_21 (hp : 21 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 21 (transLenTr ⟨128, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 21 (transLenTr ⟨128, by decide⟩ 21 hp)) T147_128
      hfix147_128 hinj147_128 hcardT147_128
      (fun i => conj_mem_of_fixedPoints _ _ (T147_128 i) (hfix147_128 i) _)
      ⟨147, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 21 hp) Q2.T147_128_2 Q2.hfix147_128_2 Q2.hinj147_128_2
      Q2.hcardT147_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_128_2 i) (Q2.hfix147_128_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨128, by decide⟩ 21 (transLenTr ⟨128, by decide⟩ 21 hp) : ↥(reps ⟨128, by decide⟩)) : Coordinate 1)
        T147_128 = colFn colCertDiv_147_128_21.D1 (m := 1) from colCertDiv_147_128_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨128, by decide⟩ 21 hp : ↥(Q2.reps ⟨128, by decide⟩)) : Coordinate 2)
        Q2.T147_128_2 = colFn colCertDiv_147_128_21.D2 (m := 1) from colCertDiv_147_128_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_128_21_match


theorem leaf_147_128_22 (hp : 22 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 22 (transLenTr ⟨128, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 22 (transLenTr ⟨128, by decide⟩ 22 hp)) T147_128
      hfix147_128 hinj147_128 hcardT147_128
      (fun i => conj_mem_of_fixedPoints _ _ (T147_128 i) (hfix147_128 i) _)
      ⟨147, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 22 hp) Q2.T147_128_2 Q2.hfix147_128_2 Q2.hinj147_128_2
      Q2.hcardT147_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_128_2 i) (Q2.hfix147_128_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨128, by decide⟩ 22 (transLenTr ⟨128, by decide⟩ 22 hp) : ↥(reps ⟨128, by decide⟩)) : Coordinate 1)
        T147_128 = colFn colCertDiv_147_128_22.D1 (m := 1) from colCertDiv_147_128_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨128, by decide⟩ 22 hp : ↥(Q2.reps ⟨128, by decide⟩)) : Coordinate 2)
        Q2.T147_128_2 = colFn colCertDiv_147_128_22.D2 (m := 1) from colCertDiv_147_128_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_128_22_match


theorem leaf_147_128_23 (hp : 23 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 23 (transLenTr ⟨128, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 23 (transLenTr ⟨128, by decide⟩ 23 hp)) T147_128
      hfix147_128 hinj147_128 hcardT147_128
      (fun i => conj_mem_of_fixedPoints _ _ (T147_128 i) (hfix147_128 i) _)
      ⟨147, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 23 hp) Q2.T147_128_2 Q2.hfix147_128_2 Q2.hinj147_128_2
      Q2.hcardT147_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_128_2 i) (Q2.hfix147_128_2 i) _)
      colCert_147_128_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_128_24 (hp : 24 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 24 (transLenTr ⟨128, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 24 (transLenTr ⟨128, by decide⟩ 24 hp)) T147_128
      hfix147_128 hinj147_128 hcardT147_128
      (fun i => conj_mem_of_fixedPoints _ _ (T147_128 i) (hfix147_128 i) _)
      ⟨147, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 24 hp) Q2.T147_128_2 Q2.hfix147_128_2 Q2.hinj147_128_2
      Q2.hcardT147_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_128_2 i) (Q2.hfix147_128_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨128, by decide⟩ 24 (transLenTr ⟨128, by decide⟩ 24 hp) : ↥(reps ⟨128, by decide⟩)) : Coordinate 1)
        T147_128 = colFn colCertDiv_147_128_24.D1 (m := 1) from colCertDiv_147_128_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨128, by decide⟩ 24 hp : ↥(Q2.reps ⟨128, by decide⟩)) : Coordinate 2)
        Q2.T147_128_2 = colFn colCertDiv_147_128_24.D2 (m := 1) from colCertDiv_147_128_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_128_24_match


theorem leaf_147_129_0 (hp : 0 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 0 (transLenTr ⟨129, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 0 (transLenTr ⟨129, by decide⟩ 0 hp)) T147_129
      hfix147_129 hinj147_129 hcardT147_129
      (fun i => conj_mem_of_fixedPoints _ _ (T147_129 i) (hfix147_129 i) _)
      ⟨147, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 0 hp) Q2.T147_129_2 Q2.hfix147_129_2 Q2.hinj147_129_2
      Q2.hcardT147_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_129_2 i) (Q2.hfix147_129_2 i) _)
      colCert_147_129_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_129_1 (hp : 1 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 1 (transLenTr ⟨129, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 1 (transLenTr ⟨129, by decide⟩ 1 hp)) T147_129
      hfix147_129 hinj147_129 hcardT147_129
      (fun i => conj_mem_of_fixedPoints _ _ (T147_129 i) (hfix147_129 i) _)
      ⟨147, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 1 hp) Q2.T147_129_2 Q2.hfix147_129_2 Q2.hinj147_129_2
      Q2.hcardT147_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_129_2 i) (Q2.hfix147_129_2 i) _)
      colCert_147_129_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_129_2 (hp : 2 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 2 (transLenTr ⟨129, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 2 (transLenTr ⟨129, by decide⟩ 2 hp)) T147_129
      hfix147_129 hinj147_129 hcardT147_129
      (fun i => conj_mem_of_fixedPoints _ _ (T147_129 i) (hfix147_129 i) _)
      ⟨147, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 2 hp) Q2.T147_129_2 Q2.hfix147_129_2 Q2.hinj147_129_2
      Q2.hcardT147_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_129_2 i) (Q2.hfix147_129_2 i) _)
      colCert_147_129_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_129_3 (hp : 3 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 3 (transLenTr ⟨129, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 3 (transLenTr ⟨129, by decide⟩ 3 hp)) T147_129
      hfix147_129 hinj147_129 hcardT147_129
      (fun i => conj_mem_of_fixedPoints _ _ (T147_129 i) (hfix147_129 i) _)
      ⟨147, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 3 hp) Q2.T147_129_2 Q2.hfix147_129_2 Q2.hinj147_129_2
      Q2.hcardT147_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_129_2 i) (Q2.hfix147_129_2 i) _)
      colCert_147_129_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_129_4 (hp : 4 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 4 (transLenTr ⟨129, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 4 (transLenTr ⟨129, by decide⟩ 4 hp)) T147_129
      hfix147_129 hinj147_129 hcardT147_129
      (fun i => conj_mem_of_fixedPoints _ _ (T147_129 i) (hfix147_129 i) _)
      ⟨147, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 4 hp) Q2.T147_129_2 Q2.hfix147_129_2 Q2.hinj147_129_2
      Q2.hcardT147_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_129_2 i) (Q2.hfix147_129_2 i) _)
      colCert_147_129_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_129_5 (hp : 5 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 5 (transLenTr ⟨129, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 5 (transLenTr ⟨129, by decide⟩ 5 hp)) T147_129
      hfix147_129 hinj147_129 hcardT147_129
      (fun i => conj_mem_of_fixedPoints _ _ (T147_129 i) (hfix147_129 i) _)
      ⟨147, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 5 hp) Q2.T147_129_2 Q2.hfix147_129_2 Q2.hinj147_129_2
      Q2.hcardT147_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_129_2 i) (Q2.hfix147_129_2 i) _)
      colCert_147_129_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_129_6 (hp : 6 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 6 (transLenTr ⟨129, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 6 (transLenTr ⟨129, by decide⟩ 6 hp)) T147_129
      hfix147_129 hinj147_129 hcardT147_129
      (fun i => conj_mem_of_fixedPoints _ _ (T147_129 i) (hfix147_129 i) _)
      ⟨147, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 6 hp) Q2.T147_129_2 Q2.hfix147_129_2 Q2.hinj147_129_2
      Q2.hcardT147_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_129_2 i) (Q2.hfix147_129_2 i) _)
      colCert_147_129_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_129_7 (hp : 7 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 7 (transLenTr ⟨129, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 7 (transLenTr ⟨129, by decide⟩ 7 hp)) T147_129
      hfix147_129 hinj147_129 hcardT147_129
      (fun i => conj_mem_of_fixedPoints _ _ (T147_129 i) (hfix147_129 i) _)
      ⟨147, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 7 hp) Q2.T147_129_2 Q2.hfix147_129_2 Q2.hinj147_129_2
      Q2.hcardT147_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_129_2 i) (Q2.hfix147_129_2 i) _)
      colCert_147_129_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_129_8 (hp : 8 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 8 (transLenTr ⟨129, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 8 (transLenTr ⟨129, by decide⟩ 8 hp)) T147_129
      hfix147_129 hinj147_129 hcardT147_129
      (fun i => conj_mem_of_fixedPoints _ _ (T147_129 i) (hfix147_129 i) _)
      ⟨147, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 8 hp) Q2.T147_129_2 Q2.hfix147_129_2 Q2.hinj147_129_2
      Q2.hcardT147_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_129_2 i) (Q2.hfix147_129_2 i) _)
      colCert_147_129_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_129_9 (hp : 9 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 9 (transLenTr ⟨129, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 9 (transLenTr ⟨129, by decide⟩ 9 hp)) T147_129
      hfix147_129 hinj147_129 hcardT147_129
      (fun i => conj_mem_of_fixedPoints _ _ (T147_129 i) (hfix147_129 i) _)
      ⟨147, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 9 hp) Q2.T147_129_2 Q2.hfix147_129_2 Q2.hinj147_129_2
      Q2.hcardT147_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_129_2 i) (Q2.hfix147_129_2 i) _)
      colCert_147_129_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_129_10 (hp : 10 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 10 (transLenTr ⟨129, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 10 (transLenTr ⟨129, by decide⟩ 10 hp)) T147_129
      hfix147_129 hinj147_129 hcardT147_129
      (fun i => conj_mem_of_fixedPoints _ _ (T147_129 i) (hfix147_129 i) _)
      ⟨147, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 10 hp) Q2.T147_129_2 Q2.hfix147_129_2 Q2.hinj147_129_2
      Q2.hcardT147_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_129_2 i) (Q2.hfix147_129_2 i) _)
      colCert_147_129_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_129_11 (hp : 11 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 11 (transLenTr ⟨129, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 11 (transLenTr ⟨129, by decide⟩ 11 hp)) T147_129
      hfix147_129 hinj147_129 hcardT147_129
      (fun i => conj_mem_of_fixedPoints _ _ (T147_129 i) (hfix147_129 i) _)
      ⟨147, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 11 hp) Q2.T147_129_2 Q2.hfix147_129_2 Q2.hinj147_129_2
      Q2.hcardT147_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_129_2 i) (Q2.hfix147_129_2 i) _)
      colCert_147_129_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_129_12 (hp : 12 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 12 (transLenTr ⟨129, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 12 (transLenTr ⟨129, by decide⟩ 12 hp)) T147_129
      hfix147_129 hinj147_129 hcardT147_129
      (fun i => conj_mem_of_fixedPoints _ _ (T147_129 i) (hfix147_129 i) _)
      ⟨147, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 12 hp) Q2.T147_129_2 Q2.hfix147_129_2 Q2.hinj147_129_2
      Q2.hcardT147_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_129_2 i) (Q2.hfix147_129_2 i) _)
      colCert_147_129_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_129_13 (hp : 13 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 13 (transLenTr ⟨129, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 13 (transLenTr ⟨129, by decide⟩ 13 hp)) T147_129
      hfix147_129 hinj147_129 hcardT147_129
      (fun i => conj_mem_of_fixedPoints _ _ (T147_129 i) (hfix147_129 i) _)
      ⟨147, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 13 hp) Q2.T147_129_2 Q2.hfix147_129_2 Q2.hinj147_129_2
      Q2.hcardT147_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_129_2 i) (Q2.hfix147_129_2 i) _)
      colCert_147_129_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_129_14 (hp : 14 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 14 (transLenTr ⟨129, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 14 (transLenTr ⟨129, by decide⟩ 14 hp)) T147_129
      hfix147_129 hinj147_129 hcardT147_129
      (fun i => conj_mem_of_fixedPoints _ _ (T147_129 i) (hfix147_129 i) _)
      ⟨147, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 14 hp) Q2.T147_129_2 Q2.hfix147_129_2 Q2.hinj147_129_2
      Q2.hcardT147_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_129_2 i) (Q2.hfix147_129_2 i) _)
      colCert_147_129_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_129_15 (hp : 15 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 15 (transLenTr ⟨129, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 15 (transLenTr ⟨129, by decide⟩ 15 hp)) T147_129
      hfix147_129 hinj147_129 hcardT147_129
      (fun i => conj_mem_of_fixedPoints _ _ (T147_129 i) (hfix147_129 i) _)
      ⟨147, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 15 hp) Q2.T147_129_2 Q2.hfix147_129_2 Q2.hinj147_129_2
      Q2.hcardT147_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_129_2 i) (Q2.hfix147_129_2 i) _)
      colCert_147_129_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_129_16 (hp : 16 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 16 (transLenTr ⟨129, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 16 (transLenTr ⟨129, by decide⟩ 16 hp)) T147_129
      hfix147_129 hinj147_129 hcardT147_129
      (fun i => conj_mem_of_fixedPoints _ _ (T147_129 i) (hfix147_129 i) _)
      ⟨147, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 16 hp) Q2.T147_129_2 Q2.hfix147_129_2 Q2.hinj147_129_2
      Q2.hcardT147_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_129_2 i) (Q2.hfix147_129_2 i) _)
      colCert_147_129_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_129_17 (hp : 17 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 17 (transLenTr ⟨129, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 17 (transLenTr ⟨129, by decide⟩ 17 hp)) T147_129
      hfix147_129 hinj147_129 hcardT147_129
      (fun i => conj_mem_of_fixedPoints _ _ (T147_129 i) (hfix147_129 i) _)
      ⟨147, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 17 hp) Q2.T147_129_2 Q2.hfix147_129_2 Q2.hinj147_129_2
      Q2.hcardT147_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_129_2 i) (Q2.hfix147_129_2 i) _)
      colCert_147_129_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_129_18 (hp : 18 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 18 (transLenTr ⟨129, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 18 (transLenTr ⟨129, by decide⟩ 18 hp)) T147_129
      hfix147_129 hinj147_129 hcardT147_129
      (fun i => conj_mem_of_fixedPoints _ _ (T147_129 i) (hfix147_129 i) _)
      ⟨147, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 18 hp) Q2.T147_129_2 Q2.hfix147_129_2 Q2.hinj147_129_2
      Q2.hcardT147_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_129_2 i) (Q2.hfix147_129_2 i) _)
      colCert_147_129_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_129_19 (hp : 19 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 19 (transLenTr ⟨129, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 19 (transLenTr ⟨129, by decide⟩ 19 hp)) T147_129
      hfix147_129 hinj147_129 hcardT147_129
      (fun i => conj_mem_of_fixedPoints _ _ (T147_129 i) (hfix147_129 i) _)
      ⟨147, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 19 hp) Q2.T147_129_2 Q2.hfix147_129_2 Q2.hinj147_129_2
      Q2.hcardT147_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_129_2 i) (Q2.hfix147_129_2 i) _)
      colCert_147_129_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_129_20 (hp : 20 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 20 (transLenTr ⟨129, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 20 (transLenTr ⟨129, by decide⟩ 20 hp)) T147_129
      hfix147_129 hinj147_129 hcardT147_129
      (fun i => conj_mem_of_fixedPoints _ _ (T147_129 i) (hfix147_129 i) _)
      ⟨147, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 20 hp) Q2.T147_129_2 Q2.hfix147_129_2 Q2.hinj147_129_2
      Q2.hcardT147_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_129_2 i) (Q2.hfix147_129_2 i) _)
      colCert_147_129_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_129_21 (hp : 21 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 21 (transLenTr ⟨129, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 21 (transLenTr ⟨129, by decide⟩ 21 hp)) T147_129
      hfix147_129 hinj147_129 hcardT147_129
      (fun i => conj_mem_of_fixedPoints _ _ (T147_129 i) (hfix147_129 i) _)
      ⟨147, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 21 hp) Q2.T147_129_2 Q2.hfix147_129_2 Q2.hinj147_129_2
      Q2.hcardT147_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_129_2 i) (Q2.hfix147_129_2 i) _)
      colCert_147_129_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_129_22 (hp : 22 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 22 (transLenTr ⟨129, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 22 (transLenTr ⟨129, by decide⟩ 22 hp)) T147_129
      hfix147_129 hinj147_129 hcardT147_129
      (fun i => conj_mem_of_fixedPoints _ _ (T147_129 i) (hfix147_129 i) _)
      ⟨147, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 22 hp) Q2.T147_129_2 Q2.hfix147_129_2 Q2.hinj147_129_2
      Q2.hcardT147_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_129_2 i) (Q2.hfix147_129_2 i) _)
      colCert_147_129_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_129_23 (hp : 23 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 23 (transLenTr ⟨129, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 23 (transLenTr ⟨129, by decide⟩ 23 hp)) T147_129
      hfix147_129 hinj147_129 hcardT147_129
      (fun i => conj_mem_of_fixedPoints _ _ (T147_129 i) (hfix147_129 i) _)
      ⟨147, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 23 hp) Q2.T147_129_2 Q2.hfix147_129_2 Q2.hinj147_129_2
      Q2.hcardT147_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_129_2 i) (Q2.hfix147_129_2 i) _)
      colCert_147_129_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_129_24 (hp : 24 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 24 (transLenTr ⟨129, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 24 (transLenTr ⟨129, by decide⟩ 24 hp)) T147_129
      hfix147_129 hinj147_129 hcardT147_129
      (fun i => conj_mem_of_fixedPoints _ _ (T147_129 i) (hfix147_129 i) _)
      ⟨147, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 24 hp) Q2.T147_129_2 Q2.hfix147_129_2 Q2.hinj147_129_2
      Q2.hcardT147_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_129_2 i) (Q2.hfix147_129_2 i) _)
      colCert_147_129_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_130_0 (hp : 0 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 0 (transLenTr ⟨130, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 0 (transLenTr ⟨130, by decide⟩ 0 hp)) T147_130
      hfix147_130 hinj147_130 hcardT147_130
      (fun i => conj_mem_of_fixedPoints _ _ (T147_130 i) (hfix147_130 i) _)
      ⟨147, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 0 hp) Q2.T147_130_2 Q2.hfix147_130_2 Q2.hinj147_130_2
      Q2.hcardT147_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_130_2 i) (Q2.hfix147_130_2 i) _)
      colCert_147_130_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_130_1 (hp : 1 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 1 (transLenTr ⟨130, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 1 (transLenTr ⟨130, by decide⟩ 1 hp)) T147_130
      hfix147_130 hinj147_130 hcardT147_130
      (fun i => conj_mem_of_fixedPoints _ _ (T147_130 i) (hfix147_130 i) _)
      ⟨147, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 1 hp) Q2.T147_130_2 Q2.hfix147_130_2 Q2.hinj147_130_2
      Q2.hcardT147_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_130_2 i) (Q2.hfix147_130_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨130, by decide⟩ 1 (transLenTr ⟨130, by decide⟩ 1 hp) : ↥(reps ⟨130, by decide⟩)) : Coordinate 1)
        T147_130 = colFn colCertDiv_147_130_1.D1 (m := 1) from colCertDiv_147_130_1.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨130, by decide⟩ 1 hp : ↥(Q2.reps ⟨130, by decide⟩)) : Coordinate 2)
        Q2.T147_130_2 = colFn colCertDiv_147_130_1.D2 (m := 1) from colCertDiv_147_130_1.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_130_1_match


theorem leaf_147_130_2 (hp : 2 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 2 (transLenTr ⟨130, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 2 (transLenTr ⟨130, by decide⟩ 2 hp)) T147_130
      hfix147_130 hinj147_130 hcardT147_130
      (fun i => conj_mem_of_fixedPoints _ _ (T147_130 i) (hfix147_130 i) _)
      ⟨147, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 2 hp) Q2.T147_130_2 Q2.hfix147_130_2 Q2.hinj147_130_2
      Q2.hcardT147_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_130_2 i) (Q2.hfix147_130_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨130, by decide⟩ 2 (transLenTr ⟨130, by decide⟩ 2 hp) : ↥(reps ⟨130, by decide⟩)) : Coordinate 1)
        T147_130 = colFn colCertDiv_147_130_2.D1 (m := 1) from colCertDiv_147_130_2.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨130, by decide⟩ 2 hp : ↥(Q2.reps ⟨130, by decide⟩)) : Coordinate 2)
        Q2.T147_130_2 = colFn colCertDiv_147_130_2.D2 (m := 1) from colCertDiv_147_130_2.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_130_2_match


theorem leaf_147_130_3 (hp : 3 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 3 (transLenTr ⟨130, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 3 (transLenTr ⟨130, by decide⟩ 3 hp)) T147_130
      hfix147_130 hinj147_130 hcardT147_130
      (fun i => conj_mem_of_fixedPoints _ _ (T147_130 i) (hfix147_130 i) _)
      ⟨147, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 3 hp) Q2.T147_130_2 Q2.hfix147_130_2 Q2.hinj147_130_2
      Q2.hcardT147_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_130_2 i) (Q2.hfix147_130_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨130, by decide⟩ 3 (transLenTr ⟨130, by decide⟩ 3 hp) : ↥(reps ⟨130, by decide⟩)) : Coordinate 1)
        T147_130 = colFn colCertDiv_147_130_3.D1 (m := 1) from colCertDiv_147_130_3.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨130, by decide⟩ 3 hp : ↥(Q2.reps ⟨130, by decide⟩)) : Coordinate 2)
        Q2.T147_130_2 = colFn colCertDiv_147_130_3.D2 (m := 1) from colCertDiv_147_130_3.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_130_3_match


theorem leaf_147_130_4 (hp : 4 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 4 (transLenTr ⟨130, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 4 (transLenTr ⟨130, by decide⟩ 4 hp)) T147_130
      hfix147_130 hinj147_130 hcardT147_130
      (fun i => conj_mem_of_fixedPoints _ _ (T147_130 i) (hfix147_130 i) _)
      ⟨147, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 4 hp) Q2.T147_130_2 Q2.hfix147_130_2 Q2.hinj147_130_2
      Q2.hcardT147_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_130_2 i) (Q2.hfix147_130_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨130, by decide⟩ 4 (transLenTr ⟨130, by decide⟩ 4 hp) : ↥(reps ⟨130, by decide⟩)) : Coordinate 1)
        T147_130 = colFn colCertDiv_147_130_4.D1 (m := 1) from colCertDiv_147_130_4.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨130, by decide⟩ 4 hp : ↥(Q2.reps ⟨130, by decide⟩)) : Coordinate 2)
        Q2.T147_130_2 = colFn colCertDiv_147_130_4.D2 (m := 1) from colCertDiv_147_130_4.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_130_4_match


theorem leaf_147_130_5 (hp : 5 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 5 (transLenTr ⟨130, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 5 (transLenTr ⟨130, by decide⟩ 5 hp)) T147_130
      hfix147_130 hinj147_130 hcardT147_130
      (fun i => conj_mem_of_fixedPoints _ _ (T147_130 i) (hfix147_130 i) _)
      ⟨147, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 5 hp) Q2.T147_130_2 Q2.hfix147_130_2 Q2.hinj147_130_2
      Q2.hcardT147_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_130_2 i) (Q2.hfix147_130_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨130, by decide⟩ 5 (transLenTr ⟨130, by decide⟩ 5 hp) : ↥(reps ⟨130, by decide⟩)) : Coordinate 1)
        T147_130 = colFn colCertDiv_147_130_5.D1 (m := 1) from colCertDiv_147_130_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨130, by decide⟩ 5 hp : ↥(Q2.reps ⟨130, by decide⟩)) : Coordinate 2)
        Q2.T147_130_2 = colFn colCertDiv_147_130_5.D2 (m := 1) from colCertDiv_147_130_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_130_5_match


theorem leaf_147_130_6 (hp : 6 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 6 (transLenTr ⟨130, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 6 (transLenTr ⟨130, by decide⟩ 6 hp)) T147_130
      hfix147_130 hinj147_130 hcardT147_130
      (fun i => conj_mem_of_fixedPoints _ _ (T147_130 i) (hfix147_130 i) _)
      ⟨147, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 6 hp) Q2.T147_130_2 Q2.hfix147_130_2 Q2.hinj147_130_2
      Q2.hcardT147_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_130_2 i) (Q2.hfix147_130_2 i) _)
      colCert_147_130_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_130_7 (hp : 7 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 7 (transLenTr ⟨130, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 7 (transLenTr ⟨130, by decide⟩ 7 hp)) T147_130
      hfix147_130 hinj147_130 hcardT147_130
      (fun i => conj_mem_of_fixedPoints _ _ (T147_130 i) (hfix147_130 i) _)
      ⟨147, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 7 hp) Q2.T147_130_2 Q2.hfix147_130_2 Q2.hinj147_130_2
      Q2.hcardT147_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_130_2 i) (Q2.hfix147_130_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨130, by decide⟩ 7 (transLenTr ⟨130, by decide⟩ 7 hp) : ↥(reps ⟨130, by decide⟩)) : Coordinate 1)
        T147_130 = colFn colCertDiv_147_130_7.D1 (m := 1) from colCertDiv_147_130_7.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨130, by decide⟩ 7 hp : ↥(Q2.reps ⟨130, by decide⟩)) : Coordinate 2)
        Q2.T147_130_2 = colFn colCertDiv_147_130_7.D2 (m := 1) from colCertDiv_147_130_7.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_130_7_match


theorem leaf_147_130_8 (hp : 8 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 8 (transLenTr ⟨130, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 8 (transLenTr ⟨130, by decide⟩ 8 hp)) T147_130
      hfix147_130 hinj147_130 hcardT147_130
      (fun i => conj_mem_of_fixedPoints _ _ (T147_130 i) (hfix147_130 i) _)
      ⟨147, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 8 hp) Q2.T147_130_2 Q2.hfix147_130_2 Q2.hinj147_130_2
      Q2.hcardT147_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_130_2 i) (Q2.hfix147_130_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨130, by decide⟩ 8 (transLenTr ⟨130, by decide⟩ 8 hp) : ↥(reps ⟨130, by decide⟩)) : Coordinate 1)
        T147_130 = colFn colCertDiv_147_130_8.D1 (m := 1) from colCertDiv_147_130_8.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨130, by decide⟩ 8 hp : ↥(Q2.reps ⟨130, by decide⟩)) : Coordinate 2)
        Q2.T147_130_2 = colFn colCertDiv_147_130_8.D2 (m := 1) from colCertDiv_147_130_8.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_130_8_match


theorem leaf_147_130_9 (hp : 9 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 9 (transLenTr ⟨130, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 9 (transLenTr ⟨130, by decide⟩ 9 hp)) T147_130
      hfix147_130 hinj147_130 hcardT147_130
      (fun i => conj_mem_of_fixedPoints _ _ (T147_130 i) (hfix147_130 i) _)
      ⟨147, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 9 hp) Q2.T147_130_2 Q2.hfix147_130_2 Q2.hinj147_130_2
      Q2.hcardT147_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_130_2 i) (Q2.hfix147_130_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨130, by decide⟩ 9 (transLenTr ⟨130, by decide⟩ 9 hp) : ↥(reps ⟨130, by decide⟩)) : Coordinate 1)
        T147_130 = colFn colCertDiv_147_130_9.D1 (m := 1) from colCertDiv_147_130_9.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨130, by decide⟩ 9 hp : ↥(Q2.reps ⟨130, by decide⟩)) : Coordinate 2)
        Q2.T147_130_2 = colFn colCertDiv_147_130_9.D2 (m := 1) from colCertDiv_147_130_9.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_130_9_match


theorem leaf_147_130_10 (hp : 10 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 10 (transLenTr ⟨130, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 10 (transLenTr ⟨130, by decide⟩ 10 hp)) T147_130
      hfix147_130 hinj147_130 hcardT147_130
      (fun i => conj_mem_of_fixedPoints _ _ (T147_130 i) (hfix147_130 i) _)
      ⟨147, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 10 hp) Q2.T147_130_2 Q2.hfix147_130_2 Q2.hinj147_130_2
      Q2.hcardT147_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_130_2 i) (Q2.hfix147_130_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨130, by decide⟩ 10 (transLenTr ⟨130, by decide⟩ 10 hp) : ↥(reps ⟨130, by decide⟩)) : Coordinate 1)
        T147_130 = colFn colCertDiv_147_130_10.D1 (m := 1) from colCertDiv_147_130_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨130, by decide⟩ 10 hp : ↥(Q2.reps ⟨130, by decide⟩)) : Coordinate 2)
        Q2.T147_130_2 = colFn colCertDiv_147_130_10.D2 (m := 1) from colCertDiv_147_130_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_130_10_match


theorem leaf_147_130_11 (hp : 11 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 11 (transLenTr ⟨130, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 11 (transLenTr ⟨130, by decide⟩ 11 hp)) T147_130
      hfix147_130 hinj147_130 hcardT147_130
      (fun i => conj_mem_of_fixedPoints _ _ (T147_130 i) (hfix147_130 i) _)
      ⟨147, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 11 hp) Q2.T147_130_2 Q2.hfix147_130_2 Q2.hinj147_130_2
      Q2.hcardT147_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_130_2 i) (Q2.hfix147_130_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨130, by decide⟩ 11 (transLenTr ⟨130, by decide⟩ 11 hp) : ↥(reps ⟨130, by decide⟩)) : Coordinate 1)
        T147_130 = colFn colCertDiv_147_130_11.D1 (m := 1) from colCertDiv_147_130_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨130, by decide⟩ 11 hp : ↥(Q2.reps ⟨130, by decide⟩)) : Coordinate 2)
        Q2.T147_130_2 = colFn colCertDiv_147_130_11.D2 (m := 1) from colCertDiv_147_130_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_130_11_match


theorem leaf_147_130_12 (hp : 12 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 12 (transLenTr ⟨130, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 12 (transLenTr ⟨130, by decide⟩ 12 hp)) T147_130
      hfix147_130 hinj147_130 hcardT147_130
      (fun i => conj_mem_of_fixedPoints _ _ (T147_130 i) (hfix147_130 i) _)
      ⟨147, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 12 hp) Q2.T147_130_2 Q2.hfix147_130_2 Q2.hinj147_130_2
      Q2.hcardT147_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_130_2 i) (Q2.hfix147_130_2 i) _)
      colCert_147_130_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_130_13 (hp : 13 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 13 (transLenTr ⟨130, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 13 (transLenTr ⟨130, by decide⟩ 13 hp)) T147_130
      hfix147_130 hinj147_130 hcardT147_130
      (fun i => conj_mem_of_fixedPoints _ _ (T147_130 i) (hfix147_130 i) _)
      ⟨147, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 13 hp) Q2.T147_130_2 Q2.hfix147_130_2 Q2.hinj147_130_2
      Q2.hcardT147_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_130_2 i) (Q2.hfix147_130_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨130, by decide⟩ 13 (transLenTr ⟨130, by decide⟩ 13 hp) : ↥(reps ⟨130, by decide⟩)) : Coordinate 1)
        T147_130 = colFn colCertDiv_147_130_13.D1 (m := 1) from colCertDiv_147_130_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨130, by decide⟩ 13 hp : ↥(Q2.reps ⟨130, by decide⟩)) : Coordinate 2)
        Q2.T147_130_2 = colFn colCertDiv_147_130_13.D2 (m := 1) from colCertDiv_147_130_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_130_13_match


theorem leaf_147_130_14 (hp : 14 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 14 (transLenTr ⟨130, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 14 (transLenTr ⟨130, by decide⟩ 14 hp)) T147_130
      hfix147_130 hinj147_130 hcardT147_130
      (fun i => conj_mem_of_fixedPoints _ _ (T147_130 i) (hfix147_130 i) _)
      ⟨147, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 14 hp) Q2.T147_130_2 Q2.hfix147_130_2 Q2.hinj147_130_2
      Q2.hcardT147_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_130_2 i) (Q2.hfix147_130_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨130, by decide⟩ 14 (transLenTr ⟨130, by decide⟩ 14 hp) : ↥(reps ⟨130, by decide⟩)) : Coordinate 1)
        T147_130 = colFn colCertDiv_147_130_14.D1 (m := 1) from colCertDiv_147_130_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨130, by decide⟩ 14 hp : ↥(Q2.reps ⟨130, by decide⟩)) : Coordinate 2)
        Q2.T147_130_2 = colFn colCertDiv_147_130_14.D2 (m := 1) from colCertDiv_147_130_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_130_14_match


theorem leaf_147_130_15 (hp : 15 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 15 (transLenTr ⟨130, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 15 (transLenTr ⟨130, by decide⟩ 15 hp)) T147_130
      hfix147_130 hinj147_130 hcardT147_130
      (fun i => conj_mem_of_fixedPoints _ _ (T147_130 i) (hfix147_130 i) _)
      ⟨147, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 15 hp) Q2.T147_130_2 Q2.hfix147_130_2 Q2.hinj147_130_2
      Q2.hcardT147_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_130_2 i) (Q2.hfix147_130_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨130, by decide⟩ 15 (transLenTr ⟨130, by decide⟩ 15 hp) : ↥(reps ⟨130, by decide⟩)) : Coordinate 1)
        T147_130 = colFn colCertDiv_147_130_15.D1 (m := 1) from colCertDiv_147_130_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨130, by decide⟩ 15 hp : ↥(Q2.reps ⟨130, by decide⟩)) : Coordinate 2)
        Q2.T147_130_2 = colFn colCertDiv_147_130_15.D2 (m := 1) from colCertDiv_147_130_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_130_15_match


theorem leaf_147_130_16 (hp : 16 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 16 (transLenTr ⟨130, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 16 (transLenTr ⟨130, by decide⟩ 16 hp)) T147_130
      hfix147_130 hinj147_130 hcardT147_130
      (fun i => conj_mem_of_fixedPoints _ _ (T147_130 i) (hfix147_130 i) _)
      ⟨147, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 16 hp) Q2.T147_130_2 Q2.hfix147_130_2 Q2.hinj147_130_2
      Q2.hcardT147_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_130_2 i) (Q2.hfix147_130_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨130, by decide⟩ 16 (transLenTr ⟨130, by decide⟩ 16 hp) : ↥(reps ⟨130, by decide⟩)) : Coordinate 1)
        T147_130 = colFn colCertDiv_147_130_16.D1 (m := 1) from colCertDiv_147_130_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨130, by decide⟩ 16 hp : ↥(Q2.reps ⟨130, by decide⟩)) : Coordinate 2)
        Q2.T147_130_2 = colFn colCertDiv_147_130_16.D2 (m := 1) from colCertDiv_147_130_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_130_16_match


theorem leaf_147_130_17 (hp : 17 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 17 (transLenTr ⟨130, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 17 (transLenTr ⟨130, by decide⟩ 17 hp)) T147_130
      hfix147_130 hinj147_130 hcardT147_130
      (fun i => conj_mem_of_fixedPoints _ _ (T147_130 i) (hfix147_130 i) _)
      ⟨147, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 17 hp) Q2.T147_130_2 Q2.hfix147_130_2 Q2.hinj147_130_2
      Q2.hcardT147_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_130_2 i) (Q2.hfix147_130_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨130, by decide⟩ 17 (transLenTr ⟨130, by decide⟩ 17 hp) : ↥(reps ⟨130, by decide⟩)) : Coordinate 1)
        T147_130 = colFn colCertDiv_147_130_17.D1 (m := 1) from colCertDiv_147_130_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨130, by decide⟩ 17 hp : ↥(Q2.reps ⟨130, by decide⟩)) : Coordinate 2)
        Q2.T147_130_2 = colFn colCertDiv_147_130_17.D2 (m := 1) from colCertDiv_147_130_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_130_17_match


theorem leaf_147_130_18 (hp : 18 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 18 (transLenTr ⟨130, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 18 (transLenTr ⟨130, by decide⟩ 18 hp)) T147_130
      hfix147_130 hinj147_130 hcardT147_130
      (fun i => conj_mem_of_fixedPoints _ _ (T147_130 i) (hfix147_130 i) _)
      ⟨147, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 18 hp) Q2.T147_130_2 Q2.hfix147_130_2 Q2.hinj147_130_2
      Q2.hcardT147_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_130_2 i) (Q2.hfix147_130_2 i) _)
      colCert_147_130_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_130_19 (hp : 19 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 19 (transLenTr ⟨130, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 19 (transLenTr ⟨130, by decide⟩ 19 hp)) T147_130
      hfix147_130 hinj147_130 hcardT147_130
      (fun i => conj_mem_of_fixedPoints _ _ (T147_130 i) (hfix147_130 i) _)
      ⟨147, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 19 hp) Q2.T147_130_2 Q2.hfix147_130_2 Q2.hinj147_130_2
      Q2.hcardT147_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_130_2 i) (Q2.hfix147_130_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨130, by decide⟩ 19 (transLenTr ⟨130, by decide⟩ 19 hp) : ↥(reps ⟨130, by decide⟩)) : Coordinate 1)
        T147_130 = colFn colCertDiv_147_130_19.D1 (m := 1) from colCertDiv_147_130_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨130, by decide⟩ 19 hp : ↥(Q2.reps ⟨130, by decide⟩)) : Coordinate 2)
        Q2.T147_130_2 = colFn colCertDiv_147_130_19.D2 (m := 1) from colCertDiv_147_130_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_130_19_match


theorem leaf_147_130_20 (hp : 20 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 20 (transLenTr ⟨130, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 20 (transLenTr ⟨130, by decide⟩ 20 hp)) T147_130
      hfix147_130 hinj147_130 hcardT147_130
      (fun i => conj_mem_of_fixedPoints _ _ (T147_130 i) (hfix147_130 i) _)
      ⟨147, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 20 hp) Q2.T147_130_2 Q2.hfix147_130_2 Q2.hinj147_130_2
      Q2.hcardT147_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_130_2 i) (Q2.hfix147_130_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨130, by decide⟩ 20 (transLenTr ⟨130, by decide⟩ 20 hp) : ↥(reps ⟨130, by decide⟩)) : Coordinate 1)
        T147_130 = colFn colCertDiv_147_130_20.D1 (m := 1) from colCertDiv_147_130_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨130, by decide⟩ 20 hp : ↥(Q2.reps ⟨130, by decide⟩)) : Coordinate 2)
        Q2.T147_130_2 = colFn colCertDiv_147_130_20.D2 (m := 1) from colCertDiv_147_130_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_130_20_match


theorem leaf_147_130_21 (hp : 21 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 21 (transLenTr ⟨130, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 21 (transLenTr ⟨130, by decide⟩ 21 hp)) T147_130
      hfix147_130 hinj147_130 hcardT147_130
      (fun i => conj_mem_of_fixedPoints _ _ (T147_130 i) (hfix147_130 i) _)
      ⟨147, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 21 hp) Q2.T147_130_2 Q2.hfix147_130_2 Q2.hinj147_130_2
      Q2.hcardT147_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_130_2 i) (Q2.hfix147_130_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨130, by decide⟩ 21 (transLenTr ⟨130, by decide⟩ 21 hp) : ↥(reps ⟨130, by decide⟩)) : Coordinate 1)
        T147_130 = colFn colCertDiv_147_130_21.D1 (m := 1) from colCertDiv_147_130_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨130, by decide⟩ 21 hp : ↥(Q2.reps ⟨130, by decide⟩)) : Coordinate 2)
        Q2.T147_130_2 = colFn colCertDiv_147_130_21.D2 (m := 1) from colCertDiv_147_130_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_130_21_match


theorem leaf_147_130_22 (hp : 22 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 22 (transLenTr ⟨130, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 22 (transLenTr ⟨130, by decide⟩ 22 hp)) T147_130
      hfix147_130 hinj147_130 hcardT147_130
      (fun i => conj_mem_of_fixedPoints _ _ (T147_130 i) (hfix147_130 i) _)
      ⟨147, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 22 hp) Q2.T147_130_2 Q2.hfix147_130_2 Q2.hinj147_130_2
      Q2.hcardT147_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_130_2 i) (Q2.hfix147_130_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨130, by decide⟩ 22 (transLenTr ⟨130, by decide⟩ 22 hp) : ↥(reps ⟨130, by decide⟩)) : Coordinate 1)
        T147_130 = colFn colCertDiv_147_130_22.D1 (m := 1) from colCertDiv_147_130_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨130, by decide⟩ 22 hp : ↥(Q2.reps ⟨130, by decide⟩)) : Coordinate 2)
        Q2.T147_130_2 = colFn colCertDiv_147_130_22.D2 (m := 1) from colCertDiv_147_130_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_130_22_match


theorem leaf_147_130_23 (hp : 23 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 23 (transLenTr ⟨130, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 23 (transLenTr ⟨130, by decide⟩ 23 hp)) T147_130
      hfix147_130 hinj147_130 hcardT147_130
      (fun i => conj_mem_of_fixedPoints _ _ (T147_130 i) (hfix147_130 i) _)
      ⟨147, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 23 hp) Q2.T147_130_2 Q2.hfix147_130_2 Q2.hinj147_130_2
      Q2.hcardT147_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_130_2 i) (Q2.hfix147_130_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨130, by decide⟩ 23 (transLenTr ⟨130, by decide⟩ 23 hp) : ↥(reps ⟨130, by decide⟩)) : Coordinate 1)
        T147_130 = colFn colCertDiv_147_130_23.D1 (m := 1) from colCertDiv_147_130_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨130, by decide⟩ 23 hp : ↥(Q2.reps ⟨130, by decide⟩)) : Coordinate 2)
        Q2.T147_130_2 = colFn colCertDiv_147_130_23.D2 (m := 1) from colCertDiv_147_130_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_130_23_match


theorem leaf_147_130_24 (hp : 24 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 24 (transLenTr ⟨130, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 24 (transLenTr ⟨130, by decide⟩ 24 hp)) T147_130
      hfix147_130 hinj147_130 hcardT147_130
      (fun i => conj_mem_of_fixedPoints _ _ (T147_130 i) (hfix147_130 i) _)
      ⟨147, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 24 hp) Q2.T147_130_2 Q2.hfix147_130_2 Q2.hinj147_130_2
      Q2.hcardT147_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_130_2 i) (Q2.hfix147_130_2 i) _)
      colCert_147_130_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_131_0 (hp : 0 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 0 (transLenTr ⟨131, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 0 (transLenTr ⟨131, by decide⟩ 0 hp)) T147_131
      hfix147_131 hinj147_131 hcardT147_131
      (fun i => conj_mem_of_fixedPoints _ _ (T147_131 i) (hfix147_131 i) _)
      ⟨147, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 0 hp) Q2.T147_131_2 Q2.hfix147_131_2 Q2.hinj147_131_2
      Q2.hcardT147_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_131_2 i) (Q2.hfix147_131_2 i) _)
      colCert_147_131_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_131_1 (hp : 1 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 1 (transLenTr ⟨131, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 1 (transLenTr ⟨131, by decide⟩ 1 hp)) T147_131
      hfix147_131 hinj147_131 hcardT147_131
      (fun i => conj_mem_of_fixedPoints _ _ (T147_131 i) (hfix147_131 i) _)
      ⟨147, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 1 hp) Q2.T147_131_2 Q2.hfix147_131_2 Q2.hinj147_131_2
      Q2.hcardT147_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_131_2 i) (Q2.hfix147_131_2 i) _)
      colCert_147_131_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_131_2 (hp : 2 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 2 (transLenTr ⟨131, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 2 (transLenTr ⟨131, by decide⟩ 2 hp)) T147_131
      hfix147_131 hinj147_131 hcardT147_131
      (fun i => conj_mem_of_fixedPoints _ _ (T147_131 i) (hfix147_131 i) _)
      ⟨147, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 2 hp) Q2.T147_131_2 Q2.hfix147_131_2 Q2.hinj147_131_2
      Q2.hcardT147_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_131_2 i) (Q2.hfix147_131_2 i) _)
      colCert_147_131_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_131_3 (hp : 3 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 3 (transLenTr ⟨131, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 3 (transLenTr ⟨131, by decide⟩ 3 hp)) T147_131
      hfix147_131 hinj147_131 hcardT147_131
      (fun i => conj_mem_of_fixedPoints _ _ (T147_131 i) (hfix147_131 i) _)
      ⟨147, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 3 hp) Q2.T147_131_2 Q2.hfix147_131_2 Q2.hinj147_131_2
      Q2.hcardT147_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_131_2 i) (Q2.hfix147_131_2 i) _)
      colCert_147_131_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_131_4 (hp : 4 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 4 (transLenTr ⟨131, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 4 (transLenTr ⟨131, by decide⟩ 4 hp)) T147_131
      hfix147_131 hinj147_131 hcardT147_131
      (fun i => conj_mem_of_fixedPoints _ _ (T147_131 i) (hfix147_131 i) _)
      ⟨147, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 4 hp) Q2.T147_131_2 Q2.hfix147_131_2 Q2.hinj147_131_2
      Q2.hcardT147_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_131_2 i) (Q2.hfix147_131_2 i) _)
      colCert_147_131_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_131_5 (hp : 5 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 5 (transLenTr ⟨131, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 5 (transLenTr ⟨131, by decide⟩ 5 hp)) T147_131
      hfix147_131 hinj147_131 hcardT147_131
      (fun i => conj_mem_of_fixedPoints _ _ (T147_131 i) (hfix147_131 i) _)
      ⟨147, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 5 hp) Q2.T147_131_2 Q2.hfix147_131_2 Q2.hinj147_131_2
      Q2.hcardT147_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_131_2 i) (Q2.hfix147_131_2 i) _)
      colCert_147_131_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_131_6 (hp : 6 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 6 (transLenTr ⟨131, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 6 (transLenTr ⟨131, by decide⟩ 6 hp)) T147_131
      hfix147_131 hinj147_131 hcardT147_131
      (fun i => conj_mem_of_fixedPoints _ _ (T147_131 i) (hfix147_131 i) _)
      ⟨147, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 6 hp) Q2.T147_131_2 Q2.hfix147_131_2 Q2.hinj147_131_2
      Q2.hcardT147_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_131_2 i) (Q2.hfix147_131_2 i) _)
      colCert_147_131_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_131_7 (hp : 7 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 7 (transLenTr ⟨131, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 7 (transLenTr ⟨131, by decide⟩ 7 hp)) T147_131
      hfix147_131 hinj147_131 hcardT147_131
      (fun i => conj_mem_of_fixedPoints _ _ (T147_131 i) (hfix147_131 i) _)
      ⟨147, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 7 hp) Q2.T147_131_2 Q2.hfix147_131_2 Q2.hinj147_131_2
      Q2.hcardT147_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_131_2 i) (Q2.hfix147_131_2 i) _)
      colCert_147_131_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_131_8 (hp : 8 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 8 (transLenTr ⟨131, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 8 (transLenTr ⟨131, by decide⟩ 8 hp)) T147_131
      hfix147_131 hinj147_131 hcardT147_131
      (fun i => conj_mem_of_fixedPoints _ _ (T147_131 i) (hfix147_131 i) _)
      ⟨147, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 8 hp) Q2.T147_131_2 Q2.hfix147_131_2 Q2.hinj147_131_2
      Q2.hcardT147_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_131_2 i) (Q2.hfix147_131_2 i) _)
      colCert_147_131_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_131_9 (hp : 9 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 9 (transLenTr ⟨131, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 9 (transLenTr ⟨131, by decide⟩ 9 hp)) T147_131
      hfix147_131 hinj147_131 hcardT147_131
      (fun i => conj_mem_of_fixedPoints _ _ (T147_131 i) (hfix147_131 i) _)
      ⟨147, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 9 hp) Q2.T147_131_2 Q2.hfix147_131_2 Q2.hinj147_131_2
      Q2.hcardT147_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_131_2 i) (Q2.hfix147_131_2 i) _)
      colCert_147_131_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_131_10 (hp : 10 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 10 (transLenTr ⟨131, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 10 (transLenTr ⟨131, by decide⟩ 10 hp)) T147_131
      hfix147_131 hinj147_131 hcardT147_131
      (fun i => conj_mem_of_fixedPoints _ _ (T147_131 i) (hfix147_131 i) _)
      ⟨147, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 10 hp) Q2.T147_131_2 Q2.hfix147_131_2 Q2.hinj147_131_2
      Q2.hcardT147_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_131_2 i) (Q2.hfix147_131_2 i) _)
      colCert_147_131_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_131_11 (hp : 11 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 11 (transLenTr ⟨131, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 11 (transLenTr ⟨131, by decide⟩ 11 hp)) T147_131
      hfix147_131 hinj147_131 hcardT147_131
      (fun i => conj_mem_of_fixedPoints _ _ (T147_131 i) (hfix147_131 i) _)
      ⟨147, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 11 hp) Q2.T147_131_2 Q2.hfix147_131_2 Q2.hinj147_131_2
      Q2.hcardT147_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_131_2 i) (Q2.hfix147_131_2 i) _)
      colCert_147_131_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_131_12 (hp : 12 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 12 (transLenTr ⟨131, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 12 (transLenTr ⟨131, by decide⟩ 12 hp)) T147_131
      hfix147_131 hinj147_131 hcardT147_131
      (fun i => conj_mem_of_fixedPoints _ _ (T147_131 i) (hfix147_131 i) _)
      ⟨147, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 12 hp) Q2.T147_131_2 Q2.hfix147_131_2 Q2.hinj147_131_2
      Q2.hcardT147_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_131_2 i) (Q2.hfix147_131_2 i) _)
      colCert_147_131_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_131_13 (hp : 13 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 13 (transLenTr ⟨131, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 13 (transLenTr ⟨131, by decide⟩ 13 hp)) T147_131
      hfix147_131 hinj147_131 hcardT147_131
      (fun i => conj_mem_of_fixedPoints _ _ (T147_131 i) (hfix147_131 i) _)
      ⟨147, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 13 hp) Q2.T147_131_2 Q2.hfix147_131_2 Q2.hinj147_131_2
      Q2.hcardT147_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_131_2 i) (Q2.hfix147_131_2 i) _)
      colCert_147_131_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_131_14 (hp : 14 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 14 (transLenTr ⟨131, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 14 (transLenTr ⟨131, by decide⟩ 14 hp)) T147_131
      hfix147_131 hinj147_131 hcardT147_131
      (fun i => conj_mem_of_fixedPoints _ _ (T147_131 i) (hfix147_131 i) _)
      ⟨147, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 14 hp) Q2.T147_131_2 Q2.hfix147_131_2 Q2.hinj147_131_2
      Q2.hcardT147_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_131_2 i) (Q2.hfix147_131_2 i) _)
      colCert_147_131_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_131_15 (hp : 15 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 15 (transLenTr ⟨131, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 15 (transLenTr ⟨131, by decide⟩ 15 hp)) T147_131
      hfix147_131 hinj147_131 hcardT147_131
      (fun i => conj_mem_of_fixedPoints _ _ (T147_131 i) (hfix147_131 i) _)
      ⟨147, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 15 hp) Q2.T147_131_2 Q2.hfix147_131_2 Q2.hinj147_131_2
      Q2.hcardT147_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_131_2 i) (Q2.hfix147_131_2 i) _)
      colCert_147_131_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_131_16 (hp : 16 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 16 (transLenTr ⟨131, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 16 (transLenTr ⟨131, by decide⟩ 16 hp)) T147_131
      hfix147_131 hinj147_131 hcardT147_131
      (fun i => conj_mem_of_fixedPoints _ _ (T147_131 i) (hfix147_131 i) _)
      ⟨147, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 16 hp) Q2.T147_131_2 Q2.hfix147_131_2 Q2.hinj147_131_2
      Q2.hcardT147_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_131_2 i) (Q2.hfix147_131_2 i) _)
      colCert_147_131_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_131_17 (hp : 17 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 17 (transLenTr ⟨131, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 17 (transLenTr ⟨131, by decide⟩ 17 hp)) T147_131
      hfix147_131 hinj147_131 hcardT147_131
      (fun i => conj_mem_of_fixedPoints _ _ (T147_131 i) (hfix147_131 i) _)
      ⟨147, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 17 hp) Q2.T147_131_2 Q2.hfix147_131_2 Q2.hinj147_131_2
      Q2.hcardT147_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_131_2 i) (Q2.hfix147_131_2 i) _)
      colCert_147_131_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_131_18 (hp : 18 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 18 (transLenTr ⟨131, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 18 (transLenTr ⟨131, by decide⟩ 18 hp)) T147_131
      hfix147_131 hinj147_131 hcardT147_131
      (fun i => conj_mem_of_fixedPoints _ _ (T147_131 i) (hfix147_131 i) _)
      ⟨147, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 18 hp) Q2.T147_131_2 Q2.hfix147_131_2 Q2.hinj147_131_2
      Q2.hcardT147_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_131_2 i) (Q2.hfix147_131_2 i) _)
      colCert_147_131_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_131_19 (hp : 19 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 19 (transLenTr ⟨131, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 19 (transLenTr ⟨131, by decide⟩ 19 hp)) T147_131
      hfix147_131 hinj147_131 hcardT147_131
      (fun i => conj_mem_of_fixedPoints _ _ (T147_131 i) (hfix147_131 i) _)
      ⟨147, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 19 hp) Q2.T147_131_2 Q2.hfix147_131_2 Q2.hinj147_131_2
      Q2.hcardT147_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_131_2 i) (Q2.hfix147_131_2 i) _)
      colCert_147_131_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_131_20 (hp : 20 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 20 (transLenTr ⟨131, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 20 (transLenTr ⟨131, by decide⟩ 20 hp)) T147_131
      hfix147_131 hinj147_131 hcardT147_131
      (fun i => conj_mem_of_fixedPoints _ _ (T147_131 i) (hfix147_131 i) _)
      ⟨147, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 20 hp) Q2.T147_131_2 Q2.hfix147_131_2 Q2.hinj147_131_2
      Q2.hcardT147_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_131_2 i) (Q2.hfix147_131_2 i) _)
      colCert_147_131_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_131_21 (hp : 21 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 21 (transLenTr ⟨131, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 21 (transLenTr ⟨131, by decide⟩ 21 hp)) T147_131
      hfix147_131 hinj147_131 hcardT147_131
      (fun i => conj_mem_of_fixedPoints _ _ (T147_131 i) (hfix147_131 i) _)
      ⟨147, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 21 hp) Q2.T147_131_2 Q2.hfix147_131_2 Q2.hinj147_131_2
      Q2.hcardT147_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_131_2 i) (Q2.hfix147_131_2 i) _)
      colCert_147_131_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_131_22 (hp : 22 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 22 (transLenTr ⟨131, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 22 (transLenTr ⟨131, by decide⟩ 22 hp)) T147_131
      hfix147_131 hinj147_131 hcardT147_131
      (fun i => conj_mem_of_fixedPoints _ _ (T147_131 i) (hfix147_131 i) _)
      ⟨147, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 22 hp) Q2.T147_131_2 Q2.hfix147_131_2 Q2.hinj147_131_2
      Q2.hcardT147_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_131_2 i) (Q2.hfix147_131_2 i) _)
      colCert_147_131_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_131_23 (hp : 23 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 23 (transLenTr ⟨131, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 23 (transLenTr ⟨131, by decide⟩ 23 hp)) T147_131
      hfix147_131 hinj147_131 hcardT147_131
      (fun i => conj_mem_of_fixedPoints _ _ (T147_131 i) (hfix147_131 i) _)
      ⟨147, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 23 hp) Q2.T147_131_2 Q2.hfix147_131_2 Q2.hinj147_131_2
      Q2.hcardT147_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_131_2 i) (Q2.hfix147_131_2 i) _)
      colCert_147_131_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_131_24 (hp : 24 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 24 (transLenTr ⟨131, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 24 (transLenTr ⟨131, by decide⟩ 24 hp)) T147_131
      hfix147_131 hinj147_131 hcardT147_131
      (fun i => conj_mem_of_fixedPoints _ _ (T147_131 i) (hfix147_131 i) _)
      ⟨147, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 24 hp) Q2.T147_131_2 Q2.hfix147_131_2 Q2.hinj147_131_2
      Q2.hcardT147_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_131_2 i) (Q2.hfix147_131_2 i) _)
      colCert_147_131_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_132_0 (hp : 0 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 0 (transLenTr ⟨132, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 0 (transLenTr ⟨132, by decide⟩ 0 hp)) T147_132
      hfix147_132 hinj147_132 hcardT147_132
      (fun i => conj_mem_of_fixedPoints _ _ (T147_132 i) (hfix147_132 i) _)
      ⟨147, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 0 hp) Q2.T147_132_2 Q2.hfix147_132_2 Q2.hinj147_132_2
      Q2.hcardT147_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_132_2 i) (Q2.hfix147_132_2 i) _)
      colCert_147_132_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_132_1 (hp : 1 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 1 (transLenTr ⟨132, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 1 (transLenTr ⟨132, by decide⟩ 1 hp)) T147_132
      hfix147_132 hinj147_132 hcardT147_132
      (fun i => conj_mem_of_fixedPoints _ _ (T147_132 i) (hfix147_132 i) _)
      ⟨147, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 1 hp) Q2.T147_132_2 Q2.hfix147_132_2 Q2.hinj147_132_2
      Q2.hcardT147_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_132_2 i) (Q2.hfix147_132_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨132, by decide⟩ 1 (transLenTr ⟨132, by decide⟩ 1 hp) : ↥(reps ⟨132, by decide⟩)) : Coordinate 1)
        T147_132 = colFn colCertDiv_147_132_1.D1 (m := 1) from colCertDiv_147_132_1.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨132, by decide⟩ 1 hp : ↥(Q2.reps ⟨132, by decide⟩)) : Coordinate 2)
        Q2.T147_132_2 = colFn colCertDiv_147_132_1.D2 (m := 1) from colCertDiv_147_132_1.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_132_1_match


theorem leaf_147_132_2 (hp : 2 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 2 (transLenTr ⟨132, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 2 (transLenTr ⟨132, by decide⟩ 2 hp)) T147_132
      hfix147_132 hinj147_132 hcardT147_132
      (fun i => conj_mem_of_fixedPoints _ _ (T147_132 i) (hfix147_132 i) _)
      ⟨147, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 2 hp) Q2.T147_132_2 Q2.hfix147_132_2 Q2.hinj147_132_2
      Q2.hcardT147_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_132_2 i) (Q2.hfix147_132_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨132, by decide⟩ 2 (transLenTr ⟨132, by decide⟩ 2 hp) : ↥(reps ⟨132, by decide⟩)) : Coordinate 1)
        T147_132 = colFn colCertDiv_147_132_2.D1 (m := 1) from colCertDiv_147_132_2.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨132, by decide⟩ 2 hp : ↥(Q2.reps ⟨132, by decide⟩)) : Coordinate 2)
        Q2.T147_132_2 = colFn colCertDiv_147_132_2.D2 (m := 1) from colCertDiv_147_132_2.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_132_2_match


theorem leaf_147_132_3 (hp : 3 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 3 (transLenTr ⟨132, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 3 (transLenTr ⟨132, by decide⟩ 3 hp)) T147_132
      hfix147_132 hinj147_132 hcardT147_132
      (fun i => conj_mem_of_fixedPoints _ _ (T147_132 i) (hfix147_132 i) _)
      ⟨147, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 3 hp) Q2.T147_132_2 Q2.hfix147_132_2 Q2.hinj147_132_2
      Q2.hcardT147_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_132_2 i) (Q2.hfix147_132_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨132, by decide⟩ 3 (transLenTr ⟨132, by decide⟩ 3 hp) : ↥(reps ⟨132, by decide⟩)) : Coordinate 1)
        T147_132 = colFn colCertDiv_147_132_3.D1 (m := 1) from colCertDiv_147_132_3.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨132, by decide⟩ 3 hp : ↥(Q2.reps ⟨132, by decide⟩)) : Coordinate 2)
        Q2.T147_132_2 = colFn colCertDiv_147_132_3.D2 (m := 1) from colCertDiv_147_132_3.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_132_3_match


theorem leaf_147_132_4 (hp : 4 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 4 (transLenTr ⟨132, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 4 (transLenTr ⟨132, by decide⟩ 4 hp)) T147_132
      hfix147_132 hinj147_132 hcardT147_132
      (fun i => conj_mem_of_fixedPoints _ _ (T147_132 i) (hfix147_132 i) _)
      ⟨147, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 4 hp) Q2.T147_132_2 Q2.hfix147_132_2 Q2.hinj147_132_2
      Q2.hcardT147_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_132_2 i) (Q2.hfix147_132_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨132, by decide⟩ 4 (transLenTr ⟨132, by decide⟩ 4 hp) : ↥(reps ⟨132, by decide⟩)) : Coordinate 1)
        T147_132 = colFn colCertDiv_147_132_4.D1 (m := 1) from colCertDiv_147_132_4.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨132, by decide⟩ 4 hp : ↥(Q2.reps ⟨132, by decide⟩)) : Coordinate 2)
        Q2.T147_132_2 = colFn colCertDiv_147_132_4.D2 (m := 1) from colCertDiv_147_132_4.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_132_4_match


theorem leaf_147_132_5 (hp : 5 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 5 (transLenTr ⟨132, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 5 (transLenTr ⟨132, by decide⟩ 5 hp)) T147_132
      hfix147_132 hinj147_132 hcardT147_132
      (fun i => conj_mem_of_fixedPoints _ _ (T147_132 i) (hfix147_132 i) _)
      ⟨147, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 5 hp) Q2.T147_132_2 Q2.hfix147_132_2 Q2.hinj147_132_2
      Q2.hcardT147_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_132_2 i) (Q2.hfix147_132_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨132, by decide⟩ 5 (transLenTr ⟨132, by decide⟩ 5 hp) : ↥(reps ⟨132, by decide⟩)) : Coordinate 1)
        T147_132 = colFn colCertDiv_147_132_5.D1 (m := 1) from colCertDiv_147_132_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨132, by decide⟩ 5 hp : ↥(Q2.reps ⟨132, by decide⟩)) : Coordinate 2)
        Q2.T147_132_2 = colFn colCertDiv_147_132_5.D2 (m := 1) from colCertDiv_147_132_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_132_5_match


theorem leaf_147_132_6 (hp : 6 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 6 (transLenTr ⟨132, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 6 (transLenTr ⟨132, by decide⟩ 6 hp)) T147_132
      hfix147_132 hinj147_132 hcardT147_132
      (fun i => conj_mem_of_fixedPoints _ _ (T147_132 i) (hfix147_132 i) _)
      ⟨147, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 6 hp) Q2.T147_132_2 Q2.hfix147_132_2 Q2.hinj147_132_2
      Q2.hcardT147_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_132_2 i) (Q2.hfix147_132_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨132, by decide⟩ 6 (transLenTr ⟨132, by decide⟩ 6 hp) : ↥(reps ⟨132, by decide⟩)) : Coordinate 1)
        T147_132 = colFn colCertDiv_147_132_6.D1 (m := 1) from colCertDiv_147_132_6.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨132, by decide⟩ 6 hp : ↥(Q2.reps ⟨132, by decide⟩)) : Coordinate 2)
        Q2.T147_132_2 = colFn colCertDiv_147_132_6.D2 (m := 1) from colCertDiv_147_132_6.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_132_6_match


theorem leaf_147_132_7 (hp : 7 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 7 (transLenTr ⟨132, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 7 (transLenTr ⟨132, by decide⟩ 7 hp)) T147_132
      hfix147_132 hinj147_132 hcardT147_132
      (fun i => conj_mem_of_fixedPoints _ _ (T147_132 i) (hfix147_132 i) _)
      ⟨147, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 7 hp) Q2.T147_132_2 Q2.hfix147_132_2 Q2.hinj147_132_2
      Q2.hcardT147_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_132_2 i) (Q2.hfix147_132_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨132, by decide⟩ 7 (transLenTr ⟨132, by decide⟩ 7 hp) : ↥(reps ⟨132, by decide⟩)) : Coordinate 1)
        T147_132 = colFn colCertDiv_147_132_7.D1 (m := 1) from colCertDiv_147_132_7.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨132, by decide⟩ 7 hp : ↥(Q2.reps ⟨132, by decide⟩)) : Coordinate 2)
        Q2.T147_132_2 = colFn colCertDiv_147_132_7.D2 (m := 1) from colCertDiv_147_132_7.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_132_7_match


theorem leaf_147_132_8 (hp : 8 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 8 (transLenTr ⟨132, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 8 (transLenTr ⟨132, by decide⟩ 8 hp)) T147_132
      hfix147_132 hinj147_132 hcardT147_132
      (fun i => conj_mem_of_fixedPoints _ _ (T147_132 i) (hfix147_132 i) _)
      ⟨147, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 8 hp) Q2.T147_132_2 Q2.hfix147_132_2 Q2.hinj147_132_2
      Q2.hcardT147_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_132_2 i) (Q2.hfix147_132_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨132, by decide⟩ 8 (transLenTr ⟨132, by decide⟩ 8 hp) : ↥(reps ⟨132, by decide⟩)) : Coordinate 1)
        T147_132 = colFn colCertDiv_147_132_8.D1 (m := 1) from colCertDiv_147_132_8.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨132, by decide⟩ 8 hp : ↥(Q2.reps ⟨132, by decide⟩)) : Coordinate 2)
        Q2.T147_132_2 = colFn colCertDiv_147_132_8.D2 (m := 1) from colCertDiv_147_132_8.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_132_8_match


theorem leaf_147_132_9 (hp : 9 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 9 (transLenTr ⟨132, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 9 (transLenTr ⟨132, by decide⟩ 9 hp)) T147_132
      hfix147_132 hinj147_132 hcardT147_132
      (fun i => conj_mem_of_fixedPoints _ _ (T147_132 i) (hfix147_132 i) _)
      ⟨147, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 9 hp) Q2.T147_132_2 Q2.hfix147_132_2 Q2.hinj147_132_2
      Q2.hcardT147_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_132_2 i) (Q2.hfix147_132_2 i) _)
      colCert_147_132_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_132_10 (hp : 10 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 10 (transLenTr ⟨132, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 10 (transLenTr ⟨132, by decide⟩ 10 hp)) T147_132
      hfix147_132 hinj147_132 hcardT147_132
      (fun i => conj_mem_of_fixedPoints _ _ (T147_132 i) (hfix147_132 i) _)
      ⟨147, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 10 hp) Q2.T147_132_2 Q2.hfix147_132_2 Q2.hinj147_132_2
      Q2.hcardT147_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_132_2 i) (Q2.hfix147_132_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨132, by decide⟩ 10 (transLenTr ⟨132, by decide⟩ 10 hp) : ↥(reps ⟨132, by decide⟩)) : Coordinate 1)
        T147_132 = colFn colCertDiv_147_132_10.D1 (m := 1) from colCertDiv_147_132_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨132, by decide⟩ 10 hp : ↥(Q2.reps ⟨132, by decide⟩)) : Coordinate 2)
        Q2.T147_132_2 = colFn colCertDiv_147_132_10.D2 (m := 1) from colCertDiv_147_132_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_132_10_match


theorem leaf_147_132_11 (hp : 11 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 11 (transLenTr ⟨132, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 11 (transLenTr ⟨132, by decide⟩ 11 hp)) T147_132
      hfix147_132 hinj147_132 hcardT147_132
      (fun i => conj_mem_of_fixedPoints _ _ (T147_132 i) (hfix147_132 i) _)
      ⟨147, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 11 hp) Q2.T147_132_2 Q2.hfix147_132_2 Q2.hinj147_132_2
      Q2.hcardT147_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_132_2 i) (Q2.hfix147_132_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨132, by decide⟩ 11 (transLenTr ⟨132, by decide⟩ 11 hp) : ↥(reps ⟨132, by decide⟩)) : Coordinate 1)
        T147_132 = colFn colCertDiv_147_132_11.D1 (m := 1) from colCertDiv_147_132_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨132, by decide⟩ 11 hp : ↥(Q2.reps ⟨132, by decide⟩)) : Coordinate 2)
        Q2.T147_132_2 = colFn colCertDiv_147_132_11.D2 (m := 1) from colCertDiv_147_132_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_132_11_match


theorem leaf_147_132_12 (hp : 12 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 12 (transLenTr ⟨132, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 12 (transLenTr ⟨132, by decide⟩ 12 hp)) T147_132
      hfix147_132 hinj147_132 hcardT147_132
      (fun i => conj_mem_of_fixedPoints _ _ (T147_132 i) (hfix147_132 i) _)
      ⟨147, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 12 hp) Q2.T147_132_2 Q2.hfix147_132_2 Q2.hinj147_132_2
      Q2.hcardT147_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_132_2 i) (Q2.hfix147_132_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨132, by decide⟩ 12 (transLenTr ⟨132, by decide⟩ 12 hp) : ↥(reps ⟨132, by decide⟩)) : Coordinate 1)
        T147_132 = colFn colCertDiv_147_132_12.D1 (m := 1) from colCertDiv_147_132_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨132, by decide⟩ 12 hp : ↥(Q2.reps ⟨132, by decide⟩)) : Coordinate 2)
        Q2.T147_132_2 = colFn colCertDiv_147_132_12.D2 (m := 1) from colCertDiv_147_132_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_132_12_match


theorem leaf_147_132_13 (hp : 13 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 13 (transLenTr ⟨132, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 13 (transLenTr ⟨132, by decide⟩ 13 hp)) T147_132
      hfix147_132 hinj147_132 hcardT147_132
      (fun i => conj_mem_of_fixedPoints _ _ (T147_132 i) (hfix147_132 i) _)
      ⟨147, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 13 hp) Q2.T147_132_2 Q2.hfix147_132_2 Q2.hinj147_132_2
      Q2.hcardT147_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_132_2 i) (Q2.hfix147_132_2 i) _)
      colCert_147_132_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_132_14 (hp : 14 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 14 (transLenTr ⟨132, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 14 (transLenTr ⟨132, by decide⟩ 14 hp)) T147_132
      hfix147_132 hinj147_132 hcardT147_132
      (fun i => conj_mem_of_fixedPoints _ _ (T147_132 i) (hfix147_132 i) _)
      ⟨147, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 14 hp) Q2.T147_132_2 Q2.hfix147_132_2 Q2.hinj147_132_2
      Q2.hcardT147_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_132_2 i) (Q2.hfix147_132_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨132, by decide⟩ 14 (transLenTr ⟨132, by decide⟩ 14 hp) : ↥(reps ⟨132, by decide⟩)) : Coordinate 1)
        T147_132 = colFn colCertDiv_147_132_14.D1 (m := 1) from colCertDiv_147_132_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨132, by decide⟩ 14 hp : ↥(Q2.reps ⟨132, by decide⟩)) : Coordinate 2)
        Q2.T147_132_2 = colFn colCertDiv_147_132_14.D2 (m := 1) from colCertDiv_147_132_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_132_14_match


theorem leaf_147_132_15 (hp : 15 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 15 (transLenTr ⟨132, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 15 (transLenTr ⟨132, by decide⟩ 15 hp)) T147_132
      hfix147_132 hinj147_132 hcardT147_132
      (fun i => conj_mem_of_fixedPoints _ _ (T147_132 i) (hfix147_132 i) _)
      ⟨147, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 15 hp) Q2.T147_132_2 Q2.hfix147_132_2 Q2.hinj147_132_2
      Q2.hcardT147_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_132_2 i) (Q2.hfix147_132_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨132, by decide⟩ 15 (transLenTr ⟨132, by decide⟩ 15 hp) : ↥(reps ⟨132, by decide⟩)) : Coordinate 1)
        T147_132 = colFn colCertDiv_147_132_15.D1 (m := 1) from colCertDiv_147_132_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨132, by decide⟩ 15 hp : ↥(Q2.reps ⟨132, by decide⟩)) : Coordinate 2)
        Q2.T147_132_2 = colFn colCertDiv_147_132_15.D2 (m := 1) from colCertDiv_147_132_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_132_15_match


theorem leaf_147_132_16 (hp : 16 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 16 (transLenTr ⟨132, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 16 (transLenTr ⟨132, by decide⟩ 16 hp)) T147_132
      hfix147_132 hinj147_132 hcardT147_132
      (fun i => conj_mem_of_fixedPoints _ _ (T147_132 i) (hfix147_132 i) _)
      ⟨147, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 16 hp) Q2.T147_132_2 Q2.hfix147_132_2 Q2.hinj147_132_2
      Q2.hcardT147_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_132_2 i) (Q2.hfix147_132_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨132, by decide⟩ 16 (transLenTr ⟨132, by decide⟩ 16 hp) : ↥(reps ⟨132, by decide⟩)) : Coordinate 1)
        T147_132 = colFn colCertDiv_147_132_16.D1 (m := 1) from colCertDiv_147_132_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨132, by decide⟩ 16 hp : ↥(Q2.reps ⟨132, by decide⟩)) : Coordinate 2)
        Q2.T147_132_2 = colFn colCertDiv_147_132_16.D2 (m := 1) from colCertDiv_147_132_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_132_16_match


theorem leaf_147_132_17 (hp : 17 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 17 (transLenTr ⟨132, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 17 (transLenTr ⟨132, by decide⟩ 17 hp)) T147_132
      hfix147_132 hinj147_132 hcardT147_132
      (fun i => conj_mem_of_fixedPoints _ _ (T147_132 i) (hfix147_132 i) _)
      ⟨147, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 17 hp) Q2.T147_132_2 Q2.hfix147_132_2 Q2.hinj147_132_2
      Q2.hcardT147_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_132_2 i) (Q2.hfix147_132_2 i) _)
      colCert_147_132_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_132_18 (hp : 18 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 18 (transLenTr ⟨132, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 18 (transLenTr ⟨132, by decide⟩ 18 hp)) T147_132
      hfix147_132 hinj147_132 hcardT147_132
      (fun i => conj_mem_of_fixedPoints _ _ (T147_132 i) (hfix147_132 i) _)
      ⟨147, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 18 hp) Q2.T147_132_2 Q2.hfix147_132_2 Q2.hinj147_132_2
      Q2.hcardT147_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_132_2 i) (Q2.hfix147_132_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨132, by decide⟩ 18 (transLenTr ⟨132, by decide⟩ 18 hp) : ↥(reps ⟨132, by decide⟩)) : Coordinate 1)
        T147_132 = colFn colCertDiv_147_132_18.D1 (m := 1) from colCertDiv_147_132_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨132, by decide⟩ 18 hp : ↥(Q2.reps ⟨132, by decide⟩)) : Coordinate 2)
        Q2.T147_132_2 = colFn colCertDiv_147_132_18.D2 (m := 1) from colCertDiv_147_132_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_132_18_match


theorem leaf_147_132_19 (hp : 19 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 19 (transLenTr ⟨132, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 19 (transLenTr ⟨132, by decide⟩ 19 hp)) T147_132
      hfix147_132 hinj147_132 hcardT147_132
      (fun i => conj_mem_of_fixedPoints _ _ (T147_132 i) (hfix147_132 i) _)
      ⟨147, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 19 hp) Q2.T147_132_2 Q2.hfix147_132_2 Q2.hinj147_132_2
      Q2.hcardT147_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_132_2 i) (Q2.hfix147_132_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨132, by decide⟩ 19 (transLenTr ⟨132, by decide⟩ 19 hp) : ↥(reps ⟨132, by decide⟩)) : Coordinate 1)
        T147_132 = colFn colCertDiv_147_132_19.D1 (m := 1) from colCertDiv_147_132_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨132, by decide⟩ 19 hp : ↥(Q2.reps ⟨132, by decide⟩)) : Coordinate 2)
        Q2.T147_132_2 = colFn colCertDiv_147_132_19.D2 (m := 1) from colCertDiv_147_132_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_132_19_match


theorem leaf_147_132_20 (hp : 20 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 20 (transLenTr ⟨132, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 20 (transLenTr ⟨132, by decide⟩ 20 hp)) T147_132
      hfix147_132 hinj147_132 hcardT147_132
      (fun i => conj_mem_of_fixedPoints _ _ (T147_132 i) (hfix147_132 i) _)
      ⟨147, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 20 hp) Q2.T147_132_2 Q2.hfix147_132_2 Q2.hinj147_132_2
      Q2.hcardT147_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_132_2 i) (Q2.hfix147_132_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨132, by decide⟩ 20 (transLenTr ⟨132, by decide⟩ 20 hp) : ↥(reps ⟨132, by decide⟩)) : Coordinate 1)
        T147_132 = colFn colCertDiv_147_132_20.D1 (m := 1) from colCertDiv_147_132_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨132, by decide⟩ 20 hp : ↥(Q2.reps ⟨132, by decide⟩)) : Coordinate 2)
        Q2.T147_132_2 = colFn colCertDiv_147_132_20.D2 (m := 1) from colCertDiv_147_132_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_132_20_match


theorem leaf_147_132_21 (hp : 21 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 21 (transLenTr ⟨132, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 21 (transLenTr ⟨132, by decide⟩ 21 hp)) T147_132
      hfix147_132 hinj147_132 hcardT147_132
      (fun i => conj_mem_of_fixedPoints _ _ (T147_132 i) (hfix147_132 i) _)
      ⟨147, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 21 hp) Q2.T147_132_2 Q2.hfix147_132_2 Q2.hinj147_132_2
      Q2.hcardT147_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_132_2 i) (Q2.hfix147_132_2 i) _)
      colCert_147_132_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_132_22 (hp : 22 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 22 (transLenTr ⟨132, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 22 (transLenTr ⟨132, by decide⟩ 22 hp)) T147_132
      hfix147_132 hinj147_132 hcardT147_132
      (fun i => conj_mem_of_fixedPoints _ _ (T147_132 i) (hfix147_132 i) _)
      ⟨147, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 22 hp) Q2.T147_132_2 Q2.hfix147_132_2 Q2.hinj147_132_2
      Q2.hcardT147_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_132_2 i) (Q2.hfix147_132_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨132, by decide⟩ 22 (transLenTr ⟨132, by decide⟩ 22 hp) : ↥(reps ⟨132, by decide⟩)) : Coordinate 1)
        T147_132 = colFn colCertDiv_147_132_22.D1 (m := 1) from colCertDiv_147_132_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨132, by decide⟩ 22 hp : ↥(Q2.reps ⟨132, by decide⟩)) : Coordinate 2)
        Q2.T147_132_2 = colFn colCertDiv_147_132_22.D2 (m := 1) from colCertDiv_147_132_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_132_22_match


theorem leaf_147_132_23 (hp : 23 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 23 (transLenTr ⟨132, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 23 (transLenTr ⟨132, by decide⟩ 23 hp)) T147_132
      hfix147_132 hinj147_132 hcardT147_132
      (fun i => conj_mem_of_fixedPoints _ _ (T147_132 i) (hfix147_132 i) _)
      ⟨147, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 23 hp) Q2.T147_132_2 Q2.hfix147_132_2 Q2.hinj147_132_2
      Q2.hcardT147_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_132_2 i) (Q2.hfix147_132_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨132, by decide⟩ 23 (transLenTr ⟨132, by decide⟩ 23 hp) : ↥(reps ⟨132, by decide⟩)) : Coordinate 1)
        T147_132 = colFn colCertDiv_147_132_23.D1 (m := 1) from colCertDiv_147_132_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨132, by decide⟩ 23 hp : ↥(Q2.reps ⟨132, by decide⟩)) : Coordinate 2)
        Q2.T147_132_2 = colFn colCertDiv_147_132_23.D2 (m := 1) from colCertDiv_147_132_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_132_23_match


theorem leaf_147_132_24 (hp : 24 < (Q2.transData.getD 132 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ 24 (transLenTr ⟨132, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨132, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨132, by decide⟩ 24 (transLenTr ⟨132, by decide⟩ 24 hp)) T147_132
      hfix147_132 hinj147_132 hcardT147_132
      (fun i => conj_mem_of_fixedPoints _ _ (T147_132 i) (hfix147_132 i) _)
      ⟨147, by decide⟩ ⟨132, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨132, by decide⟩ 24 hp) Q2.T147_132_2 Q2.hfix147_132_2 Q2.hinj147_132_2
      Q2.hcardT147_132_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_132_2 i) (Q2.hfix147_132_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨132, by decide⟩ 24 (transLenTr ⟨132, by decide⟩ 24 hp) : ↥(reps ⟨132, by decide⟩)) : Coordinate 1)
        T147_132 = colFn colCertDiv_147_132_24.D1 (m := 1) from colCertDiv_147_132_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨132, by decide⟩ 24 hp : ↥(Q2.reps ⟨132, by decide⟩)) : Coordinate 2)
        Q2.T147_132_2 = colFn colCertDiv_147_132_24.D2 (m := 1) from colCertDiv_147_132_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_132_24_match


theorem leaf_147_133_0 (hp : 0 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 0 (transLenTr ⟨133, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 0 (transLenTr ⟨133, by decide⟩ 0 hp)) T147_133
      hfix147_133 hinj147_133 hcardT147_133
      (fun i => conj_mem_of_fixedPoints _ _ (T147_133 i) (hfix147_133 i) _)
      ⟨147, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 0 hp) Q2.T147_133_2 Q2.hfix147_133_2 Q2.hinj147_133_2
      Q2.hcardT147_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_133_2 i) (Q2.hfix147_133_2 i) _)
      colCert_147_133_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_133_1 (hp : 1 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 1 (transLenTr ⟨133, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 1 (transLenTr ⟨133, by decide⟩ 1 hp)) T147_133
      hfix147_133 hinj147_133 hcardT147_133
      (fun i => conj_mem_of_fixedPoints _ _ (T147_133 i) (hfix147_133 i) _)
      ⟨147, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 1 hp) Q2.T147_133_2 Q2.hfix147_133_2 Q2.hinj147_133_2
      Q2.hcardT147_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_133_2 i) (Q2.hfix147_133_2 i) _)
      colCert_147_133_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_133_2 (hp : 2 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 2 (transLenTr ⟨133, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 2 (transLenTr ⟨133, by decide⟩ 2 hp)) T147_133
      hfix147_133 hinj147_133 hcardT147_133
      (fun i => conj_mem_of_fixedPoints _ _ (T147_133 i) (hfix147_133 i) _)
      ⟨147, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 2 hp) Q2.T147_133_2 Q2.hfix147_133_2 Q2.hinj147_133_2
      Q2.hcardT147_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_133_2 i) (Q2.hfix147_133_2 i) _)
      colCert_147_133_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_133_3 (hp : 3 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 3 (transLenTr ⟨133, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 3 (transLenTr ⟨133, by decide⟩ 3 hp)) T147_133
      hfix147_133 hinj147_133 hcardT147_133
      (fun i => conj_mem_of_fixedPoints _ _ (T147_133 i) (hfix147_133 i) _)
      ⟨147, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 3 hp) Q2.T147_133_2 Q2.hfix147_133_2 Q2.hinj147_133_2
      Q2.hcardT147_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_133_2 i) (Q2.hfix147_133_2 i) _)
      colCert_147_133_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_133_4 (hp : 4 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 4 (transLenTr ⟨133, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 4 (transLenTr ⟨133, by decide⟩ 4 hp)) T147_133
      hfix147_133 hinj147_133 hcardT147_133
      (fun i => conj_mem_of_fixedPoints _ _ (T147_133 i) (hfix147_133 i) _)
      ⟨147, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 4 hp) Q2.T147_133_2 Q2.hfix147_133_2 Q2.hinj147_133_2
      Q2.hcardT147_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_133_2 i) (Q2.hfix147_133_2 i) _)
      colCert_147_133_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_133_5 (hp : 5 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 5 (transLenTr ⟨133, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 5 (transLenTr ⟨133, by decide⟩ 5 hp)) T147_133
      hfix147_133 hinj147_133 hcardT147_133
      (fun i => conj_mem_of_fixedPoints _ _ (T147_133 i) (hfix147_133 i) _)
      ⟨147, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 5 hp) Q2.T147_133_2 Q2.hfix147_133_2 Q2.hinj147_133_2
      Q2.hcardT147_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_133_2 i) (Q2.hfix147_133_2 i) _)
      colCert_147_133_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_133_6 (hp : 6 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 6 (transLenTr ⟨133, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 6 (transLenTr ⟨133, by decide⟩ 6 hp)) T147_133
      hfix147_133 hinj147_133 hcardT147_133
      (fun i => conj_mem_of_fixedPoints _ _ (T147_133 i) (hfix147_133 i) _)
      ⟨147, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 6 hp) Q2.T147_133_2 Q2.hfix147_133_2 Q2.hinj147_133_2
      Q2.hcardT147_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_133_2 i) (Q2.hfix147_133_2 i) _)
      colCert_147_133_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_133_7 (hp : 7 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 7 (transLenTr ⟨133, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 7 (transLenTr ⟨133, by decide⟩ 7 hp)) T147_133
      hfix147_133 hinj147_133 hcardT147_133
      (fun i => conj_mem_of_fixedPoints _ _ (T147_133 i) (hfix147_133 i) _)
      ⟨147, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 7 hp) Q2.T147_133_2 Q2.hfix147_133_2 Q2.hinj147_133_2
      Q2.hcardT147_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_133_2 i) (Q2.hfix147_133_2 i) _)
      colCert_147_133_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_133_8 (hp : 8 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 8 (transLenTr ⟨133, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 8 (transLenTr ⟨133, by decide⟩ 8 hp)) T147_133
      hfix147_133 hinj147_133 hcardT147_133
      (fun i => conj_mem_of_fixedPoints _ _ (T147_133 i) (hfix147_133 i) _)
      ⟨147, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 8 hp) Q2.T147_133_2 Q2.hfix147_133_2 Q2.hinj147_133_2
      Q2.hcardT147_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_133_2 i) (Q2.hfix147_133_2 i) _)
      colCert_147_133_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_133_9 (hp : 9 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 9 (transLenTr ⟨133, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 9 (transLenTr ⟨133, by decide⟩ 9 hp)) T147_133
      hfix147_133 hinj147_133 hcardT147_133
      (fun i => conj_mem_of_fixedPoints _ _ (T147_133 i) (hfix147_133 i) _)
      ⟨147, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 9 hp) Q2.T147_133_2 Q2.hfix147_133_2 Q2.hinj147_133_2
      Q2.hcardT147_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_133_2 i) (Q2.hfix147_133_2 i) _)
      colCert_147_133_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_133_10 (hp : 10 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 10 (transLenTr ⟨133, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 10 (transLenTr ⟨133, by decide⟩ 10 hp)) T147_133
      hfix147_133 hinj147_133 hcardT147_133
      (fun i => conj_mem_of_fixedPoints _ _ (T147_133 i) (hfix147_133 i) _)
      ⟨147, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 10 hp) Q2.T147_133_2 Q2.hfix147_133_2 Q2.hinj147_133_2
      Q2.hcardT147_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_133_2 i) (Q2.hfix147_133_2 i) _)
      colCert_147_133_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_133_11 (hp : 11 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 11 (transLenTr ⟨133, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 11 (transLenTr ⟨133, by decide⟩ 11 hp)) T147_133
      hfix147_133 hinj147_133 hcardT147_133
      (fun i => conj_mem_of_fixedPoints _ _ (T147_133 i) (hfix147_133 i) _)
      ⟨147, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 11 hp) Q2.T147_133_2 Q2.hfix147_133_2 Q2.hinj147_133_2
      Q2.hcardT147_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_133_2 i) (Q2.hfix147_133_2 i) _)
      colCert_147_133_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_133_12 (hp : 12 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 12 (transLenTr ⟨133, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 12 (transLenTr ⟨133, by decide⟩ 12 hp)) T147_133
      hfix147_133 hinj147_133 hcardT147_133
      (fun i => conj_mem_of_fixedPoints _ _ (T147_133 i) (hfix147_133 i) _)
      ⟨147, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 12 hp) Q2.T147_133_2 Q2.hfix147_133_2 Q2.hinj147_133_2
      Q2.hcardT147_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_133_2 i) (Q2.hfix147_133_2 i) _)
      colCert_147_133_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_133_13 (hp : 13 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 13 (transLenTr ⟨133, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 13 (transLenTr ⟨133, by decide⟩ 13 hp)) T147_133
      hfix147_133 hinj147_133 hcardT147_133
      (fun i => conj_mem_of_fixedPoints _ _ (T147_133 i) (hfix147_133 i) _)
      ⟨147, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 13 hp) Q2.T147_133_2 Q2.hfix147_133_2 Q2.hinj147_133_2
      Q2.hcardT147_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_133_2 i) (Q2.hfix147_133_2 i) _)
      colCert_147_133_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_133_14 (hp : 14 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 14 (transLenTr ⟨133, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 14 (transLenTr ⟨133, by decide⟩ 14 hp)) T147_133
      hfix147_133 hinj147_133 hcardT147_133
      (fun i => conj_mem_of_fixedPoints _ _ (T147_133 i) (hfix147_133 i) _)
      ⟨147, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 14 hp) Q2.T147_133_2 Q2.hfix147_133_2 Q2.hinj147_133_2
      Q2.hcardT147_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_133_2 i) (Q2.hfix147_133_2 i) _)
      colCert_147_133_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_133_15 (hp : 15 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 15 (transLenTr ⟨133, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 15 (transLenTr ⟨133, by decide⟩ 15 hp)) T147_133
      hfix147_133 hinj147_133 hcardT147_133
      (fun i => conj_mem_of_fixedPoints _ _ (T147_133 i) (hfix147_133 i) _)
      ⟨147, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 15 hp) Q2.T147_133_2 Q2.hfix147_133_2 Q2.hinj147_133_2
      Q2.hcardT147_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_133_2 i) (Q2.hfix147_133_2 i) _)
      colCert_147_133_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_133_16 (hp : 16 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 16 (transLenTr ⟨133, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 16 (transLenTr ⟨133, by decide⟩ 16 hp)) T147_133
      hfix147_133 hinj147_133 hcardT147_133
      (fun i => conj_mem_of_fixedPoints _ _ (T147_133 i) (hfix147_133 i) _)
      ⟨147, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 16 hp) Q2.T147_133_2 Q2.hfix147_133_2 Q2.hinj147_133_2
      Q2.hcardT147_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_133_2 i) (Q2.hfix147_133_2 i) _)
      colCert_147_133_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_133_17 (hp : 17 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 17 (transLenTr ⟨133, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 17 (transLenTr ⟨133, by decide⟩ 17 hp)) T147_133
      hfix147_133 hinj147_133 hcardT147_133
      (fun i => conj_mem_of_fixedPoints _ _ (T147_133 i) (hfix147_133 i) _)
      ⟨147, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 17 hp) Q2.T147_133_2 Q2.hfix147_133_2 Q2.hinj147_133_2
      Q2.hcardT147_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_133_2 i) (Q2.hfix147_133_2 i) _)
      colCert_147_133_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_133_18 (hp : 18 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 18 (transLenTr ⟨133, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 18 (transLenTr ⟨133, by decide⟩ 18 hp)) T147_133
      hfix147_133 hinj147_133 hcardT147_133
      (fun i => conj_mem_of_fixedPoints _ _ (T147_133 i) (hfix147_133 i) _)
      ⟨147, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 18 hp) Q2.T147_133_2 Q2.hfix147_133_2 Q2.hinj147_133_2
      Q2.hcardT147_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_133_2 i) (Q2.hfix147_133_2 i) _)
      colCert_147_133_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_133_19 (hp : 19 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 19 (transLenTr ⟨133, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 19 (transLenTr ⟨133, by decide⟩ 19 hp)) T147_133
      hfix147_133 hinj147_133 hcardT147_133
      (fun i => conj_mem_of_fixedPoints _ _ (T147_133 i) (hfix147_133 i) _)
      ⟨147, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 19 hp) Q2.T147_133_2 Q2.hfix147_133_2 Q2.hinj147_133_2
      Q2.hcardT147_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_133_2 i) (Q2.hfix147_133_2 i) _)
      colCert_147_133_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_133_20 (hp : 20 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 20 (transLenTr ⟨133, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 20 (transLenTr ⟨133, by decide⟩ 20 hp)) T147_133
      hfix147_133 hinj147_133 hcardT147_133
      (fun i => conj_mem_of_fixedPoints _ _ (T147_133 i) (hfix147_133 i) _)
      ⟨147, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 20 hp) Q2.T147_133_2 Q2.hfix147_133_2 Q2.hinj147_133_2
      Q2.hcardT147_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_133_2 i) (Q2.hfix147_133_2 i) _)
      colCert_147_133_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_133_21 (hp : 21 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 21 (transLenTr ⟨133, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 21 (transLenTr ⟨133, by decide⟩ 21 hp)) T147_133
      hfix147_133 hinj147_133 hcardT147_133
      (fun i => conj_mem_of_fixedPoints _ _ (T147_133 i) (hfix147_133 i) _)
      ⟨147, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 21 hp) Q2.T147_133_2 Q2.hfix147_133_2 Q2.hinj147_133_2
      Q2.hcardT147_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_133_2 i) (Q2.hfix147_133_2 i) _)
      colCert_147_133_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_133_22 (hp : 22 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 22 (transLenTr ⟨133, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 22 (transLenTr ⟨133, by decide⟩ 22 hp)) T147_133
      hfix147_133 hinj147_133 hcardT147_133
      (fun i => conj_mem_of_fixedPoints _ _ (T147_133 i) (hfix147_133 i) _)
      ⟨147, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 22 hp) Q2.T147_133_2 Q2.hfix147_133_2 Q2.hinj147_133_2
      Q2.hcardT147_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_133_2 i) (Q2.hfix147_133_2 i) _)
      colCert_147_133_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_133_23 (hp : 23 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 23 (transLenTr ⟨133, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 23 (transLenTr ⟨133, by decide⟩ 23 hp)) T147_133
      hfix147_133 hinj147_133 hcardT147_133
      (fun i => conj_mem_of_fixedPoints _ _ (T147_133 i) (hfix147_133 i) _)
      ⟨147, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 23 hp) Q2.T147_133_2 Q2.hfix147_133_2 Q2.hinj147_133_2
      Q2.hcardT147_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_133_2 i) (Q2.hfix147_133_2 i) _)
      colCert_147_133_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_133_24 (hp : 24 < (Q2.transData.getD 133 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ 24 (transLenTr ⟨133, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨133, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨133, by decide⟩ 24 (transLenTr ⟨133, by decide⟩ 24 hp)) T147_133
      hfix147_133 hinj147_133 hcardT147_133
      (fun i => conj_mem_of_fixedPoints _ _ (T147_133 i) (hfix147_133 i) _)
      ⟨147, by decide⟩ ⟨133, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨133, by decide⟩ 24 hp) Q2.T147_133_2 Q2.hfix147_133_2 Q2.hinj147_133_2
      Q2.hcardT147_133_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_133_2 i) (Q2.hfix147_133_2 i) _)
      colCert_147_133_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_134_0 (hp : 0 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 0 (transLenTr ⟨134, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 0 (transLenTr ⟨134, by decide⟩ 0 hp)) T147_134
      hfix147_134 hinj147_134 hcardT147_134
      (fun i => conj_mem_of_fixedPoints _ _ (T147_134 i) (hfix147_134 i) _)
      ⟨147, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 0 hp) Q2.T147_134_2 Q2.hfix147_134_2 Q2.hinj147_134_2
      Q2.hcardT147_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_134_2 i) (Q2.hfix147_134_2 i) _)
      colCert_147_134_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_134_1 (hp : 1 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 1 (transLenTr ⟨134, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 1 (transLenTr ⟨134, by decide⟩ 1 hp)) T147_134
      hfix147_134 hinj147_134 hcardT147_134
      (fun i => conj_mem_of_fixedPoints _ _ (T147_134 i) (hfix147_134 i) _)
      ⟨147, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 1 hp) Q2.T147_134_2 Q2.hfix147_134_2 Q2.hinj147_134_2
      Q2.hcardT147_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_134_2 i) (Q2.hfix147_134_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨134, by decide⟩ 1 (transLenTr ⟨134, by decide⟩ 1 hp) : ↥(reps ⟨134, by decide⟩)) : Coordinate 1)
        T147_134 = colFn colCertDiv_147_134_1.D1 (m := 1) from colCertDiv_147_134_1.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨134, by decide⟩ 1 hp : ↥(Q2.reps ⟨134, by decide⟩)) : Coordinate 2)
        Q2.T147_134_2 = colFn colCertDiv_147_134_1.D2 (m := 1) from colCertDiv_147_134_1.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_134_1_match


theorem leaf_147_134_2 (hp : 2 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 2 (transLenTr ⟨134, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 2 (transLenTr ⟨134, by decide⟩ 2 hp)) T147_134
      hfix147_134 hinj147_134 hcardT147_134
      (fun i => conj_mem_of_fixedPoints _ _ (T147_134 i) (hfix147_134 i) _)
      ⟨147, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 2 hp) Q2.T147_134_2 Q2.hfix147_134_2 Q2.hinj147_134_2
      Q2.hcardT147_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_134_2 i) (Q2.hfix147_134_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨134, by decide⟩ 2 (transLenTr ⟨134, by decide⟩ 2 hp) : ↥(reps ⟨134, by decide⟩)) : Coordinate 1)
        T147_134 = colFn colCertDiv_147_134_2.D1 (m := 1) from colCertDiv_147_134_2.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨134, by decide⟩ 2 hp : ↥(Q2.reps ⟨134, by decide⟩)) : Coordinate 2)
        Q2.T147_134_2 = colFn colCertDiv_147_134_2.D2 (m := 1) from colCertDiv_147_134_2.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_134_2_match


theorem leaf_147_134_3 (hp : 3 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 3 (transLenTr ⟨134, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 3 (transLenTr ⟨134, by decide⟩ 3 hp)) T147_134
      hfix147_134 hinj147_134 hcardT147_134
      (fun i => conj_mem_of_fixedPoints _ _ (T147_134 i) (hfix147_134 i) _)
      ⟨147, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 3 hp) Q2.T147_134_2 Q2.hfix147_134_2 Q2.hinj147_134_2
      Q2.hcardT147_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_134_2 i) (Q2.hfix147_134_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨134, by decide⟩ 3 (transLenTr ⟨134, by decide⟩ 3 hp) : ↥(reps ⟨134, by decide⟩)) : Coordinate 1)
        T147_134 = colFn colCertDiv_147_134_3.D1 (m := 1) from colCertDiv_147_134_3.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨134, by decide⟩ 3 hp : ↥(Q2.reps ⟨134, by decide⟩)) : Coordinate 2)
        Q2.T147_134_2 = colFn colCertDiv_147_134_3.D2 (m := 1) from colCertDiv_147_134_3.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_134_3_match


theorem leaf_147_134_4 (hp : 4 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 4 (transLenTr ⟨134, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 4 (transLenTr ⟨134, by decide⟩ 4 hp)) T147_134
      hfix147_134 hinj147_134 hcardT147_134
      (fun i => conj_mem_of_fixedPoints _ _ (T147_134 i) (hfix147_134 i) _)
      ⟨147, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 4 hp) Q2.T147_134_2 Q2.hfix147_134_2 Q2.hinj147_134_2
      Q2.hcardT147_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_134_2 i) (Q2.hfix147_134_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨134, by decide⟩ 4 (transLenTr ⟨134, by decide⟩ 4 hp) : ↥(reps ⟨134, by decide⟩)) : Coordinate 1)
        T147_134 = colFn colCertDiv_147_134_4.D1 (m := 1) from colCertDiv_147_134_4.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨134, by decide⟩ 4 hp : ↥(Q2.reps ⟨134, by decide⟩)) : Coordinate 2)
        Q2.T147_134_2 = colFn colCertDiv_147_134_4.D2 (m := 1) from colCertDiv_147_134_4.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_134_4_match


theorem leaf_147_134_5 (hp : 5 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 5 (transLenTr ⟨134, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 5 (transLenTr ⟨134, by decide⟩ 5 hp)) T147_134
      hfix147_134 hinj147_134 hcardT147_134
      (fun i => conj_mem_of_fixedPoints _ _ (T147_134 i) (hfix147_134 i) _)
      ⟨147, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 5 hp) Q2.T147_134_2 Q2.hfix147_134_2 Q2.hinj147_134_2
      Q2.hcardT147_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_134_2 i) (Q2.hfix147_134_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨134, by decide⟩ 5 (transLenTr ⟨134, by decide⟩ 5 hp) : ↥(reps ⟨134, by decide⟩)) : Coordinate 1)
        T147_134 = colFn colCertDiv_147_134_5.D1 (m := 1) from colCertDiv_147_134_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨134, by decide⟩ 5 hp : ↥(Q2.reps ⟨134, by decide⟩)) : Coordinate 2)
        Q2.T147_134_2 = colFn colCertDiv_147_134_5.D2 (m := 1) from colCertDiv_147_134_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_134_5_match


theorem leaf_147_134_6 (hp : 6 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 6 (transLenTr ⟨134, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 6 (transLenTr ⟨134, by decide⟩ 6 hp)) T147_134
      hfix147_134 hinj147_134 hcardT147_134
      (fun i => conj_mem_of_fixedPoints _ _ (T147_134 i) (hfix147_134 i) _)
      ⟨147, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 6 hp) Q2.T147_134_2 Q2.hfix147_134_2 Q2.hinj147_134_2
      Q2.hcardT147_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_134_2 i) (Q2.hfix147_134_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨134, by decide⟩ 6 (transLenTr ⟨134, by decide⟩ 6 hp) : ↥(reps ⟨134, by decide⟩)) : Coordinate 1)
        T147_134 = colFn colCertDiv_147_134_6.D1 (m := 1) from colCertDiv_147_134_6.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨134, by decide⟩ 6 hp : ↥(Q2.reps ⟨134, by decide⟩)) : Coordinate 2)
        Q2.T147_134_2 = colFn colCertDiv_147_134_6.D2 (m := 1) from colCertDiv_147_134_6.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_134_6_match


theorem leaf_147_134_7 (hp : 7 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 7 (transLenTr ⟨134, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 7 (transLenTr ⟨134, by decide⟩ 7 hp)) T147_134
      hfix147_134 hinj147_134 hcardT147_134
      (fun i => conj_mem_of_fixedPoints _ _ (T147_134 i) (hfix147_134 i) _)
      ⟨147, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 7 hp) Q2.T147_134_2 Q2.hfix147_134_2 Q2.hinj147_134_2
      Q2.hcardT147_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_134_2 i) (Q2.hfix147_134_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨134, by decide⟩ 7 (transLenTr ⟨134, by decide⟩ 7 hp) : ↥(reps ⟨134, by decide⟩)) : Coordinate 1)
        T147_134 = colFn colCertDiv_147_134_7.D1 (m := 1) from colCertDiv_147_134_7.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨134, by decide⟩ 7 hp : ↥(Q2.reps ⟨134, by decide⟩)) : Coordinate 2)
        Q2.T147_134_2 = colFn colCertDiv_147_134_7.D2 (m := 1) from colCertDiv_147_134_7.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_134_7_match


theorem leaf_147_134_8 (hp : 8 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 8 (transLenTr ⟨134, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 8 (transLenTr ⟨134, by decide⟩ 8 hp)) T147_134
      hfix147_134 hinj147_134 hcardT147_134
      (fun i => conj_mem_of_fixedPoints _ _ (T147_134 i) (hfix147_134 i) _)
      ⟨147, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 8 hp) Q2.T147_134_2 Q2.hfix147_134_2 Q2.hinj147_134_2
      Q2.hcardT147_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_134_2 i) (Q2.hfix147_134_2 i) _)
      colCert_147_134_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_134_9 (hp : 9 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 9 (transLenTr ⟨134, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 9 (transLenTr ⟨134, by decide⟩ 9 hp)) T147_134
      hfix147_134 hinj147_134 hcardT147_134
      (fun i => conj_mem_of_fixedPoints _ _ (T147_134 i) (hfix147_134 i) _)
      ⟨147, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 9 hp) Q2.T147_134_2 Q2.hfix147_134_2 Q2.hinj147_134_2
      Q2.hcardT147_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_134_2 i) (Q2.hfix147_134_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨134, by decide⟩ 9 (transLenTr ⟨134, by decide⟩ 9 hp) : ↥(reps ⟨134, by decide⟩)) : Coordinate 1)
        T147_134 = colFn colCertDiv_147_134_9.D1 (m := 1) from colCertDiv_147_134_9.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨134, by decide⟩ 9 hp : ↥(Q2.reps ⟨134, by decide⟩)) : Coordinate 2)
        Q2.T147_134_2 = colFn colCertDiv_147_134_9.D2 (m := 1) from colCertDiv_147_134_9.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_134_9_match


theorem leaf_147_134_10 (hp : 10 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 10 (transLenTr ⟨134, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 10 (transLenTr ⟨134, by decide⟩ 10 hp)) T147_134
      hfix147_134 hinj147_134 hcardT147_134
      (fun i => conj_mem_of_fixedPoints _ _ (T147_134 i) (hfix147_134 i) _)
      ⟨147, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 10 hp) Q2.T147_134_2 Q2.hfix147_134_2 Q2.hinj147_134_2
      Q2.hcardT147_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_134_2 i) (Q2.hfix147_134_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨134, by decide⟩ 10 (transLenTr ⟨134, by decide⟩ 10 hp) : ↥(reps ⟨134, by decide⟩)) : Coordinate 1)
        T147_134 = colFn colCertDiv_147_134_10.D1 (m := 1) from colCertDiv_147_134_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨134, by decide⟩ 10 hp : ↥(Q2.reps ⟨134, by decide⟩)) : Coordinate 2)
        Q2.T147_134_2 = colFn colCertDiv_147_134_10.D2 (m := 1) from colCertDiv_147_134_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_134_10_match


theorem leaf_147_134_11 (hp : 11 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 11 (transLenTr ⟨134, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 11 (transLenTr ⟨134, by decide⟩ 11 hp)) T147_134
      hfix147_134 hinj147_134 hcardT147_134
      (fun i => conj_mem_of_fixedPoints _ _ (T147_134 i) (hfix147_134 i) _)
      ⟨147, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 11 hp) Q2.T147_134_2 Q2.hfix147_134_2 Q2.hinj147_134_2
      Q2.hcardT147_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_134_2 i) (Q2.hfix147_134_2 i) _)
      colCert_147_134_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_134_12 (hp : 12 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 12 (transLenTr ⟨134, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 12 (transLenTr ⟨134, by decide⟩ 12 hp)) T147_134
      hfix147_134 hinj147_134 hcardT147_134
      (fun i => conj_mem_of_fixedPoints _ _ (T147_134 i) (hfix147_134 i) _)
      ⟨147, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 12 hp) Q2.T147_134_2 Q2.hfix147_134_2 Q2.hinj147_134_2
      Q2.hcardT147_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_134_2 i) (Q2.hfix147_134_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨134, by decide⟩ 12 (transLenTr ⟨134, by decide⟩ 12 hp) : ↥(reps ⟨134, by decide⟩)) : Coordinate 1)
        T147_134 = colFn colCertDiv_147_134_12.D1 (m := 1) from colCertDiv_147_134_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨134, by decide⟩ 12 hp : ↥(Q2.reps ⟨134, by decide⟩)) : Coordinate 2)
        Q2.T147_134_2 = colFn colCertDiv_147_134_12.D2 (m := 1) from colCertDiv_147_134_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_134_12_match


theorem leaf_147_134_13 (hp : 13 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 13 (transLenTr ⟨134, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 13 (transLenTr ⟨134, by decide⟩ 13 hp)) T147_134
      hfix147_134 hinj147_134 hcardT147_134
      (fun i => conj_mem_of_fixedPoints _ _ (T147_134 i) (hfix147_134 i) _)
      ⟨147, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 13 hp) Q2.T147_134_2 Q2.hfix147_134_2 Q2.hinj147_134_2
      Q2.hcardT147_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_134_2 i) (Q2.hfix147_134_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨134, by decide⟩ 13 (transLenTr ⟨134, by decide⟩ 13 hp) : ↥(reps ⟨134, by decide⟩)) : Coordinate 1)
        T147_134 = colFn colCertDiv_147_134_13.D1 (m := 1) from colCertDiv_147_134_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨134, by decide⟩ 13 hp : ↥(Q2.reps ⟨134, by decide⟩)) : Coordinate 2)
        Q2.T147_134_2 = colFn colCertDiv_147_134_13.D2 (m := 1) from colCertDiv_147_134_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_134_13_match


theorem leaf_147_134_14 (hp : 14 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 14 (transLenTr ⟨134, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 14 (transLenTr ⟨134, by decide⟩ 14 hp)) T147_134
      hfix147_134 hinj147_134 hcardT147_134
      (fun i => conj_mem_of_fixedPoints _ _ (T147_134 i) (hfix147_134 i) _)
      ⟨147, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 14 hp) Q2.T147_134_2 Q2.hfix147_134_2 Q2.hinj147_134_2
      Q2.hcardT147_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_134_2 i) (Q2.hfix147_134_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨134, by decide⟩ 14 (transLenTr ⟨134, by decide⟩ 14 hp) : ↥(reps ⟨134, by decide⟩)) : Coordinate 1)
        T147_134 = colFn colCertDiv_147_134_14.D1 (m := 1) from colCertDiv_147_134_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨134, by decide⟩ 14 hp : ↥(Q2.reps ⟨134, by decide⟩)) : Coordinate 2)
        Q2.T147_134_2 = colFn colCertDiv_147_134_14.D2 (m := 1) from colCertDiv_147_134_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_134_14_match


theorem leaf_147_134_15 (hp : 15 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 15 (transLenTr ⟨134, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 15 (transLenTr ⟨134, by decide⟩ 15 hp)) T147_134
      hfix147_134 hinj147_134 hcardT147_134
      (fun i => conj_mem_of_fixedPoints _ _ (T147_134 i) (hfix147_134 i) _)
      ⟨147, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 15 hp) Q2.T147_134_2 Q2.hfix147_134_2 Q2.hinj147_134_2
      Q2.hcardT147_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_134_2 i) (Q2.hfix147_134_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨134, by decide⟩ 15 (transLenTr ⟨134, by decide⟩ 15 hp) : ↥(reps ⟨134, by decide⟩)) : Coordinate 1)
        T147_134 = colFn colCertDiv_147_134_15.D1 (m := 1) from colCertDiv_147_134_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨134, by decide⟩ 15 hp : ↥(Q2.reps ⟨134, by decide⟩)) : Coordinate 2)
        Q2.T147_134_2 = colFn colCertDiv_147_134_15.D2 (m := 1) from colCertDiv_147_134_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_134_15_match


theorem leaf_147_134_16 (hp : 16 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 16 (transLenTr ⟨134, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 16 (transLenTr ⟨134, by decide⟩ 16 hp)) T147_134
      hfix147_134 hinj147_134 hcardT147_134
      (fun i => conj_mem_of_fixedPoints _ _ (T147_134 i) (hfix147_134 i) _)
      ⟨147, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 16 hp) Q2.T147_134_2 Q2.hfix147_134_2 Q2.hinj147_134_2
      Q2.hcardT147_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_134_2 i) (Q2.hfix147_134_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨134, by decide⟩ 16 (transLenTr ⟨134, by decide⟩ 16 hp) : ↥(reps ⟨134, by decide⟩)) : Coordinate 1)
        T147_134 = colFn colCertDiv_147_134_16.D1 (m := 1) from colCertDiv_147_134_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨134, by decide⟩ 16 hp : ↥(Q2.reps ⟨134, by decide⟩)) : Coordinate 2)
        Q2.T147_134_2 = colFn colCertDiv_147_134_16.D2 (m := 1) from colCertDiv_147_134_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_134_16_match


end LeanDring.P5Presentation
