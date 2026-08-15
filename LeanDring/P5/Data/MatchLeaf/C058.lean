/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C035
import LeanDring.P5.Data.ColCdd.C036
import LeanDring.P5.Data.ColCdd.C037
import LeanDring.P5.Data.ColRestCheap.C133
import LeanDring.P5.Data.ColRestCheap.C134
import LeanDring.P5.Data.ColRestCheap.C135
import LeanDring.P5.Data.EntryK.C044
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C042
import LeanDring.P5.Data.SpeciesDiv.C043

/-! # Stage-5 leaves, chunk 57 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_147_134_17 (hp : 17 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 17 (transLenTr ⟨134, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 17 (transLenTr ⟨134, by decide⟩ 17 hp)) T147_134
      hfix147_134 hinj147_134 hcardT147_134
      (fun i => conj_mem_of_fixedPoints _ _ (T147_134 i) (hfix147_134 i) _)
      ⟨147, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 17 hp) Q2.T147_134_2 Q2.hfix147_134_2 Q2.hinj147_134_2
      Q2.hcardT147_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_134_2 i) (Q2.hfix147_134_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨134, by decide⟩ 17 (transLenTr ⟨134, by decide⟩ 17 hp) : ↥(reps ⟨134, by decide⟩)) : Coordinate 1)
        T147_134 = colFn colCertDiv_147_134_17.D1 (m := 1) from colCertDiv_147_134_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨134, by decide⟩ 17 hp : ↥(Q2.reps ⟨134, by decide⟩)) : Coordinate 2)
        Q2.T147_134_2 = colFn colCertDiv_147_134_17.D2 (m := 1) from colCertDiv_147_134_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_134_17_match


theorem leaf_147_134_18 (hp : 18 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 18 (transLenTr ⟨134, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 18 (transLenTr ⟨134, by decide⟩ 18 hp)) T147_134
      hfix147_134 hinj147_134 hcardT147_134
      (fun i => conj_mem_of_fixedPoints _ _ (T147_134 i) (hfix147_134 i) _)
      ⟨147, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 18 hp) Q2.T147_134_2 Q2.hfix147_134_2 Q2.hinj147_134_2
      Q2.hcardT147_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_134_2 i) (Q2.hfix147_134_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨134, by decide⟩ 18 (transLenTr ⟨134, by decide⟩ 18 hp) : ↥(reps ⟨134, by decide⟩)) : Coordinate 1)
        T147_134 = colFn colCertDiv_147_134_18.D1 (m := 1) from colCertDiv_147_134_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨134, by decide⟩ 18 hp : ↥(Q2.reps ⟨134, by decide⟩)) : Coordinate 2)
        Q2.T147_134_2 = colFn colCertDiv_147_134_18.D2 (m := 1) from colCertDiv_147_134_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_134_18_match


theorem leaf_147_134_19 (hp : 19 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 19 (transLenTr ⟨134, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 19 (transLenTr ⟨134, by decide⟩ 19 hp)) T147_134
      hfix147_134 hinj147_134 hcardT147_134
      (fun i => conj_mem_of_fixedPoints _ _ (T147_134 i) (hfix147_134 i) _)
      ⟨147, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 19 hp) Q2.T147_134_2 Q2.hfix147_134_2 Q2.hinj147_134_2
      Q2.hcardT147_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_134_2 i) (Q2.hfix147_134_2 i) _)
      colCert_147_134_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_134_20 (hp : 20 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 20 (transLenTr ⟨134, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 20 (transLenTr ⟨134, by decide⟩ 20 hp)) T147_134
      hfix147_134 hinj147_134 hcardT147_134
      (fun i => conj_mem_of_fixedPoints _ _ (T147_134 i) (hfix147_134 i) _)
      ⟨147, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 20 hp) Q2.T147_134_2 Q2.hfix147_134_2 Q2.hinj147_134_2
      Q2.hcardT147_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_134_2 i) (Q2.hfix147_134_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨134, by decide⟩ 20 (transLenTr ⟨134, by decide⟩ 20 hp) : ↥(reps ⟨134, by decide⟩)) : Coordinate 1)
        T147_134 = colFn colCertDiv_147_134_20.D1 (m := 1) from colCertDiv_147_134_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨134, by decide⟩ 20 hp : ↥(Q2.reps ⟨134, by decide⟩)) : Coordinate 2)
        Q2.T147_134_2 = colFn colCertDiv_147_134_20.D2 (m := 1) from colCertDiv_147_134_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_134_20_match


theorem leaf_147_134_21 (hp : 21 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 21 (transLenTr ⟨134, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 21 (transLenTr ⟨134, by decide⟩ 21 hp)) T147_134
      hfix147_134 hinj147_134 hcardT147_134
      (fun i => conj_mem_of_fixedPoints _ _ (T147_134 i) (hfix147_134 i) _)
      ⟨147, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 21 hp) Q2.T147_134_2 Q2.hfix147_134_2 Q2.hinj147_134_2
      Q2.hcardT147_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_134_2 i) (Q2.hfix147_134_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨134, by decide⟩ 21 (transLenTr ⟨134, by decide⟩ 21 hp) : ↥(reps ⟨134, by decide⟩)) : Coordinate 1)
        T147_134 = colFn colCertDiv_147_134_21.D1 (m := 1) from colCertDiv_147_134_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨134, by decide⟩ 21 hp : ↥(Q2.reps ⟨134, by decide⟩)) : Coordinate 2)
        Q2.T147_134_2 = colFn colCertDiv_147_134_21.D2 (m := 1) from colCertDiv_147_134_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_134_21_match


theorem leaf_147_134_22 (hp : 22 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 22 (transLenTr ⟨134, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 22 (transLenTr ⟨134, by decide⟩ 22 hp)) T147_134
      hfix147_134 hinj147_134 hcardT147_134
      (fun i => conj_mem_of_fixedPoints _ _ (T147_134 i) (hfix147_134 i) _)
      ⟨147, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 22 hp) Q2.T147_134_2 Q2.hfix147_134_2 Q2.hinj147_134_2
      Q2.hcardT147_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_134_2 i) (Q2.hfix147_134_2 i) _)
      colCert_147_134_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_134_23 (hp : 23 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 23 (transLenTr ⟨134, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 23 (transLenTr ⟨134, by decide⟩ 23 hp)) T147_134
      hfix147_134 hinj147_134 hcardT147_134
      (fun i => conj_mem_of_fixedPoints _ _ (T147_134 i) (hfix147_134 i) _)
      ⟨147, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 23 hp) Q2.T147_134_2 Q2.hfix147_134_2 Q2.hinj147_134_2
      Q2.hcardT147_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_134_2 i) (Q2.hfix147_134_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨134, by decide⟩ 23 (transLenTr ⟨134, by decide⟩ 23 hp) : ↥(reps ⟨134, by decide⟩)) : Coordinate 1)
        T147_134 = colFn colCertDiv_147_134_23.D1 (m := 1) from colCertDiv_147_134_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨134, by decide⟩ 23 hp : ↥(Q2.reps ⟨134, by decide⟩)) : Coordinate 2)
        Q2.T147_134_2 = colFn colCertDiv_147_134_23.D2 (m := 1) from colCertDiv_147_134_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_134_23_match


theorem leaf_147_134_24 (hp : 24 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 24 (transLenTr ⟨134, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 24 (transLenTr ⟨134, by decide⟩ 24 hp)) T147_134
      hfix147_134 hinj147_134 hcardT147_134
      (fun i => conj_mem_of_fixedPoints _ _ (T147_134 i) (hfix147_134 i) _)
      ⟨147, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 24 hp) Q2.T147_134_2 Q2.hfix147_134_2 Q2.hinj147_134_2
      Q2.hcardT147_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_134_2 i) (Q2.hfix147_134_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨134, by decide⟩ 24 (transLenTr ⟨134, by decide⟩ 24 hp) : ↥(reps ⟨134, by decide⟩)) : Coordinate 1)
        T147_134 = colFn colCertDiv_147_134_24.D1 (m := 1) from colCertDiv_147_134_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨134, by decide⟩ 24 hp : ↥(Q2.reps ⟨134, by decide⟩)) : Coordinate 2)
        Q2.T147_134_2 = colFn colCertDiv_147_134_24.D2 (m := 1) from colCertDiv_147_134_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_134_24_match


theorem leaf_147_135_0 (hp : 0 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 0 (transLenTr ⟨135, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 0 (transLenTr ⟨135, by decide⟩ 0 hp)) T147_135
      hfix147_135 hinj147_135 hcardT147_135
      (fun i => conj_mem_of_fixedPoints _ _ (T147_135 i) (hfix147_135 i) _)
      ⟨147, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 0 hp) Q2.T147_135_2 Q2.hfix147_135_2 Q2.hinj147_135_2
      Q2.hcardT147_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_135_2 i) (Q2.hfix147_135_2 i) _)
      colCert_147_135_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_135_1 (hp : 1 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 1 (transLenTr ⟨135, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 1 (transLenTr ⟨135, by decide⟩ 1 hp)) T147_135
      hfix147_135 hinj147_135 hcardT147_135
      (fun i => conj_mem_of_fixedPoints _ _ (T147_135 i) (hfix147_135 i) _)
      ⟨147, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 1 hp) Q2.T147_135_2 Q2.hfix147_135_2 Q2.hinj147_135_2
      Q2.hcardT147_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_135_2 i) (Q2.hfix147_135_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨135, by decide⟩ 1 (transLenTr ⟨135, by decide⟩ 1 hp) : ↥(reps ⟨135, by decide⟩)) : Coordinate 1)
        T147_135 = colFn colCertDiv_147_135_1.D1 (m := 1) from colCertDiv_147_135_1.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨135, by decide⟩ 1 hp : ↥(Q2.reps ⟨135, by decide⟩)) : Coordinate 2)
        Q2.T147_135_2 = colFn colCertDiv_147_135_1.D2 (m := 1) from colCertDiv_147_135_1.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_135_1_match


theorem leaf_147_135_2 (hp : 2 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 2 (transLenTr ⟨135, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 2 (transLenTr ⟨135, by decide⟩ 2 hp)) T147_135
      hfix147_135 hinj147_135 hcardT147_135
      (fun i => conj_mem_of_fixedPoints _ _ (T147_135 i) (hfix147_135 i) _)
      ⟨147, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 2 hp) Q2.T147_135_2 Q2.hfix147_135_2 Q2.hinj147_135_2
      Q2.hcardT147_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_135_2 i) (Q2.hfix147_135_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨135, by decide⟩ 2 (transLenTr ⟨135, by decide⟩ 2 hp) : ↥(reps ⟨135, by decide⟩)) : Coordinate 1)
        T147_135 = colFn colCertDiv_147_135_2.D1 (m := 1) from colCertDiv_147_135_2.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨135, by decide⟩ 2 hp : ↥(Q2.reps ⟨135, by decide⟩)) : Coordinate 2)
        Q2.T147_135_2 = colFn colCertDiv_147_135_2.D2 (m := 1) from colCertDiv_147_135_2.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_135_2_match


theorem leaf_147_135_3 (hp : 3 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 3 (transLenTr ⟨135, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 3 (transLenTr ⟨135, by decide⟩ 3 hp)) T147_135
      hfix147_135 hinj147_135 hcardT147_135
      (fun i => conj_mem_of_fixedPoints _ _ (T147_135 i) (hfix147_135 i) _)
      ⟨147, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 3 hp) Q2.T147_135_2 Q2.hfix147_135_2 Q2.hinj147_135_2
      Q2.hcardT147_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_135_2 i) (Q2.hfix147_135_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨135, by decide⟩ 3 (transLenTr ⟨135, by decide⟩ 3 hp) : ↥(reps ⟨135, by decide⟩)) : Coordinate 1)
        T147_135 = colFn colCertDiv_147_135_3.D1 (m := 1) from colCertDiv_147_135_3.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨135, by decide⟩ 3 hp : ↥(Q2.reps ⟨135, by decide⟩)) : Coordinate 2)
        Q2.T147_135_2 = colFn colCertDiv_147_135_3.D2 (m := 1) from colCertDiv_147_135_3.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_135_3_match


theorem leaf_147_135_4 (hp : 4 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 4 (transLenTr ⟨135, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 4 (transLenTr ⟨135, by decide⟩ 4 hp)) T147_135
      hfix147_135 hinj147_135 hcardT147_135
      (fun i => conj_mem_of_fixedPoints _ _ (T147_135 i) (hfix147_135 i) _)
      ⟨147, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 4 hp) Q2.T147_135_2 Q2.hfix147_135_2 Q2.hinj147_135_2
      Q2.hcardT147_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_135_2 i) (Q2.hfix147_135_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨135, by decide⟩ 4 (transLenTr ⟨135, by decide⟩ 4 hp) : ↥(reps ⟨135, by decide⟩)) : Coordinate 1)
        T147_135 = colFn colCertDiv_147_135_4.D1 (m := 1) from colCertDiv_147_135_4.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨135, by decide⟩ 4 hp : ↥(Q2.reps ⟨135, by decide⟩)) : Coordinate 2)
        Q2.T147_135_2 = colFn colCertDiv_147_135_4.D2 (m := 1) from colCertDiv_147_135_4.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_135_4_match


theorem leaf_147_135_5 (hp : 5 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 5 (transLenTr ⟨135, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 5 (transLenTr ⟨135, by decide⟩ 5 hp)) T147_135
      hfix147_135 hinj147_135 hcardT147_135
      (fun i => conj_mem_of_fixedPoints _ _ (T147_135 i) (hfix147_135 i) _)
      ⟨147, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 5 hp) Q2.T147_135_2 Q2.hfix147_135_2 Q2.hinj147_135_2
      Q2.hcardT147_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_135_2 i) (Q2.hfix147_135_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨135, by decide⟩ 5 (transLenTr ⟨135, by decide⟩ 5 hp) : ↥(reps ⟨135, by decide⟩)) : Coordinate 1)
        T147_135 = colFn colCertDiv_147_135_5.D1 (m := 1) from colCertDiv_147_135_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨135, by decide⟩ 5 hp : ↥(Q2.reps ⟨135, by decide⟩)) : Coordinate 2)
        Q2.T147_135_2 = colFn colCertDiv_147_135_5.D2 (m := 1) from colCertDiv_147_135_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_135_5_match


theorem leaf_147_135_6 (hp : 6 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 6 (transLenTr ⟨135, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 6 (transLenTr ⟨135, by decide⟩ 6 hp)) T147_135
      hfix147_135 hinj147_135 hcardT147_135
      (fun i => conj_mem_of_fixedPoints _ _ (T147_135 i) (hfix147_135 i) _)
      ⟨147, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 6 hp) Q2.T147_135_2 Q2.hfix147_135_2 Q2.hinj147_135_2
      Q2.hcardT147_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_135_2 i) (Q2.hfix147_135_2 i) _)
      colCert_147_135_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_135_7 (hp : 7 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 7 (transLenTr ⟨135, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 7 (transLenTr ⟨135, by decide⟩ 7 hp)) T147_135
      hfix147_135 hinj147_135 hcardT147_135
      (fun i => conj_mem_of_fixedPoints _ _ (T147_135 i) (hfix147_135 i) _)
      ⟨147, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 7 hp) Q2.T147_135_2 Q2.hfix147_135_2 Q2.hinj147_135_2
      Q2.hcardT147_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_135_2 i) (Q2.hfix147_135_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨135, by decide⟩ 7 (transLenTr ⟨135, by decide⟩ 7 hp) : ↥(reps ⟨135, by decide⟩)) : Coordinate 1)
        T147_135 = colFn colCertDiv_147_135_7.D1 (m := 1) from colCertDiv_147_135_7.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨135, by decide⟩ 7 hp : ↥(Q2.reps ⟨135, by decide⟩)) : Coordinate 2)
        Q2.T147_135_2 = colFn colCertDiv_147_135_7.D2 (m := 1) from colCertDiv_147_135_7.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_135_7_match


theorem leaf_147_135_8 (hp : 8 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 8 (transLenTr ⟨135, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 8 (transLenTr ⟨135, by decide⟩ 8 hp)) T147_135
      hfix147_135 hinj147_135 hcardT147_135
      (fun i => conj_mem_of_fixedPoints _ _ (T147_135 i) (hfix147_135 i) _)
      ⟨147, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 8 hp) Q2.T147_135_2 Q2.hfix147_135_2 Q2.hinj147_135_2
      Q2.hcardT147_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_135_2 i) (Q2.hfix147_135_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨135, by decide⟩ 8 (transLenTr ⟨135, by decide⟩ 8 hp) : ↥(reps ⟨135, by decide⟩)) : Coordinate 1)
        T147_135 = colFn colCertDiv_147_135_8.D1 (m := 1) from colCertDiv_147_135_8.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨135, by decide⟩ 8 hp : ↥(Q2.reps ⟨135, by decide⟩)) : Coordinate 2)
        Q2.T147_135_2 = colFn colCertDiv_147_135_8.D2 (m := 1) from colCertDiv_147_135_8.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_135_8_match


theorem leaf_147_135_9 (hp : 9 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 9 (transLenTr ⟨135, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 9 (transLenTr ⟨135, by decide⟩ 9 hp)) T147_135
      hfix147_135 hinj147_135 hcardT147_135
      (fun i => conj_mem_of_fixedPoints _ _ (T147_135 i) (hfix147_135 i) _)
      ⟨147, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 9 hp) Q2.T147_135_2 Q2.hfix147_135_2 Q2.hinj147_135_2
      Q2.hcardT147_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_135_2 i) (Q2.hfix147_135_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨135, by decide⟩ 9 (transLenTr ⟨135, by decide⟩ 9 hp) : ↥(reps ⟨135, by decide⟩)) : Coordinate 1)
        T147_135 = colFn colCertDiv_147_135_9.D1 (m := 1) from colCertDiv_147_135_9.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨135, by decide⟩ 9 hp : ↥(Q2.reps ⟨135, by decide⟩)) : Coordinate 2)
        Q2.T147_135_2 = colFn colCertDiv_147_135_9.D2 (m := 1) from colCertDiv_147_135_9.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_135_9_match


theorem leaf_147_135_10 (hp : 10 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 10 (transLenTr ⟨135, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 10 (transLenTr ⟨135, by decide⟩ 10 hp)) T147_135
      hfix147_135 hinj147_135 hcardT147_135
      (fun i => conj_mem_of_fixedPoints _ _ (T147_135 i) (hfix147_135 i) _)
      ⟨147, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 10 hp) Q2.T147_135_2 Q2.hfix147_135_2 Q2.hinj147_135_2
      Q2.hcardT147_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_135_2 i) (Q2.hfix147_135_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨135, by decide⟩ 10 (transLenTr ⟨135, by decide⟩ 10 hp) : ↥(reps ⟨135, by decide⟩)) : Coordinate 1)
        T147_135 = colFn colCertDiv_147_135_10.D1 (m := 1) from colCertDiv_147_135_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨135, by decide⟩ 10 hp : ↥(Q2.reps ⟨135, by decide⟩)) : Coordinate 2)
        Q2.T147_135_2 = colFn colCertDiv_147_135_10.D2 (m := 1) from colCertDiv_147_135_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_135_10_match


theorem leaf_147_135_11 (hp : 11 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 11 (transLenTr ⟨135, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 11 (transLenTr ⟨135, by decide⟩ 11 hp)) T147_135
      hfix147_135 hinj147_135 hcardT147_135
      (fun i => conj_mem_of_fixedPoints _ _ (T147_135 i) (hfix147_135 i) _)
      ⟨147, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 11 hp) Q2.T147_135_2 Q2.hfix147_135_2 Q2.hinj147_135_2
      Q2.hcardT147_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_135_2 i) (Q2.hfix147_135_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨135, by decide⟩ 11 (transLenTr ⟨135, by decide⟩ 11 hp) : ↥(reps ⟨135, by decide⟩)) : Coordinate 1)
        T147_135 = colFn colCertDiv_147_135_11.D1 (m := 1) from colCertDiv_147_135_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨135, by decide⟩ 11 hp : ↥(Q2.reps ⟨135, by decide⟩)) : Coordinate 2)
        Q2.T147_135_2 = colFn colCertDiv_147_135_11.D2 (m := 1) from colCertDiv_147_135_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_135_11_match


theorem leaf_147_135_12 (hp : 12 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 12 (transLenTr ⟨135, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 12 (transLenTr ⟨135, by decide⟩ 12 hp)) T147_135
      hfix147_135 hinj147_135 hcardT147_135
      (fun i => conj_mem_of_fixedPoints _ _ (T147_135 i) (hfix147_135 i) _)
      ⟨147, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 12 hp) Q2.T147_135_2 Q2.hfix147_135_2 Q2.hinj147_135_2
      Q2.hcardT147_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_135_2 i) (Q2.hfix147_135_2 i) _)
      colCert_147_135_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_135_13 (hp : 13 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 13 (transLenTr ⟨135, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 13 (transLenTr ⟨135, by decide⟩ 13 hp)) T147_135
      hfix147_135 hinj147_135 hcardT147_135
      (fun i => conj_mem_of_fixedPoints _ _ (T147_135 i) (hfix147_135 i) _)
      ⟨147, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 13 hp) Q2.T147_135_2 Q2.hfix147_135_2 Q2.hinj147_135_2
      Q2.hcardT147_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_135_2 i) (Q2.hfix147_135_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨135, by decide⟩ 13 (transLenTr ⟨135, by decide⟩ 13 hp) : ↥(reps ⟨135, by decide⟩)) : Coordinate 1)
        T147_135 = colFn colCertDiv_147_135_13.D1 (m := 1) from colCertDiv_147_135_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨135, by decide⟩ 13 hp : ↥(Q2.reps ⟨135, by decide⟩)) : Coordinate 2)
        Q2.T147_135_2 = colFn colCertDiv_147_135_13.D2 (m := 1) from colCertDiv_147_135_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_135_13_match


theorem leaf_147_135_14 (hp : 14 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 14 (transLenTr ⟨135, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 14 (transLenTr ⟨135, by decide⟩ 14 hp)) T147_135
      hfix147_135 hinj147_135 hcardT147_135
      (fun i => conj_mem_of_fixedPoints _ _ (T147_135 i) (hfix147_135 i) _)
      ⟨147, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 14 hp) Q2.T147_135_2 Q2.hfix147_135_2 Q2.hinj147_135_2
      Q2.hcardT147_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_135_2 i) (Q2.hfix147_135_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨135, by decide⟩ 14 (transLenTr ⟨135, by decide⟩ 14 hp) : ↥(reps ⟨135, by decide⟩)) : Coordinate 1)
        T147_135 = colFn colCertDiv_147_135_14.D1 (m := 1) from colCertDiv_147_135_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨135, by decide⟩ 14 hp : ↥(Q2.reps ⟨135, by decide⟩)) : Coordinate 2)
        Q2.T147_135_2 = colFn colCertDiv_147_135_14.D2 (m := 1) from colCertDiv_147_135_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_135_14_match


theorem leaf_147_135_15 (hp : 15 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 15 (transLenTr ⟨135, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 15 (transLenTr ⟨135, by decide⟩ 15 hp)) T147_135
      hfix147_135 hinj147_135 hcardT147_135
      (fun i => conj_mem_of_fixedPoints _ _ (T147_135 i) (hfix147_135 i) _)
      ⟨147, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 15 hp) Q2.T147_135_2 Q2.hfix147_135_2 Q2.hinj147_135_2
      Q2.hcardT147_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_135_2 i) (Q2.hfix147_135_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨135, by decide⟩ 15 (transLenTr ⟨135, by decide⟩ 15 hp) : ↥(reps ⟨135, by decide⟩)) : Coordinate 1)
        T147_135 = colFn colCertDiv_147_135_15.D1 (m := 1) from colCertDiv_147_135_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨135, by decide⟩ 15 hp : ↥(Q2.reps ⟨135, by decide⟩)) : Coordinate 2)
        Q2.T147_135_2 = colFn colCertDiv_147_135_15.D2 (m := 1) from colCertDiv_147_135_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_135_15_match


theorem leaf_147_135_16 (hp : 16 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 16 (transLenTr ⟨135, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 16 (transLenTr ⟨135, by decide⟩ 16 hp)) T147_135
      hfix147_135 hinj147_135 hcardT147_135
      (fun i => conj_mem_of_fixedPoints _ _ (T147_135 i) (hfix147_135 i) _)
      ⟨147, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 16 hp) Q2.T147_135_2 Q2.hfix147_135_2 Q2.hinj147_135_2
      Q2.hcardT147_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_135_2 i) (Q2.hfix147_135_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨135, by decide⟩ 16 (transLenTr ⟨135, by decide⟩ 16 hp) : ↥(reps ⟨135, by decide⟩)) : Coordinate 1)
        T147_135 = colFn colCertDiv_147_135_16.D1 (m := 1) from colCertDiv_147_135_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨135, by decide⟩ 16 hp : ↥(Q2.reps ⟨135, by decide⟩)) : Coordinate 2)
        Q2.T147_135_2 = colFn colCertDiv_147_135_16.D2 (m := 1) from colCertDiv_147_135_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_135_16_match


theorem leaf_147_135_17 (hp : 17 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 17 (transLenTr ⟨135, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 17 (transLenTr ⟨135, by decide⟩ 17 hp)) T147_135
      hfix147_135 hinj147_135 hcardT147_135
      (fun i => conj_mem_of_fixedPoints _ _ (T147_135 i) (hfix147_135 i) _)
      ⟨147, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 17 hp) Q2.T147_135_2 Q2.hfix147_135_2 Q2.hinj147_135_2
      Q2.hcardT147_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_135_2 i) (Q2.hfix147_135_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨135, by decide⟩ 17 (transLenTr ⟨135, by decide⟩ 17 hp) : ↥(reps ⟨135, by decide⟩)) : Coordinate 1)
        T147_135 = colFn colCertDiv_147_135_17.D1 (m := 1) from colCertDiv_147_135_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨135, by decide⟩ 17 hp : ↥(Q2.reps ⟨135, by decide⟩)) : Coordinate 2)
        Q2.T147_135_2 = colFn colCertDiv_147_135_17.D2 (m := 1) from colCertDiv_147_135_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_135_17_match


theorem leaf_147_135_18 (hp : 18 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 18 (transLenTr ⟨135, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 18 (transLenTr ⟨135, by decide⟩ 18 hp)) T147_135
      hfix147_135 hinj147_135 hcardT147_135
      (fun i => conj_mem_of_fixedPoints _ _ (T147_135 i) (hfix147_135 i) _)
      ⟨147, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 18 hp) Q2.T147_135_2 Q2.hfix147_135_2 Q2.hinj147_135_2
      Q2.hcardT147_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_135_2 i) (Q2.hfix147_135_2 i) _)
      colCert_147_135_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_135_19 (hp : 19 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 19 (transLenTr ⟨135, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 19 (transLenTr ⟨135, by decide⟩ 19 hp)) T147_135
      hfix147_135 hinj147_135 hcardT147_135
      (fun i => conj_mem_of_fixedPoints _ _ (T147_135 i) (hfix147_135 i) _)
      ⟨147, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 19 hp) Q2.T147_135_2 Q2.hfix147_135_2 Q2.hinj147_135_2
      Q2.hcardT147_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_135_2 i) (Q2.hfix147_135_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨135, by decide⟩ 19 (transLenTr ⟨135, by decide⟩ 19 hp) : ↥(reps ⟨135, by decide⟩)) : Coordinate 1)
        T147_135 = colFn colCertDiv_147_135_19.D1 (m := 1) from colCertDiv_147_135_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨135, by decide⟩ 19 hp : ↥(Q2.reps ⟨135, by decide⟩)) : Coordinate 2)
        Q2.T147_135_2 = colFn colCertDiv_147_135_19.D2 (m := 1) from colCertDiv_147_135_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_135_19_match


theorem leaf_147_135_20 (hp : 20 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 20 (transLenTr ⟨135, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 20 (transLenTr ⟨135, by decide⟩ 20 hp)) T147_135
      hfix147_135 hinj147_135 hcardT147_135
      (fun i => conj_mem_of_fixedPoints _ _ (T147_135 i) (hfix147_135 i) _)
      ⟨147, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 20 hp) Q2.T147_135_2 Q2.hfix147_135_2 Q2.hinj147_135_2
      Q2.hcardT147_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_135_2 i) (Q2.hfix147_135_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨135, by decide⟩ 20 (transLenTr ⟨135, by decide⟩ 20 hp) : ↥(reps ⟨135, by decide⟩)) : Coordinate 1)
        T147_135 = colFn colCertDiv_147_135_20.D1 (m := 1) from colCertDiv_147_135_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨135, by decide⟩ 20 hp : ↥(Q2.reps ⟨135, by decide⟩)) : Coordinate 2)
        Q2.T147_135_2 = colFn colCertDiv_147_135_20.D2 (m := 1) from colCertDiv_147_135_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_135_20_match


theorem leaf_147_135_21 (hp : 21 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 21 (transLenTr ⟨135, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 21 (transLenTr ⟨135, by decide⟩ 21 hp)) T147_135
      hfix147_135 hinj147_135 hcardT147_135
      (fun i => conj_mem_of_fixedPoints _ _ (T147_135 i) (hfix147_135 i) _)
      ⟨147, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 21 hp) Q2.T147_135_2 Q2.hfix147_135_2 Q2.hinj147_135_2
      Q2.hcardT147_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_135_2 i) (Q2.hfix147_135_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨135, by decide⟩ 21 (transLenTr ⟨135, by decide⟩ 21 hp) : ↥(reps ⟨135, by decide⟩)) : Coordinate 1)
        T147_135 = colFn colCertDiv_147_135_21.D1 (m := 1) from colCertDiv_147_135_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨135, by decide⟩ 21 hp : ↥(Q2.reps ⟨135, by decide⟩)) : Coordinate 2)
        Q2.T147_135_2 = colFn colCertDiv_147_135_21.D2 (m := 1) from colCertDiv_147_135_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_135_21_match


theorem leaf_147_135_22 (hp : 22 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 22 (transLenTr ⟨135, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 22 (transLenTr ⟨135, by decide⟩ 22 hp)) T147_135
      hfix147_135 hinj147_135 hcardT147_135
      (fun i => conj_mem_of_fixedPoints _ _ (T147_135 i) (hfix147_135 i) _)
      ⟨147, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 22 hp) Q2.T147_135_2 Q2.hfix147_135_2 Q2.hinj147_135_2
      Q2.hcardT147_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_135_2 i) (Q2.hfix147_135_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨135, by decide⟩ 22 (transLenTr ⟨135, by decide⟩ 22 hp) : ↥(reps ⟨135, by decide⟩)) : Coordinate 1)
        T147_135 = colFn colCertDiv_147_135_22.D1 (m := 1) from colCertDiv_147_135_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨135, by decide⟩ 22 hp : ↥(Q2.reps ⟨135, by decide⟩)) : Coordinate 2)
        Q2.T147_135_2 = colFn colCertDiv_147_135_22.D2 (m := 1) from colCertDiv_147_135_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_135_22_match


theorem leaf_147_135_23 (hp : 23 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 23 (transLenTr ⟨135, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 23 (transLenTr ⟨135, by decide⟩ 23 hp)) T147_135
      hfix147_135 hinj147_135 hcardT147_135
      (fun i => conj_mem_of_fixedPoints _ _ (T147_135 i) (hfix147_135 i) _)
      ⟨147, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 23 hp) Q2.T147_135_2 Q2.hfix147_135_2 Q2.hinj147_135_2
      Q2.hcardT147_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_135_2 i) (Q2.hfix147_135_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨135, by decide⟩ 23 (transLenTr ⟨135, by decide⟩ 23 hp) : ↥(reps ⟨135, by decide⟩)) : Coordinate 1)
        T147_135 = colFn colCertDiv_147_135_23.D1 (m := 1) from colCertDiv_147_135_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨135, by decide⟩ 23 hp : ↥(Q2.reps ⟨135, by decide⟩)) : Coordinate 2)
        Q2.T147_135_2 = colFn colCertDiv_147_135_23.D2 (m := 1) from colCertDiv_147_135_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_135_23_match


theorem leaf_147_135_24 (hp : 24 < (Q2.transData.getD 135 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ 24 (transLenTr ⟨135, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨135, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨135, by decide⟩ 24 (transLenTr ⟨135, by decide⟩ 24 hp)) T147_135
      hfix147_135 hinj147_135 hcardT147_135
      (fun i => conj_mem_of_fixedPoints _ _ (T147_135 i) (hfix147_135 i) _)
      ⟨147, by decide⟩ ⟨135, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨135, by decide⟩ 24 hp) Q2.T147_135_2 Q2.hfix147_135_2 Q2.hinj147_135_2
      Q2.hcardT147_135_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_135_2 i) (Q2.hfix147_135_2 i) _)
      colCert_147_135_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_136_0 (hp : 0 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 0 (transLenTr ⟨136, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 0 (transLenTr ⟨136, by decide⟩ 0 hp)) T147_136
      hfix147_136 hinj147_136 hcardT147_136
      (fun i => conj_mem_of_fixedPoints _ _ (T147_136 i) (hfix147_136 i) _)
      ⟨147, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 0 hp) Q2.T147_136_2 Q2.hfix147_136_2 Q2.hinj147_136_2
      Q2.hcardT147_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_136_2 i) (Q2.hfix147_136_2 i) _)
      colCert_147_136_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_136_1 (hp : 1 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 1 (transLenTr ⟨136, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 1 (transLenTr ⟨136, by decide⟩ 1 hp)) T147_136
      hfix147_136 hinj147_136 hcardT147_136
      (fun i => conj_mem_of_fixedPoints _ _ (T147_136 i) (hfix147_136 i) _)
      ⟨147, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 1 hp) Q2.T147_136_2 Q2.hfix147_136_2 Q2.hinj147_136_2
      Q2.hcardT147_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_136_2 i) (Q2.hfix147_136_2 i) _)
      colCert_147_136_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_136_2 (hp : 2 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 2 (transLenTr ⟨136, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 2 (transLenTr ⟨136, by decide⟩ 2 hp)) T147_136
      hfix147_136 hinj147_136 hcardT147_136
      (fun i => conj_mem_of_fixedPoints _ _ (T147_136 i) (hfix147_136 i) _)
      ⟨147, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 2 hp) Q2.T147_136_2 Q2.hfix147_136_2 Q2.hinj147_136_2
      Q2.hcardT147_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_136_2 i) (Q2.hfix147_136_2 i) _)
      colCert_147_136_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_136_3 (hp : 3 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 3 (transLenTr ⟨136, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 3 (transLenTr ⟨136, by decide⟩ 3 hp)) T147_136
      hfix147_136 hinj147_136 hcardT147_136
      (fun i => conj_mem_of_fixedPoints _ _ (T147_136 i) (hfix147_136 i) _)
      ⟨147, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 3 hp) Q2.T147_136_2 Q2.hfix147_136_2 Q2.hinj147_136_2
      Q2.hcardT147_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_136_2 i) (Q2.hfix147_136_2 i) _)
      colCert_147_136_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_136_4 (hp : 4 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 4 (transLenTr ⟨136, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 4 (transLenTr ⟨136, by decide⟩ 4 hp)) T147_136
      hfix147_136 hinj147_136 hcardT147_136
      (fun i => conj_mem_of_fixedPoints _ _ (T147_136 i) (hfix147_136 i) _)
      ⟨147, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 4 hp) Q2.T147_136_2 Q2.hfix147_136_2 Q2.hinj147_136_2
      Q2.hcardT147_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_136_2 i) (Q2.hfix147_136_2 i) _)
      colCert_147_136_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_136_5 (hp : 5 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 5 (transLenTr ⟨136, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 5 (transLenTr ⟨136, by decide⟩ 5 hp)) T147_136
      hfix147_136 hinj147_136 hcardT147_136
      (fun i => conj_mem_of_fixedPoints _ _ (T147_136 i) (hfix147_136 i) _)
      ⟨147, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 5 hp) Q2.T147_136_2 Q2.hfix147_136_2 Q2.hinj147_136_2
      Q2.hcardT147_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_136_2 i) (Q2.hfix147_136_2 i) _)
      colCert_147_136_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_136_6 (hp : 6 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 6 (transLenTr ⟨136, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 6 (transLenTr ⟨136, by decide⟩ 6 hp)) T147_136
      hfix147_136 hinj147_136 hcardT147_136
      (fun i => conj_mem_of_fixedPoints _ _ (T147_136 i) (hfix147_136 i) _)
      ⟨147, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 6 hp) Q2.T147_136_2 Q2.hfix147_136_2 Q2.hinj147_136_2
      Q2.hcardT147_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_136_2 i) (Q2.hfix147_136_2 i) _)
      colCert_147_136_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_136_7 (hp : 7 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 7 (transLenTr ⟨136, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 7 (transLenTr ⟨136, by decide⟩ 7 hp)) T147_136
      hfix147_136 hinj147_136 hcardT147_136
      (fun i => conj_mem_of_fixedPoints _ _ (T147_136 i) (hfix147_136 i) _)
      ⟨147, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 7 hp) Q2.T147_136_2 Q2.hfix147_136_2 Q2.hinj147_136_2
      Q2.hcardT147_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_136_2 i) (Q2.hfix147_136_2 i) _)
      colCert_147_136_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_136_8 (hp : 8 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 8 (transLenTr ⟨136, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 8 (transLenTr ⟨136, by decide⟩ 8 hp)) T147_136
      hfix147_136 hinj147_136 hcardT147_136
      (fun i => conj_mem_of_fixedPoints _ _ (T147_136 i) (hfix147_136 i) _)
      ⟨147, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 8 hp) Q2.T147_136_2 Q2.hfix147_136_2 Q2.hinj147_136_2
      Q2.hcardT147_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_136_2 i) (Q2.hfix147_136_2 i) _)
      colCert_147_136_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_136_9 (hp : 9 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 9 (transLenTr ⟨136, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 9 (transLenTr ⟨136, by decide⟩ 9 hp)) T147_136
      hfix147_136 hinj147_136 hcardT147_136
      (fun i => conj_mem_of_fixedPoints _ _ (T147_136 i) (hfix147_136 i) _)
      ⟨147, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 9 hp) Q2.T147_136_2 Q2.hfix147_136_2 Q2.hinj147_136_2
      Q2.hcardT147_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_136_2 i) (Q2.hfix147_136_2 i) _)
      colCert_147_136_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_136_10 (hp : 10 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 10 (transLenTr ⟨136, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 10 (transLenTr ⟨136, by decide⟩ 10 hp)) T147_136
      hfix147_136 hinj147_136 hcardT147_136
      (fun i => conj_mem_of_fixedPoints _ _ (T147_136 i) (hfix147_136 i) _)
      ⟨147, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 10 hp) Q2.T147_136_2 Q2.hfix147_136_2 Q2.hinj147_136_2
      Q2.hcardT147_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_136_2 i) (Q2.hfix147_136_2 i) _)
      colCert_147_136_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_136_11 (hp : 11 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 11 (transLenTr ⟨136, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 11 (transLenTr ⟨136, by decide⟩ 11 hp)) T147_136
      hfix147_136 hinj147_136 hcardT147_136
      (fun i => conj_mem_of_fixedPoints _ _ (T147_136 i) (hfix147_136 i) _)
      ⟨147, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 11 hp) Q2.T147_136_2 Q2.hfix147_136_2 Q2.hinj147_136_2
      Q2.hcardT147_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_136_2 i) (Q2.hfix147_136_2 i) _)
      colCert_147_136_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_136_12 (hp : 12 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 12 (transLenTr ⟨136, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 12 (transLenTr ⟨136, by decide⟩ 12 hp)) T147_136
      hfix147_136 hinj147_136 hcardT147_136
      (fun i => conj_mem_of_fixedPoints _ _ (T147_136 i) (hfix147_136 i) _)
      ⟨147, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 12 hp) Q2.T147_136_2 Q2.hfix147_136_2 Q2.hinj147_136_2
      Q2.hcardT147_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_136_2 i) (Q2.hfix147_136_2 i) _)
      colCert_147_136_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_136_13 (hp : 13 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 13 (transLenTr ⟨136, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 13 (transLenTr ⟨136, by decide⟩ 13 hp)) T147_136
      hfix147_136 hinj147_136 hcardT147_136
      (fun i => conj_mem_of_fixedPoints _ _ (T147_136 i) (hfix147_136 i) _)
      ⟨147, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 13 hp) Q2.T147_136_2 Q2.hfix147_136_2 Q2.hinj147_136_2
      Q2.hcardT147_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_136_2 i) (Q2.hfix147_136_2 i) _)
      colCert_147_136_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_136_14 (hp : 14 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 14 (transLenTr ⟨136, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 14 (transLenTr ⟨136, by decide⟩ 14 hp)) T147_136
      hfix147_136 hinj147_136 hcardT147_136
      (fun i => conj_mem_of_fixedPoints _ _ (T147_136 i) (hfix147_136 i) _)
      ⟨147, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 14 hp) Q2.T147_136_2 Q2.hfix147_136_2 Q2.hinj147_136_2
      Q2.hcardT147_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_136_2 i) (Q2.hfix147_136_2 i) _)
      colCert_147_136_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_136_15 (hp : 15 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 15 (transLenTr ⟨136, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 15 (transLenTr ⟨136, by decide⟩ 15 hp)) T147_136
      hfix147_136 hinj147_136 hcardT147_136
      (fun i => conj_mem_of_fixedPoints _ _ (T147_136 i) (hfix147_136 i) _)
      ⟨147, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 15 hp) Q2.T147_136_2 Q2.hfix147_136_2 Q2.hinj147_136_2
      Q2.hcardT147_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_136_2 i) (Q2.hfix147_136_2 i) _)
      colCert_147_136_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_136_16 (hp : 16 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 16 (transLenTr ⟨136, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 16 (transLenTr ⟨136, by decide⟩ 16 hp)) T147_136
      hfix147_136 hinj147_136 hcardT147_136
      (fun i => conj_mem_of_fixedPoints _ _ (T147_136 i) (hfix147_136 i) _)
      ⟨147, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 16 hp) Q2.T147_136_2 Q2.hfix147_136_2 Q2.hinj147_136_2
      Q2.hcardT147_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_136_2 i) (Q2.hfix147_136_2 i) _)
      colCert_147_136_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_136_17 (hp : 17 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 17 (transLenTr ⟨136, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 17 (transLenTr ⟨136, by decide⟩ 17 hp)) T147_136
      hfix147_136 hinj147_136 hcardT147_136
      (fun i => conj_mem_of_fixedPoints _ _ (T147_136 i) (hfix147_136 i) _)
      ⟨147, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 17 hp) Q2.T147_136_2 Q2.hfix147_136_2 Q2.hinj147_136_2
      Q2.hcardT147_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_136_2 i) (Q2.hfix147_136_2 i) _)
      colCert_147_136_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_136_18 (hp : 18 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 18 (transLenTr ⟨136, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 18 (transLenTr ⟨136, by decide⟩ 18 hp)) T147_136
      hfix147_136 hinj147_136 hcardT147_136
      (fun i => conj_mem_of_fixedPoints _ _ (T147_136 i) (hfix147_136 i) _)
      ⟨147, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 18 hp) Q2.T147_136_2 Q2.hfix147_136_2 Q2.hinj147_136_2
      Q2.hcardT147_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_136_2 i) (Q2.hfix147_136_2 i) _)
      colCert_147_136_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_136_19 (hp : 19 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 19 (transLenTr ⟨136, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 19 (transLenTr ⟨136, by decide⟩ 19 hp)) T147_136
      hfix147_136 hinj147_136 hcardT147_136
      (fun i => conj_mem_of_fixedPoints _ _ (T147_136 i) (hfix147_136 i) _)
      ⟨147, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 19 hp) Q2.T147_136_2 Q2.hfix147_136_2 Q2.hinj147_136_2
      Q2.hcardT147_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_136_2 i) (Q2.hfix147_136_2 i) _)
      colCert_147_136_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_136_20 (hp : 20 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 20 (transLenTr ⟨136, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 20 (transLenTr ⟨136, by decide⟩ 20 hp)) T147_136
      hfix147_136 hinj147_136 hcardT147_136
      (fun i => conj_mem_of_fixedPoints _ _ (T147_136 i) (hfix147_136 i) _)
      ⟨147, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 20 hp) Q2.T147_136_2 Q2.hfix147_136_2 Q2.hinj147_136_2
      Q2.hcardT147_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_136_2 i) (Q2.hfix147_136_2 i) _)
      colCert_147_136_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_136_21 (hp : 21 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 21 (transLenTr ⟨136, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 21 (transLenTr ⟨136, by decide⟩ 21 hp)) T147_136
      hfix147_136 hinj147_136 hcardT147_136
      (fun i => conj_mem_of_fixedPoints _ _ (T147_136 i) (hfix147_136 i) _)
      ⟨147, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 21 hp) Q2.T147_136_2 Q2.hfix147_136_2 Q2.hinj147_136_2
      Q2.hcardT147_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_136_2 i) (Q2.hfix147_136_2 i) _)
      colCert_147_136_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_136_22 (hp : 22 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 22 (transLenTr ⟨136, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 22 (transLenTr ⟨136, by decide⟩ 22 hp)) T147_136
      hfix147_136 hinj147_136 hcardT147_136
      (fun i => conj_mem_of_fixedPoints _ _ (T147_136 i) (hfix147_136 i) _)
      ⟨147, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 22 hp) Q2.T147_136_2 Q2.hfix147_136_2 Q2.hinj147_136_2
      Q2.hcardT147_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_136_2 i) (Q2.hfix147_136_2 i) _)
      colCert_147_136_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_136_23 (hp : 23 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 23 (transLenTr ⟨136, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 23 (transLenTr ⟨136, by decide⟩ 23 hp)) T147_136
      hfix147_136 hinj147_136 hcardT147_136
      (fun i => conj_mem_of_fixedPoints _ _ (T147_136 i) (hfix147_136 i) _)
      ⟨147, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 23 hp) Q2.T147_136_2 Q2.hfix147_136_2 Q2.hinj147_136_2
      Q2.hcardT147_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_136_2 i) (Q2.hfix147_136_2 i) _)
      colCert_147_136_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_136_24 (hp : 24 < (Q2.transData.getD 136 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ 24 (transLenTr ⟨136, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨136, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨136, by decide⟩ 24 (transLenTr ⟨136, by decide⟩ 24 hp)) T147_136
      hfix147_136 hinj147_136 hcardT147_136
      (fun i => conj_mem_of_fixedPoints _ _ (T147_136 i) (hfix147_136 i) _)
      ⟨147, by decide⟩ ⟨136, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨136, by decide⟩ 24 hp) Q2.T147_136_2 Q2.hfix147_136_2 Q2.hinj147_136_2
      Q2.hcardT147_136_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_136_2 i) (Q2.hfix147_136_2 i) _)
      colCert_147_136_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_137_0 (hp : 0 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 0 (transLenTr ⟨137, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 0 (transLenTr ⟨137, by decide⟩ 0 hp)) T147_137
      hfix147_137 hinj147_137 hcardT147_137
      (fun i => conj_mem_of_fixedPoints _ _ (T147_137 i) (hfix147_137 i) _)
      ⟨147, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 0 hp) Q2.T147_137_2 Q2.hfix147_137_2 Q2.hinj147_137_2
      Q2.hcardT147_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_137_2 i) (Q2.hfix147_137_2 i) _)
      colCert_147_137_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_137_1 (hp : 1 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 1 (transLenTr ⟨137, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 1 (transLenTr ⟨137, by decide⟩ 1 hp)) T147_137
      hfix147_137 hinj147_137 hcardT147_137
      (fun i => conj_mem_of_fixedPoints _ _ (T147_137 i) (hfix147_137 i) _)
      ⟨147, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 1 hp) Q2.T147_137_2 Q2.hfix147_137_2 Q2.hinj147_137_2
      Q2.hcardT147_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_137_2 i) (Q2.hfix147_137_2 i) _)
      colCert_147_137_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_137_2 (hp : 2 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 2 (transLenTr ⟨137, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 2 (transLenTr ⟨137, by decide⟩ 2 hp)) T147_137
      hfix147_137 hinj147_137 hcardT147_137
      (fun i => conj_mem_of_fixedPoints _ _ (T147_137 i) (hfix147_137 i) _)
      ⟨147, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 2 hp) Q2.T147_137_2 Q2.hfix147_137_2 Q2.hinj147_137_2
      Q2.hcardT147_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_137_2 i) (Q2.hfix147_137_2 i) _)
      colCert_147_137_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_137_3 (hp : 3 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 3 (transLenTr ⟨137, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 3 (transLenTr ⟨137, by decide⟩ 3 hp)) T147_137
      hfix147_137 hinj147_137 hcardT147_137
      (fun i => conj_mem_of_fixedPoints _ _ (T147_137 i) (hfix147_137 i) _)
      ⟨147, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 3 hp) Q2.T147_137_2 Q2.hfix147_137_2 Q2.hinj147_137_2
      Q2.hcardT147_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_137_2 i) (Q2.hfix147_137_2 i) _)
      colCert_147_137_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_137_4 (hp : 4 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 4 (transLenTr ⟨137, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 4 (transLenTr ⟨137, by decide⟩ 4 hp)) T147_137
      hfix147_137 hinj147_137 hcardT147_137
      (fun i => conj_mem_of_fixedPoints _ _ (T147_137 i) (hfix147_137 i) _)
      ⟨147, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 4 hp) Q2.T147_137_2 Q2.hfix147_137_2 Q2.hinj147_137_2
      Q2.hcardT147_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_137_2 i) (Q2.hfix147_137_2 i) _)
      colCert_147_137_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_137_5 (hp : 5 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 5 (transLenTr ⟨137, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 5 (transLenTr ⟨137, by decide⟩ 5 hp)) T147_137
      hfix147_137 hinj147_137 hcardT147_137
      (fun i => conj_mem_of_fixedPoints _ _ (T147_137 i) (hfix147_137 i) _)
      ⟨147, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 5 hp) Q2.T147_137_2 Q2.hfix147_137_2 Q2.hinj147_137_2
      Q2.hcardT147_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_137_2 i) (Q2.hfix147_137_2 i) _)
      colCert_147_137_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_137_6 (hp : 6 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 6 (transLenTr ⟨137, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 6 (transLenTr ⟨137, by decide⟩ 6 hp)) T147_137
      hfix147_137 hinj147_137 hcardT147_137
      (fun i => conj_mem_of_fixedPoints _ _ (T147_137 i) (hfix147_137 i) _)
      ⟨147, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 6 hp) Q2.T147_137_2 Q2.hfix147_137_2 Q2.hinj147_137_2
      Q2.hcardT147_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_137_2 i) (Q2.hfix147_137_2 i) _)
      colCert_147_137_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_137_7 (hp : 7 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 7 (transLenTr ⟨137, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 7 (transLenTr ⟨137, by decide⟩ 7 hp)) T147_137
      hfix147_137 hinj147_137 hcardT147_137
      (fun i => conj_mem_of_fixedPoints _ _ (T147_137 i) (hfix147_137 i) _)
      ⟨147, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 7 hp) Q2.T147_137_2 Q2.hfix147_137_2 Q2.hinj147_137_2
      Q2.hcardT147_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_137_2 i) (Q2.hfix147_137_2 i) _)
      colCert_147_137_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_137_8 (hp : 8 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 8 (transLenTr ⟨137, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 8 (transLenTr ⟨137, by decide⟩ 8 hp)) T147_137
      hfix147_137 hinj147_137 hcardT147_137
      (fun i => conj_mem_of_fixedPoints _ _ (T147_137 i) (hfix147_137 i) _)
      ⟨147, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 8 hp) Q2.T147_137_2 Q2.hfix147_137_2 Q2.hinj147_137_2
      Q2.hcardT147_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_137_2 i) (Q2.hfix147_137_2 i) _)
      colCert_147_137_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_137_9 (hp : 9 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 9 (transLenTr ⟨137, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 9 (transLenTr ⟨137, by decide⟩ 9 hp)) T147_137
      hfix147_137 hinj147_137 hcardT147_137
      (fun i => conj_mem_of_fixedPoints _ _ (T147_137 i) (hfix147_137 i) _)
      ⟨147, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 9 hp) Q2.T147_137_2 Q2.hfix147_137_2 Q2.hinj147_137_2
      Q2.hcardT147_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_137_2 i) (Q2.hfix147_137_2 i) _)
      colCert_147_137_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_137_10 (hp : 10 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 10 (transLenTr ⟨137, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 10 (transLenTr ⟨137, by decide⟩ 10 hp)) T147_137
      hfix147_137 hinj147_137 hcardT147_137
      (fun i => conj_mem_of_fixedPoints _ _ (T147_137 i) (hfix147_137 i) _)
      ⟨147, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 10 hp) Q2.T147_137_2 Q2.hfix147_137_2 Q2.hinj147_137_2
      Q2.hcardT147_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_137_2 i) (Q2.hfix147_137_2 i) _)
      colCert_147_137_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_137_11 (hp : 11 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 11 (transLenTr ⟨137, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 11 (transLenTr ⟨137, by decide⟩ 11 hp)) T147_137
      hfix147_137 hinj147_137 hcardT147_137
      (fun i => conj_mem_of_fixedPoints _ _ (T147_137 i) (hfix147_137 i) _)
      ⟨147, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 11 hp) Q2.T147_137_2 Q2.hfix147_137_2 Q2.hinj147_137_2
      Q2.hcardT147_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_137_2 i) (Q2.hfix147_137_2 i) _)
      colCert_147_137_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_137_12 (hp : 12 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 12 (transLenTr ⟨137, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 12 (transLenTr ⟨137, by decide⟩ 12 hp)) T147_137
      hfix147_137 hinj147_137 hcardT147_137
      (fun i => conj_mem_of_fixedPoints _ _ (T147_137 i) (hfix147_137 i) _)
      ⟨147, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 12 hp) Q2.T147_137_2 Q2.hfix147_137_2 Q2.hinj147_137_2
      Q2.hcardT147_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_137_2 i) (Q2.hfix147_137_2 i) _)
      colCert_147_137_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_137_13 (hp : 13 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 13 (transLenTr ⟨137, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 13 (transLenTr ⟨137, by decide⟩ 13 hp)) T147_137
      hfix147_137 hinj147_137 hcardT147_137
      (fun i => conj_mem_of_fixedPoints _ _ (T147_137 i) (hfix147_137 i) _)
      ⟨147, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 13 hp) Q2.T147_137_2 Q2.hfix147_137_2 Q2.hinj147_137_2
      Q2.hcardT147_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_137_2 i) (Q2.hfix147_137_2 i) _)
      colCert_147_137_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_137_14 (hp : 14 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 14 (transLenTr ⟨137, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 14 (transLenTr ⟨137, by decide⟩ 14 hp)) T147_137
      hfix147_137 hinj147_137 hcardT147_137
      (fun i => conj_mem_of_fixedPoints _ _ (T147_137 i) (hfix147_137 i) _)
      ⟨147, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 14 hp) Q2.T147_137_2 Q2.hfix147_137_2 Q2.hinj147_137_2
      Q2.hcardT147_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_137_2 i) (Q2.hfix147_137_2 i) _)
      colCert_147_137_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_137_15 (hp : 15 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 15 (transLenTr ⟨137, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 15 (transLenTr ⟨137, by decide⟩ 15 hp)) T147_137
      hfix147_137 hinj147_137 hcardT147_137
      (fun i => conj_mem_of_fixedPoints _ _ (T147_137 i) (hfix147_137 i) _)
      ⟨147, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 15 hp) Q2.T147_137_2 Q2.hfix147_137_2 Q2.hinj147_137_2
      Q2.hcardT147_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_137_2 i) (Q2.hfix147_137_2 i) _)
      colCert_147_137_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_137_16 (hp : 16 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 16 (transLenTr ⟨137, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 16 (transLenTr ⟨137, by decide⟩ 16 hp)) T147_137
      hfix147_137 hinj147_137 hcardT147_137
      (fun i => conj_mem_of_fixedPoints _ _ (T147_137 i) (hfix147_137 i) _)
      ⟨147, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 16 hp) Q2.T147_137_2 Q2.hfix147_137_2 Q2.hinj147_137_2
      Q2.hcardT147_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_137_2 i) (Q2.hfix147_137_2 i) _)
      colCert_147_137_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_137_17 (hp : 17 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 17 (transLenTr ⟨137, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 17 (transLenTr ⟨137, by decide⟩ 17 hp)) T147_137
      hfix147_137 hinj147_137 hcardT147_137
      (fun i => conj_mem_of_fixedPoints _ _ (T147_137 i) (hfix147_137 i) _)
      ⟨147, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 17 hp) Q2.T147_137_2 Q2.hfix147_137_2 Q2.hinj147_137_2
      Q2.hcardT147_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_137_2 i) (Q2.hfix147_137_2 i) _)
      colCert_147_137_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_137_18 (hp : 18 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 18 (transLenTr ⟨137, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 18 (transLenTr ⟨137, by decide⟩ 18 hp)) T147_137
      hfix147_137 hinj147_137 hcardT147_137
      (fun i => conj_mem_of_fixedPoints _ _ (T147_137 i) (hfix147_137 i) _)
      ⟨147, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 18 hp) Q2.T147_137_2 Q2.hfix147_137_2 Q2.hinj147_137_2
      Q2.hcardT147_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_137_2 i) (Q2.hfix147_137_2 i) _)
      colCert_147_137_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_137_19 (hp : 19 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 19 (transLenTr ⟨137, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 19 (transLenTr ⟨137, by decide⟩ 19 hp)) T147_137
      hfix147_137 hinj147_137 hcardT147_137
      (fun i => conj_mem_of_fixedPoints _ _ (T147_137 i) (hfix147_137 i) _)
      ⟨147, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 19 hp) Q2.T147_137_2 Q2.hfix147_137_2 Q2.hinj147_137_2
      Q2.hcardT147_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_137_2 i) (Q2.hfix147_137_2 i) _)
      colCert_147_137_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_137_20 (hp : 20 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 20 (transLenTr ⟨137, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 20 (transLenTr ⟨137, by decide⟩ 20 hp)) T147_137
      hfix147_137 hinj147_137 hcardT147_137
      (fun i => conj_mem_of_fixedPoints _ _ (T147_137 i) (hfix147_137 i) _)
      ⟨147, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 20 hp) Q2.T147_137_2 Q2.hfix147_137_2 Q2.hinj147_137_2
      Q2.hcardT147_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_137_2 i) (Q2.hfix147_137_2 i) _)
      colCert_147_137_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_137_21 (hp : 21 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 21 (transLenTr ⟨137, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 21 (transLenTr ⟨137, by decide⟩ 21 hp)) T147_137
      hfix147_137 hinj147_137 hcardT147_137
      (fun i => conj_mem_of_fixedPoints _ _ (T147_137 i) (hfix147_137 i) _)
      ⟨147, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 21 hp) Q2.T147_137_2 Q2.hfix147_137_2 Q2.hinj147_137_2
      Q2.hcardT147_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_137_2 i) (Q2.hfix147_137_2 i) _)
      colCert_147_137_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_137_22 (hp : 22 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 22 (transLenTr ⟨137, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 22 (transLenTr ⟨137, by decide⟩ 22 hp)) T147_137
      hfix147_137 hinj147_137 hcardT147_137
      (fun i => conj_mem_of_fixedPoints _ _ (T147_137 i) (hfix147_137 i) _)
      ⟨147, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 22 hp) Q2.T147_137_2 Q2.hfix147_137_2 Q2.hinj147_137_2
      Q2.hcardT147_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_137_2 i) (Q2.hfix147_137_2 i) _)
      colCert_147_137_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_137_23 (hp : 23 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 23 (transLenTr ⟨137, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 23 (transLenTr ⟨137, by decide⟩ 23 hp)) T147_137
      hfix147_137 hinj147_137 hcardT147_137
      (fun i => conj_mem_of_fixedPoints _ _ (T147_137 i) (hfix147_137 i) _)
      ⟨147, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 23 hp) Q2.T147_137_2 Q2.hfix147_137_2 Q2.hinj147_137_2
      Q2.hcardT147_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_137_2 i) (Q2.hfix147_137_2 i) _)
      colCert_147_137_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_137_24 (hp : 24 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 24 (transLenTr ⟨137, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 24 (transLenTr ⟨137, by decide⟩ 24 hp)) T147_137
      hfix147_137 hinj147_137 hcardT147_137
      (fun i => conj_mem_of_fixedPoints _ _ (T147_137 i) (hfix147_137 i) _)
      ⟨147, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 24 hp) Q2.T147_137_2 Q2.hfix147_137_2 Q2.hinj147_137_2
      Q2.hcardT147_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_137_2 i) (Q2.hfix147_137_2 i) _)
      colCert_147_137_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_138_0 (hp : 0 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 0 (transLenTr ⟨138, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 0 (transLenTr ⟨138, by decide⟩ 0 hp)) T147_138
      hfix147_138 hinj147_138 hcardT147_138
      (fun i => conj_mem_of_fixedPoints _ _ (T147_138 i) (hfix147_138 i) _)
      ⟨147, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 0 hp) Q2.T147_138_2 Q2.hfix147_138_2 Q2.hinj147_138_2
      Q2.hcardT147_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_138_2 i) (Q2.hfix147_138_2 i) _)
      colCert_147_138_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_138_1 (hp : 1 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 1 (transLenTr ⟨138, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 1 (transLenTr ⟨138, by decide⟩ 1 hp)) T147_138
      hfix147_138 hinj147_138 hcardT147_138
      (fun i => conj_mem_of_fixedPoints _ _ (T147_138 i) (hfix147_138 i) _)
      ⟨147, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 1 hp) Q2.T147_138_2 Q2.hfix147_138_2 Q2.hinj147_138_2
      Q2.hcardT147_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_138_2 i) (Q2.hfix147_138_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨138, by decide⟩ 1 (transLenTr ⟨138, by decide⟩ 1 hp) : ↥(reps ⟨138, by decide⟩)) : Coordinate 1)
        T147_138 = colFn colCertDiv_147_138_1.D1 (m := 1) from colCertDiv_147_138_1.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨138, by decide⟩ 1 hp : ↥(Q2.reps ⟨138, by decide⟩)) : Coordinate 2)
        Q2.T147_138_2 = colFn colCertDiv_147_138_1.D2 (m := 1) from colCertDiv_147_138_1.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_138_1_match


theorem leaf_147_138_2 (hp : 2 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 2 (transLenTr ⟨138, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 2 (transLenTr ⟨138, by decide⟩ 2 hp)) T147_138
      hfix147_138 hinj147_138 hcardT147_138
      (fun i => conj_mem_of_fixedPoints _ _ (T147_138 i) (hfix147_138 i) _)
      ⟨147, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 2 hp) Q2.T147_138_2 Q2.hfix147_138_2 Q2.hinj147_138_2
      Q2.hcardT147_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_138_2 i) (Q2.hfix147_138_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨138, by decide⟩ 2 (transLenTr ⟨138, by decide⟩ 2 hp) : ↥(reps ⟨138, by decide⟩)) : Coordinate 1)
        T147_138 = colFn colCertDiv_147_138_2.D1 (m := 1) from colCertDiv_147_138_2.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨138, by decide⟩ 2 hp : ↥(Q2.reps ⟨138, by decide⟩)) : Coordinate 2)
        Q2.T147_138_2 = colFn colCertDiv_147_138_2.D2 (m := 1) from colCertDiv_147_138_2.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_138_2_match


theorem leaf_147_138_3 (hp : 3 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 3 (transLenTr ⟨138, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 3 (transLenTr ⟨138, by decide⟩ 3 hp)) T147_138
      hfix147_138 hinj147_138 hcardT147_138
      (fun i => conj_mem_of_fixedPoints _ _ (T147_138 i) (hfix147_138 i) _)
      ⟨147, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 3 hp) Q2.T147_138_2 Q2.hfix147_138_2 Q2.hinj147_138_2
      Q2.hcardT147_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_138_2 i) (Q2.hfix147_138_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨138, by decide⟩ 3 (transLenTr ⟨138, by decide⟩ 3 hp) : ↥(reps ⟨138, by decide⟩)) : Coordinate 1)
        T147_138 = colFn colCertDiv_147_138_3.D1 (m := 1) from colCertDiv_147_138_3.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨138, by decide⟩ 3 hp : ↥(Q2.reps ⟨138, by decide⟩)) : Coordinate 2)
        Q2.T147_138_2 = colFn colCertDiv_147_138_3.D2 (m := 1) from colCertDiv_147_138_3.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_138_3_match


theorem leaf_147_138_4 (hp : 4 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 4 (transLenTr ⟨138, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 4 (transLenTr ⟨138, by decide⟩ 4 hp)) T147_138
      hfix147_138 hinj147_138 hcardT147_138
      (fun i => conj_mem_of_fixedPoints _ _ (T147_138 i) (hfix147_138 i) _)
      ⟨147, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 4 hp) Q2.T147_138_2 Q2.hfix147_138_2 Q2.hinj147_138_2
      Q2.hcardT147_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_138_2 i) (Q2.hfix147_138_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨138, by decide⟩ 4 (transLenTr ⟨138, by decide⟩ 4 hp) : ↥(reps ⟨138, by decide⟩)) : Coordinate 1)
        T147_138 = colFn colCertDiv_147_138_4.D1 (m := 1) from colCertDiv_147_138_4.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨138, by decide⟩ 4 hp : ↥(Q2.reps ⟨138, by decide⟩)) : Coordinate 2)
        Q2.T147_138_2 = colFn colCertDiv_147_138_4.D2 (m := 1) from colCertDiv_147_138_4.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_138_4_match


theorem leaf_147_138_5 (hp : 5 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 5 (transLenTr ⟨138, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 5 (transLenTr ⟨138, by decide⟩ 5 hp)) T147_138
      hfix147_138 hinj147_138 hcardT147_138
      (fun i => conj_mem_of_fixedPoints _ _ (T147_138 i) (hfix147_138 i) _)
      ⟨147, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 5 hp) Q2.T147_138_2 Q2.hfix147_138_2 Q2.hinj147_138_2
      Q2.hcardT147_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_138_2 i) (Q2.hfix147_138_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨138, by decide⟩ 5 (transLenTr ⟨138, by decide⟩ 5 hp) : ↥(reps ⟨138, by decide⟩)) : Coordinate 1)
        T147_138 = colFn colCertDiv_147_138_5.D1 (m := 1) from colCertDiv_147_138_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨138, by decide⟩ 5 hp : ↥(Q2.reps ⟨138, by decide⟩)) : Coordinate 2)
        Q2.T147_138_2 = colFn colCertDiv_147_138_5.D2 (m := 1) from colCertDiv_147_138_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_138_5_match


theorem leaf_147_138_6 (hp : 6 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 6 (transLenTr ⟨138, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 6 (transLenTr ⟨138, by decide⟩ 6 hp)) T147_138
      hfix147_138 hinj147_138 hcardT147_138
      (fun i => conj_mem_of_fixedPoints _ _ (T147_138 i) (hfix147_138 i) _)
      ⟨147, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 6 hp) Q2.T147_138_2 Q2.hfix147_138_2 Q2.hinj147_138_2
      Q2.hcardT147_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_138_2 i) (Q2.hfix147_138_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨138, by decide⟩ 6 (transLenTr ⟨138, by decide⟩ 6 hp) : ↥(reps ⟨138, by decide⟩)) : Coordinate 1)
        T147_138 = colFn colCertDiv_147_138_6.D1 (m := 1) from colCertDiv_147_138_6.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨138, by decide⟩ 6 hp : ↥(Q2.reps ⟨138, by decide⟩)) : Coordinate 2)
        Q2.T147_138_2 = colFn colCertDiv_147_138_6.D2 (m := 1) from colCertDiv_147_138_6.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_138_6_match


theorem leaf_147_138_7 (hp : 7 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 7 (transLenTr ⟨138, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 7 (transLenTr ⟨138, by decide⟩ 7 hp)) T147_138
      hfix147_138 hinj147_138 hcardT147_138
      (fun i => conj_mem_of_fixedPoints _ _ (T147_138 i) (hfix147_138 i) _)
      ⟨147, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 7 hp) Q2.T147_138_2 Q2.hfix147_138_2 Q2.hinj147_138_2
      Q2.hcardT147_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_138_2 i) (Q2.hfix147_138_2 i) _)
      colCert_147_138_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_138_8 (hp : 8 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 8 (transLenTr ⟨138, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 8 (transLenTr ⟨138, by decide⟩ 8 hp)) T147_138
      hfix147_138 hinj147_138 hcardT147_138
      (fun i => conj_mem_of_fixedPoints _ _ (T147_138 i) (hfix147_138 i) _)
      ⟨147, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 8 hp) Q2.T147_138_2 Q2.hfix147_138_2 Q2.hinj147_138_2
      Q2.hcardT147_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_138_2 i) (Q2.hfix147_138_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨138, by decide⟩ 8 (transLenTr ⟨138, by decide⟩ 8 hp) : ↥(reps ⟨138, by decide⟩)) : Coordinate 1)
        T147_138 = colFn colCertDiv_147_138_8.D1 (m := 1) from colCertDiv_147_138_8.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨138, by decide⟩ 8 hp : ↥(Q2.reps ⟨138, by decide⟩)) : Coordinate 2)
        Q2.T147_138_2 = colFn colCertDiv_147_138_8.D2 (m := 1) from colCertDiv_147_138_8.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_138_8_match


theorem leaf_147_138_9 (hp : 9 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 9 (transLenTr ⟨138, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 9 (transLenTr ⟨138, by decide⟩ 9 hp)) T147_138
      hfix147_138 hinj147_138 hcardT147_138
      (fun i => conj_mem_of_fixedPoints _ _ (T147_138 i) (hfix147_138 i) _)
      ⟨147, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 9 hp) Q2.T147_138_2 Q2.hfix147_138_2 Q2.hinj147_138_2
      Q2.hcardT147_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_138_2 i) (Q2.hfix147_138_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨138, by decide⟩ 9 (transLenTr ⟨138, by decide⟩ 9 hp) : ↥(reps ⟨138, by decide⟩)) : Coordinate 1)
        T147_138 = colFn colCertDiv_147_138_9.D1 (m := 1) from colCertDiv_147_138_9.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨138, by decide⟩ 9 hp : ↥(Q2.reps ⟨138, by decide⟩)) : Coordinate 2)
        Q2.T147_138_2 = colFn colCertDiv_147_138_9.D2 (m := 1) from colCertDiv_147_138_9.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_138_9_match


theorem leaf_147_138_10 (hp : 10 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 10 (transLenTr ⟨138, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 10 (transLenTr ⟨138, by decide⟩ 10 hp)) T147_138
      hfix147_138 hinj147_138 hcardT147_138
      (fun i => conj_mem_of_fixedPoints _ _ (T147_138 i) (hfix147_138 i) _)
      ⟨147, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 10 hp) Q2.T147_138_2 Q2.hfix147_138_2 Q2.hinj147_138_2
      Q2.hcardT147_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_138_2 i) (Q2.hfix147_138_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨138, by decide⟩ 10 (transLenTr ⟨138, by decide⟩ 10 hp) : ↥(reps ⟨138, by decide⟩)) : Coordinate 1)
        T147_138 = colFn colCertDiv_147_138_10.D1 (m := 1) from colCertDiv_147_138_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨138, by decide⟩ 10 hp : ↥(Q2.reps ⟨138, by decide⟩)) : Coordinate 2)
        Q2.T147_138_2 = colFn colCertDiv_147_138_10.D2 (m := 1) from colCertDiv_147_138_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_138_10_match


theorem leaf_147_138_11 (hp : 11 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 11 (transLenTr ⟨138, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 11 (transLenTr ⟨138, by decide⟩ 11 hp)) T147_138
      hfix147_138 hinj147_138 hcardT147_138
      (fun i => conj_mem_of_fixedPoints _ _ (T147_138 i) (hfix147_138 i) _)
      ⟨147, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 11 hp) Q2.T147_138_2 Q2.hfix147_138_2 Q2.hinj147_138_2
      Q2.hcardT147_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_138_2 i) (Q2.hfix147_138_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨138, by decide⟩ 11 (transLenTr ⟨138, by decide⟩ 11 hp) : ↥(reps ⟨138, by decide⟩)) : Coordinate 1)
        T147_138 = colFn colCertDiv_147_138_11.D1 (m := 1) from colCertDiv_147_138_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨138, by decide⟩ 11 hp : ↥(Q2.reps ⟨138, by decide⟩)) : Coordinate 2)
        Q2.T147_138_2 = colFn colCertDiv_147_138_11.D2 (m := 1) from colCertDiv_147_138_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_138_11_match


theorem leaf_147_138_12 (hp : 12 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 12 (transLenTr ⟨138, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 12 (transLenTr ⟨138, by decide⟩ 12 hp)) T147_138
      hfix147_138 hinj147_138 hcardT147_138
      (fun i => conj_mem_of_fixedPoints _ _ (T147_138 i) (hfix147_138 i) _)
      ⟨147, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 12 hp) Q2.T147_138_2 Q2.hfix147_138_2 Q2.hinj147_138_2
      Q2.hcardT147_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_138_2 i) (Q2.hfix147_138_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨138, by decide⟩ 12 (transLenTr ⟨138, by decide⟩ 12 hp) : ↥(reps ⟨138, by decide⟩)) : Coordinate 1)
        T147_138 = colFn colCertDiv_147_138_12.D1 (m := 1) from colCertDiv_147_138_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨138, by decide⟩ 12 hp : ↥(Q2.reps ⟨138, by decide⟩)) : Coordinate 2)
        Q2.T147_138_2 = colFn colCertDiv_147_138_12.D2 (m := 1) from colCertDiv_147_138_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_138_12_match


theorem leaf_147_138_13 (hp : 13 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 13 (transLenTr ⟨138, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 13 (transLenTr ⟨138, by decide⟩ 13 hp)) T147_138
      hfix147_138 hinj147_138 hcardT147_138
      (fun i => conj_mem_of_fixedPoints _ _ (T147_138 i) (hfix147_138 i) _)
      ⟨147, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 13 hp) Q2.T147_138_2 Q2.hfix147_138_2 Q2.hinj147_138_2
      Q2.hcardT147_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_138_2 i) (Q2.hfix147_138_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨138, by decide⟩ 13 (transLenTr ⟨138, by decide⟩ 13 hp) : ↥(reps ⟨138, by decide⟩)) : Coordinate 1)
        T147_138 = colFn colCertDiv_147_138_13.D1 (m := 1) from colCertDiv_147_138_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨138, by decide⟩ 13 hp : ↥(Q2.reps ⟨138, by decide⟩)) : Coordinate 2)
        Q2.T147_138_2 = colFn colCertDiv_147_138_13.D2 (m := 1) from colCertDiv_147_138_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_138_13_match


theorem leaf_147_138_14 (hp : 14 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 14 (transLenTr ⟨138, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 14 (transLenTr ⟨138, by decide⟩ 14 hp)) T147_138
      hfix147_138 hinj147_138 hcardT147_138
      (fun i => conj_mem_of_fixedPoints _ _ (T147_138 i) (hfix147_138 i) _)
      ⟨147, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 14 hp) Q2.T147_138_2 Q2.hfix147_138_2 Q2.hinj147_138_2
      Q2.hcardT147_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_138_2 i) (Q2.hfix147_138_2 i) _)
      colCert_147_138_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_138_15 (hp : 15 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 15 (transLenTr ⟨138, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 15 (transLenTr ⟨138, by decide⟩ 15 hp)) T147_138
      hfix147_138 hinj147_138 hcardT147_138
      (fun i => conj_mem_of_fixedPoints _ _ (T147_138 i) (hfix147_138 i) _)
      ⟨147, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 15 hp) Q2.T147_138_2 Q2.hfix147_138_2 Q2.hinj147_138_2
      Q2.hcardT147_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_138_2 i) (Q2.hfix147_138_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨138, by decide⟩ 15 (transLenTr ⟨138, by decide⟩ 15 hp) : ↥(reps ⟨138, by decide⟩)) : Coordinate 1)
        T147_138 = colFn colCertDiv_147_138_15.D1 (m := 1) from colCertDiv_147_138_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨138, by decide⟩ 15 hp : ↥(Q2.reps ⟨138, by decide⟩)) : Coordinate 2)
        Q2.T147_138_2 = colFn colCertDiv_147_138_15.D2 (m := 1) from colCertDiv_147_138_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_138_15_match


theorem leaf_147_138_16 (hp : 16 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 16 (transLenTr ⟨138, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 16 (transLenTr ⟨138, by decide⟩ 16 hp)) T147_138
      hfix147_138 hinj147_138 hcardT147_138
      (fun i => conj_mem_of_fixedPoints _ _ (T147_138 i) (hfix147_138 i) _)
      ⟨147, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 16 hp) Q2.T147_138_2 Q2.hfix147_138_2 Q2.hinj147_138_2
      Q2.hcardT147_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_138_2 i) (Q2.hfix147_138_2 i) _)
      colCert_147_138_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_138_17 (hp : 17 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 17 (transLenTr ⟨138, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 17 (transLenTr ⟨138, by decide⟩ 17 hp)) T147_138
      hfix147_138 hinj147_138 hcardT147_138
      (fun i => conj_mem_of_fixedPoints _ _ (T147_138 i) (hfix147_138 i) _)
      ⟨147, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 17 hp) Q2.T147_138_2 Q2.hfix147_138_2 Q2.hinj147_138_2
      Q2.hcardT147_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_138_2 i) (Q2.hfix147_138_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨138, by decide⟩ 17 (transLenTr ⟨138, by decide⟩ 17 hp) : ↥(reps ⟨138, by decide⟩)) : Coordinate 1)
        T147_138 = colFn colCertDiv_147_138_17.D1 (m := 1) from colCertDiv_147_138_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨138, by decide⟩ 17 hp : ↥(Q2.reps ⟨138, by decide⟩)) : Coordinate 2)
        Q2.T147_138_2 = colFn colCertDiv_147_138_17.D2 (m := 1) from colCertDiv_147_138_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_138_17_match


theorem leaf_147_138_18 (hp : 18 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 18 (transLenTr ⟨138, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 18 (transLenTr ⟨138, by decide⟩ 18 hp)) T147_138
      hfix147_138 hinj147_138 hcardT147_138
      (fun i => conj_mem_of_fixedPoints _ _ (T147_138 i) (hfix147_138 i) _)
      ⟨147, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 18 hp) Q2.T147_138_2 Q2.hfix147_138_2 Q2.hinj147_138_2
      Q2.hcardT147_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_138_2 i) (Q2.hfix147_138_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨138, by decide⟩ 18 (transLenTr ⟨138, by decide⟩ 18 hp) : ↥(reps ⟨138, by decide⟩)) : Coordinate 1)
        T147_138 = colFn colCertDiv_147_138_18.D1 (m := 1) from colCertDiv_147_138_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨138, by decide⟩ 18 hp : ↥(Q2.reps ⟨138, by decide⟩)) : Coordinate 2)
        Q2.T147_138_2 = colFn colCertDiv_147_138_18.D2 (m := 1) from colCertDiv_147_138_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_138_18_match


theorem leaf_147_138_19 (hp : 19 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 19 (transLenTr ⟨138, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 19 (transLenTr ⟨138, by decide⟩ 19 hp)) T147_138
      hfix147_138 hinj147_138 hcardT147_138
      (fun i => conj_mem_of_fixedPoints _ _ (T147_138 i) (hfix147_138 i) _)
      ⟨147, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 19 hp) Q2.T147_138_2 Q2.hfix147_138_2 Q2.hinj147_138_2
      Q2.hcardT147_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_138_2 i) (Q2.hfix147_138_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨138, by decide⟩ 19 (transLenTr ⟨138, by decide⟩ 19 hp) : ↥(reps ⟨138, by decide⟩)) : Coordinate 1)
        T147_138 = colFn colCertDiv_147_138_19.D1 (m := 1) from colCertDiv_147_138_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨138, by decide⟩ 19 hp : ↥(Q2.reps ⟨138, by decide⟩)) : Coordinate 2)
        Q2.T147_138_2 = colFn colCertDiv_147_138_19.D2 (m := 1) from colCertDiv_147_138_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_138_19_match


theorem leaf_147_138_20 (hp : 20 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 20 (transLenTr ⟨138, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 20 (transLenTr ⟨138, by decide⟩ 20 hp)) T147_138
      hfix147_138 hinj147_138 hcardT147_138
      (fun i => conj_mem_of_fixedPoints _ _ (T147_138 i) (hfix147_138 i) _)
      ⟨147, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 20 hp) Q2.T147_138_2 Q2.hfix147_138_2 Q2.hinj147_138_2
      Q2.hcardT147_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_138_2 i) (Q2.hfix147_138_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨138, by decide⟩ 20 (transLenTr ⟨138, by decide⟩ 20 hp) : ↥(reps ⟨138, by decide⟩)) : Coordinate 1)
        T147_138 = colFn colCertDiv_147_138_20.D1 (m := 1) from colCertDiv_147_138_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨138, by decide⟩ 20 hp : ↥(Q2.reps ⟨138, by decide⟩)) : Coordinate 2)
        Q2.T147_138_2 = colFn colCertDiv_147_138_20.D2 (m := 1) from colCertDiv_147_138_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_138_20_match


theorem leaf_147_138_21 (hp : 21 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 21 (transLenTr ⟨138, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 21 (transLenTr ⟨138, by decide⟩ 21 hp)) T147_138
      hfix147_138 hinj147_138 hcardT147_138
      (fun i => conj_mem_of_fixedPoints _ _ (T147_138 i) (hfix147_138 i) _)
      ⟨147, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 21 hp) Q2.T147_138_2 Q2.hfix147_138_2 Q2.hinj147_138_2
      Q2.hcardT147_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_138_2 i) (Q2.hfix147_138_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨138, by decide⟩ 21 (transLenTr ⟨138, by decide⟩ 21 hp) : ↥(reps ⟨138, by decide⟩)) : Coordinate 1)
        T147_138 = colFn colCertDiv_147_138_21.D1 (m := 1) from colCertDiv_147_138_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨138, by decide⟩ 21 hp : ↥(Q2.reps ⟨138, by decide⟩)) : Coordinate 2)
        Q2.T147_138_2 = colFn colCertDiv_147_138_21.D2 (m := 1) from colCertDiv_147_138_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_138_21_match


theorem leaf_147_138_22 (hp : 22 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 22 (transLenTr ⟨138, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 22 (transLenTr ⟨138, by decide⟩ 22 hp)) T147_138
      hfix147_138 hinj147_138 hcardT147_138
      (fun i => conj_mem_of_fixedPoints _ _ (T147_138 i) (hfix147_138 i) _)
      ⟨147, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 22 hp) Q2.T147_138_2 Q2.hfix147_138_2 Q2.hinj147_138_2
      Q2.hcardT147_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_138_2 i) (Q2.hfix147_138_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨138, by decide⟩ 22 (transLenTr ⟨138, by decide⟩ 22 hp) : ↥(reps ⟨138, by decide⟩)) : Coordinate 1)
        T147_138 = colFn colCertDiv_147_138_22.D1 (m := 1) from colCertDiv_147_138_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨138, by decide⟩ 22 hp : ↥(Q2.reps ⟨138, by decide⟩)) : Coordinate 2)
        Q2.T147_138_2 = colFn colCertDiv_147_138_22.D2 (m := 1) from colCertDiv_147_138_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_138_22_match


theorem leaf_147_138_23 (hp : 23 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 23 (transLenTr ⟨138, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 23 (transLenTr ⟨138, by decide⟩ 23 hp)) T147_138
      hfix147_138 hinj147_138 hcardT147_138
      (fun i => conj_mem_of_fixedPoints _ _ (T147_138 i) (hfix147_138 i) _)
      ⟨147, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 23 hp) Q2.T147_138_2 Q2.hfix147_138_2 Q2.hinj147_138_2
      Q2.hcardT147_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_138_2 i) (Q2.hfix147_138_2 i) _)
      colCert_147_138_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_138_24 (hp : 24 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 24 (transLenTr ⟨138, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 24 (transLenTr ⟨138, by decide⟩ 24 hp)) T147_138
      hfix147_138 hinj147_138 hcardT147_138
      (fun i => conj_mem_of_fixedPoints _ _ (T147_138 i) (hfix147_138 i) _)
      ⟨147, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 24 hp) Q2.T147_138_2 Q2.hfix147_138_2 Q2.hinj147_138_2
      Q2.hcardT147_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_138_2 i) (Q2.hfix147_138_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨138, by decide⟩ 24 (transLenTr ⟨138, by decide⟩ 24 hp) : ↥(reps ⟨138, by decide⟩)) : Coordinate 1)
        T147_138 = colFn colCertDiv_147_138_24.D1 (m := 1) from colCertDiv_147_138_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨138, by decide⟩ 24 hp : ↥(Q2.reps ⟨138, by decide⟩)) : Coordinate 2)
        Q2.T147_138_2 = colFn colCertDiv_147_138_24.D2 (m := 1) from colCertDiv_147_138_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_138_24_match


theorem leaf_147_139_0 (hp : 0 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 0 (transLenTr ⟨139, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 0 (transLenTr ⟨139, by decide⟩ 0 hp)) T147_139
      hfix147_139 hinj147_139 hcardT147_139
      (fun i => conj_mem_of_fixedPoints _ _ (T147_139 i) (hfix147_139 i) _)
      ⟨147, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 0 hp) Q2.T147_139_2 Q2.hfix147_139_2 Q2.hinj147_139_2
      Q2.hcardT147_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_139_2 i) (Q2.hfix147_139_2 i) _)
      colCert_147_139_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_139_1 (hp : 1 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 1 (transLenTr ⟨139, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 1 (transLenTr ⟨139, by decide⟩ 1 hp)) T147_139
      hfix147_139 hinj147_139 hcardT147_139
      (fun i => conj_mem_of_fixedPoints _ _ (T147_139 i) (hfix147_139 i) _)
      ⟨147, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 1 hp) Q2.T147_139_2 Q2.hfix147_139_2 Q2.hinj147_139_2
      Q2.hcardT147_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_139_2 i) (Q2.hfix147_139_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨139, by decide⟩ 1 (transLenTr ⟨139, by decide⟩ 1 hp) : ↥(reps ⟨139, by decide⟩)) : Coordinate 1)
        T147_139 = colFn colCertDiv_147_139_1.D1 (m := 1) from colCertDiv_147_139_1.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨139, by decide⟩ 1 hp : ↥(Q2.reps ⟨139, by decide⟩)) : Coordinate 2)
        Q2.T147_139_2 = colFn colCertDiv_147_139_1.D2 (m := 1) from colCertDiv_147_139_1.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_139_1_match


theorem leaf_147_139_2 (hp : 2 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 2 (transLenTr ⟨139, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 2 (transLenTr ⟨139, by decide⟩ 2 hp)) T147_139
      hfix147_139 hinj147_139 hcardT147_139
      (fun i => conj_mem_of_fixedPoints _ _ (T147_139 i) (hfix147_139 i) _)
      ⟨147, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 2 hp) Q2.T147_139_2 Q2.hfix147_139_2 Q2.hinj147_139_2
      Q2.hcardT147_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_139_2 i) (Q2.hfix147_139_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨139, by decide⟩ 2 (transLenTr ⟨139, by decide⟩ 2 hp) : ↥(reps ⟨139, by decide⟩)) : Coordinate 1)
        T147_139 = colFn colCertDiv_147_139_2.D1 (m := 1) from colCertDiv_147_139_2.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨139, by decide⟩ 2 hp : ↥(Q2.reps ⟨139, by decide⟩)) : Coordinate 2)
        Q2.T147_139_2 = colFn colCertDiv_147_139_2.D2 (m := 1) from colCertDiv_147_139_2.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_139_2_match


theorem leaf_147_139_3 (hp : 3 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 3 (transLenTr ⟨139, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 3 (transLenTr ⟨139, by decide⟩ 3 hp)) T147_139
      hfix147_139 hinj147_139 hcardT147_139
      (fun i => conj_mem_of_fixedPoints _ _ (T147_139 i) (hfix147_139 i) _)
      ⟨147, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 3 hp) Q2.T147_139_2 Q2.hfix147_139_2 Q2.hinj147_139_2
      Q2.hcardT147_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_139_2 i) (Q2.hfix147_139_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨139, by decide⟩ 3 (transLenTr ⟨139, by decide⟩ 3 hp) : ↥(reps ⟨139, by decide⟩)) : Coordinate 1)
        T147_139 = colFn colCertDiv_147_139_3.D1 (m := 1) from colCertDiv_147_139_3.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨139, by decide⟩ 3 hp : ↥(Q2.reps ⟨139, by decide⟩)) : Coordinate 2)
        Q2.T147_139_2 = colFn colCertDiv_147_139_3.D2 (m := 1) from colCertDiv_147_139_3.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_139_3_match


theorem leaf_147_139_4 (hp : 4 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 4 (transLenTr ⟨139, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 4 (transLenTr ⟨139, by decide⟩ 4 hp)) T147_139
      hfix147_139 hinj147_139 hcardT147_139
      (fun i => conj_mem_of_fixedPoints _ _ (T147_139 i) (hfix147_139 i) _)
      ⟨147, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 4 hp) Q2.T147_139_2 Q2.hfix147_139_2 Q2.hinj147_139_2
      Q2.hcardT147_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_139_2 i) (Q2.hfix147_139_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨139, by decide⟩ 4 (transLenTr ⟨139, by decide⟩ 4 hp) : ↥(reps ⟨139, by decide⟩)) : Coordinate 1)
        T147_139 = colFn colCertDiv_147_139_4.D1 (m := 1) from colCertDiv_147_139_4.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨139, by decide⟩ 4 hp : ↥(Q2.reps ⟨139, by decide⟩)) : Coordinate 2)
        Q2.T147_139_2 = colFn colCertDiv_147_139_4.D2 (m := 1) from colCertDiv_147_139_4.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_139_4_match


theorem leaf_147_139_5 (hp : 5 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 5 (transLenTr ⟨139, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 5 (transLenTr ⟨139, by decide⟩ 5 hp)) T147_139
      hfix147_139 hinj147_139 hcardT147_139
      (fun i => conj_mem_of_fixedPoints _ _ (T147_139 i) (hfix147_139 i) _)
      ⟨147, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 5 hp) Q2.T147_139_2 Q2.hfix147_139_2 Q2.hinj147_139_2
      Q2.hcardT147_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_139_2 i) (Q2.hfix147_139_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨139, by decide⟩ 5 (transLenTr ⟨139, by decide⟩ 5 hp) : ↥(reps ⟨139, by decide⟩)) : Coordinate 1)
        T147_139 = colFn colCertDiv_147_139_5.D1 (m := 1) from colCertDiv_147_139_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨139, by decide⟩ 5 hp : ↥(Q2.reps ⟨139, by decide⟩)) : Coordinate 2)
        Q2.T147_139_2 = colFn colCertDiv_147_139_5.D2 (m := 1) from colCertDiv_147_139_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_139_5_match


theorem leaf_147_139_6 (hp : 6 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 6 (transLenTr ⟨139, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 6 (transLenTr ⟨139, by decide⟩ 6 hp)) T147_139
      hfix147_139 hinj147_139 hcardT147_139
      (fun i => conj_mem_of_fixedPoints _ _ (T147_139 i) (hfix147_139 i) _)
      ⟨147, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 6 hp) Q2.T147_139_2 Q2.hfix147_139_2 Q2.hinj147_139_2
      Q2.hcardT147_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_139_2 i) (Q2.hfix147_139_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨139, by decide⟩ 6 (transLenTr ⟨139, by decide⟩ 6 hp) : ↥(reps ⟨139, by decide⟩)) : Coordinate 1)
        T147_139 = colFn colCertDiv_147_139_6.D1 (m := 1) from colCertDiv_147_139_6.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨139, by decide⟩ 6 hp : ↥(Q2.reps ⟨139, by decide⟩)) : Coordinate 2)
        Q2.T147_139_2 = colFn colCertDiv_147_139_6.D2 (m := 1) from colCertDiv_147_139_6.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_139_6_match


theorem leaf_147_139_7 (hp : 7 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 7 (transLenTr ⟨139, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 7 (transLenTr ⟨139, by decide⟩ 7 hp)) T147_139
      hfix147_139 hinj147_139 hcardT147_139
      (fun i => conj_mem_of_fixedPoints _ _ (T147_139 i) (hfix147_139 i) _)
      ⟨147, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 7 hp) Q2.T147_139_2 Q2.hfix147_139_2 Q2.hinj147_139_2
      Q2.hcardT147_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_139_2 i) (Q2.hfix147_139_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨139, by decide⟩ 7 (transLenTr ⟨139, by decide⟩ 7 hp) : ↥(reps ⟨139, by decide⟩)) : Coordinate 1)
        T147_139 = colFn colCertDiv_147_139_7.D1 (m := 1) from colCertDiv_147_139_7.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨139, by decide⟩ 7 hp : ↥(Q2.reps ⟨139, by decide⟩)) : Coordinate 2)
        Q2.T147_139_2 = colFn colCertDiv_147_139_7.D2 (m := 1) from colCertDiv_147_139_7.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_139_7_match


theorem leaf_147_139_8 (hp : 8 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 8 (transLenTr ⟨139, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 8 (transLenTr ⟨139, by decide⟩ 8 hp)) T147_139
      hfix147_139 hinj147_139 hcardT147_139
      (fun i => conj_mem_of_fixedPoints _ _ (T147_139 i) (hfix147_139 i) _)
      ⟨147, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 8 hp) Q2.T147_139_2 Q2.hfix147_139_2 Q2.hinj147_139_2
      Q2.hcardT147_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_139_2 i) (Q2.hfix147_139_2 i) _)
      colCert_147_139_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_139_9 (hp : 9 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 9 (transLenTr ⟨139, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 9 (transLenTr ⟨139, by decide⟩ 9 hp)) T147_139
      hfix147_139 hinj147_139 hcardT147_139
      (fun i => conj_mem_of_fixedPoints _ _ (T147_139 i) (hfix147_139 i) _)
      ⟨147, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 9 hp) Q2.T147_139_2 Q2.hfix147_139_2 Q2.hinj147_139_2
      Q2.hcardT147_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_139_2 i) (Q2.hfix147_139_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨139, by decide⟩ 9 (transLenTr ⟨139, by decide⟩ 9 hp) : ↥(reps ⟨139, by decide⟩)) : Coordinate 1)
        T147_139 = colFn colCertDiv_147_139_9.D1 (m := 1) from colCertDiv_147_139_9.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨139, by decide⟩ 9 hp : ↥(Q2.reps ⟨139, by decide⟩)) : Coordinate 2)
        Q2.T147_139_2 = colFn colCertDiv_147_139_9.D2 (m := 1) from colCertDiv_147_139_9.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_139_9_match


theorem leaf_147_139_10 (hp : 10 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 10 (transLenTr ⟨139, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 10 (transLenTr ⟨139, by decide⟩ 10 hp)) T147_139
      hfix147_139 hinj147_139 hcardT147_139
      (fun i => conj_mem_of_fixedPoints _ _ (T147_139 i) (hfix147_139 i) _)
      ⟨147, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 10 hp) Q2.T147_139_2 Q2.hfix147_139_2 Q2.hinj147_139_2
      Q2.hcardT147_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_139_2 i) (Q2.hfix147_139_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨139, by decide⟩ 10 (transLenTr ⟨139, by decide⟩ 10 hp) : ↥(reps ⟨139, by decide⟩)) : Coordinate 1)
        T147_139 = colFn colCertDiv_147_139_10.D1 (m := 1) from colCertDiv_147_139_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨139, by decide⟩ 10 hp : ↥(Q2.reps ⟨139, by decide⟩)) : Coordinate 2)
        Q2.T147_139_2 = colFn colCertDiv_147_139_10.D2 (m := 1) from colCertDiv_147_139_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_139_10_match


theorem leaf_147_139_11 (hp : 11 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 11 (transLenTr ⟨139, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 11 (transLenTr ⟨139, by decide⟩ 11 hp)) T147_139
      hfix147_139 hinj147_139 hcardT147_139
      (fun i => conj_mem_of_fixedPoints _ _ (T147_139 i) (hfix147_139 i) _)
      ⟨147, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 11 hp) Q2.T147_139_2 Q2.hfix147_139_2 Q2.hinj147_139_2
      Q2.hcardT147_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_139_2 i) (Q2.hfix147_139_2 i) _)
      colCert_147_139_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_139_12 (hp : 12 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 12 (transLenTr ⟨139, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 12 (transLenTr ⟨139, by decide⟩ 12 hp)) T147_139
      hfix147_139 hinj147_139 hcardT147_139
      (fun i => conj_mem_of_fixedPoints _ _ (T147_139 i) (hfix147_139 i) _)
      ⟨147, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 12 hp) Q2.T147_139_2 Q2.hfix147_139_2 Q2.hinj147_139_2
      Q2.hcardT147_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_139_2 i) (Q2.hfix147_139_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨139, by decide⟩ 12 (transLenTr ⟨139, by decide⟩ 12 hp) : ↥(reps ⟨139, by decide⟩)) : Coordinate 1)
        T147_139 = colFn colCertDiv_147_139_12.D1 (m := 1) from colCertDiv_147_139_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨139, by decide⟩ 12 hp : ↥(Q2.reps ⟨139, by decide⟩)) : Coordinate 2)
        Q2.T147_139_2 = colFn colCertDiv_147_139_12.D2 (m := 1) from colCertDiv_147_139_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_139_12_match


theorem leaf_147_139_13 (hp : 13 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 13 (transLenTr ⟨139, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 13 (transLenTr ⟨139, by decide⟩ 13 hp)) T147_139
      hfix147_139 hinj147_139 hcardT147_139
      (fun i => conj_mem_of_fixedPoints _ _ (T147_139 i) (hfix147_139 i) _)
      ⟨147, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 13 hp) Q2.T147_139_2 Q2.hfix147_139_2 Q2.hinj147_139_2
      Q2.hcardT147_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_139_2 i) (Q2.hfix147_139_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨139, by decide⟩ 13 (transLenTr ⟨139, by decide⟩ 13 hp) : ↥(reps ⟨139, by decide⟩)) : Coordinate 1)
        T147_139 = colFn colCertDiv_147_139_13.D1 (m := 1) from colCertDiv_147_139_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨139, by decide⟩ 13 hp : ↥(Q2.reps ⟨139, by decide⟩)) : Coordinate 2)
        Q2.T147_139_2 = colFn colCertDiv_147_139_13.D2 (m := 1) from colCertDiv_147_139_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_139_13_match


theorem leaf_147_139_14 (hp : 14 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 14 (transLenTr ⟨139, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 14 (transLenTr ⟨139, by decide⟩ 14 hp)) T147_139
      hfix147_139 hinj147_139 hcardT147_139
      (fun i => conj_mem_of_fixedPoints _ _ (T147_139 i) (hfix147_139 i) _)
      ⟨147, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 14 hp) Q2.T147_139_2 Q2.hfix147_139_2 Q2.hinj147_139_2
      Q2.hcardT147_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_139_2 i) (Q2.hfix147_139_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨139, by decide⟩ 14 (transLenTr ⟨139, by decide⟩ 14 hp) : ↥(reps ⟨139, by decide⟩)) : Coordinate 1)
        T147_139 = colFn colCertDiv_147_139_14.D1 (m := 1) from colCertDiv_147_139_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨139, by decide⟩ 14 hp : ↥(Q2.reps ⟨139, by decide⟩)) : Coordinate 2)
        Q2.T147_139_2 = colFn colCertDiv_147_139_14.D2 (m := 1) from colCertDiv_147_139_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_139_14_match


theorem leaf_147_139_15 (hp : 15 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 15 (transLenTr ⟨139, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 15 (transLenTr ⟨139, by decide⟩ 15 hp)) T147_139
      hfix147_139 hinj147_139 hcardT147_139
      (fun i => conj_mem_of_fixedPoints _ _ (T147_139 i) (hfix147_139 i) _)
      ⟨147, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 15 hp) Q2.T147_139_2 Q2.hfix147_139_2 Q2.hinj147_139_2
      Q2.hcardT147_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_139_2 i) (Q2.hfix147_139_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨139, by decide⟩ 15 (transLenTr ⟨139, by decide⟩ 15 hp) : ↥(reps ⟨139, by decide⟩)) : Coordinate 1)
        T147_139 = colFn colCertDiv_147_139_15.D1 (m := 1) from colCertDiv_147_139_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨139, by decide⟩ 15 hp : ↥(Q2.reps ⟨139, by decide⟩)) : Coordinate 2)
        Q2.T147_139_2 = colFn colCertDiv_147_139_15.D2 (m := 1) from colCertDiv_147_139_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_139_15_match


theorem leaf_147_139_16 (hp : 16 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 16 (transLenTr ⟨139, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 16 (transLenTr ⟨139, by decide⟩ 16 hp)) T147_139
      hfix147_139 hinj147_139 hcardT147_139
      (fun i => conj_mem_of_fixedPoints _ _ (T147_139 i) (hfix147_139 i) _)
      ⟨147, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 16 hp) Q2.T147_139_2 Q2.hfix147_139_2 Q2.hinj147_139_2
      Q2.hcardT147_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_139_2 i) (Q2.hfix147_139_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨139, by decide⟩ 16 (transLenTr ⟨139, by decide⟩ 16 hp) : ↥(reps ⟨139, by decide⟩)) : Coordinate 1)
        T147_139 = colFn colCertDiv_147_139_16.D1 (m := 1) from colCertDiv_147_139_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨139, by decide⟩ 16 hp : ↥(Q2.reps ⟨139, by decide⟩)) : Coordinate 2)
        Q2.T147_139_2 = colFn colCertDiv_147_139_16.D2 (m := 1) from colCertDiv_147_139_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_139_16_match


theorem leaf_147_139_17 (hp : 17 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 17 (transLenTr ⟨139, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 17 (transLenTr ⟨139, by decide⟩ 17 hp)) T147_139
      hfix147_139 hinj147_139 hcardT147_139
      (fun i => conj_mem_of_fixedPoints _ _ (T147_139 i) (hfix147_139 i) _)
      ⟨147, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 17 hp) Q2.T147_139_2 Q2.hfix147_139_2 Q2.hinj147_139_2
      Q2.hcardT147_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_139_2 i) (Q2.hfix147_139_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨139, by decide⟩ 17 (transLenTr ⟨139, by decide⟩ 17 hp) : ↥(reps ⟨139, by decide⟩)) : Coordinate 1)
        T147_139 = colFn colCertDiv_147_139_17.D1 (m := 1) from colCertDiv_147_139_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨139, by decide⟩ 17 hp : ↥(Q2.reps ⟨139, by decide⟩)) : Coordinate 2)
        Q2.T147_139_2 = colFn colCertDiv_147_139_17.D2 (m := 1) from colCertDiv_147_139_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_139_17_match


theorem leaf_147_139_18 (hp : 18 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 18 (transLenTr ⟨139, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 18 (transLenTr ⟨139, by decide⟩ 18 hp)) T147_139
      hfix147_139 hinj147_139 hcardT147_139
      (fun i => conj_mem_of_fixedPoints _ _ (T147_139 i) (hfix147_139 i) _)
      ⟨147, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 18 hp) Q2.T147_139_2 Q2.hfix147_139_2 Q2.hinj147_139_2
      Q2.hcardT147_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_139_2 i) (Q2.hfix147_139_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨139, by decide⟩ 18 (transLenTr ⟨139, by decide⟩ 18 hp) : ↥(reps ⟨139, by decide⟩)) : Coordinate 1)
        T147_139 = colFn colCertDiv_147_139_18.D1 (m := 1) from colCertDiv_147_139_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨139, by decide⟩ 18 hp : ↥(Q2.reps ⟨139, by decide⟩)) : Coordinate 2)
        Q2.T147_139_2 = colFn colCertDiv_147_139_18.D2 (m := 1) from colCertDiv_147_139_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_139_18_match


theorem leaf_147_139_19 (hp : 19 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 19 (transLenTr ⟨139, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 19 (transLenTr ⟨139, by decide⟩ 19 hp)) T147_139
      hfix147_139 hinj147_139 hcardT147_139
      (fun i => conj_mem_of_fixedPoints _ _ (T147_139 i) (hfix147_139 i) _)
      ⟨147, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 19 hp) Q2.T147_139_2 Q2.hfix147_139_2 Q2.hinj147_139_2
      Q2.hcardT147_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_139_2 i) (Q2.hfix147_139_2 i) _)
      colCert_147_139_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_139_20 (hp : 20 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 20 (transLenTr ⟨139, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 20 (transLenTr ⟨139, by decide⟩ 20 hp)) T147_139
      hfix147_139 hinj147_139 hcardT147_139
      (fun i => conj_mem_of_fixedPoints _ _ (T147_139 i) (hfix147_139 i) _)
      ⟨147, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 20 hp) Q2.T147_139_2 Q2.hfix147_139_2 Q2.hinj147_139_2
      Q2.hcardT147_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_139_2 i) (Q2.hfix147_139_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨139, by decide⟩ 20 (transLenTr ⟨139, by decide⟩ 20 hp) : ↥(reps ⟨139, by decide⟩)) : Coordinate 1)
        T147_139 = colFn colCertDiv_147_139_20.D1 (m := 1) from colCertDiv_147_139_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨139, by decide⟩ 20 hp : ↥(Q2.reps ⟨139, by decide⟩)) : Coordinate 2)
        Q2.T147_139_2 = colFn colCertDiv_147_139_20.D2 (m := 1) from colCertDiv_147_139_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_139_20_match


theorem leaf_147_139_21 (hp : 21 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 21 (transLenTr ⟨139, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 21 (transLenTr ⟨139, by decide⟩ 21 hp)) T147_139
      hfix147_139 hinj147_139 hcardT147_139
      (fun i => conj_mem_of_fixedPoints _ _ (T147_139 i) (hfix147_139 i) _)
      ⟨147, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 21 hp) Q2.T147_139_2 Q2.hfix147_139_2 Q2.hinj147_139_2
      Q2.hcardT147_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_139_2 i) (Q2.hfix147_139_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨139, by decide⟩ 21 (transLenTr ⟨139, by decide⟩ 21 hp) : ↥(reps ⟨139, by decide⟩)) : Coordinate 1)
        T147_139 = colFn colCertDiv_147_139_21.D1 (m := 1) from colCertDiv_147_139_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨139, by decide⟩ 21 hp : ↥(Q2.reps ⟨139, by decide⟩)) : Coordinate 2)
        Q2.T147_139_2 = colFn colCertDiv_147_139_21.D2 (m := 1) from colCertDiv_147_139_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_139_21_match


theorem leaf_147_139_22 (hp : 22 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 22 (transLenTr ⟨139, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 22 (transLenTr ⟨139, by decide⟩ 22 hp)) T147_139
      hfix147_139 hinj147_139 hcardT147_139
      (fun i => conj_mem_of_fixedPoints _ _ (T147_139 i) (hfix147_139 i) _)
      ⟨147, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 22 hp) Q2.T147_139_2 Q2.hfix147_139_2 Q2.hinj147_139_2
      Q2.hcardT147_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_139_2 i) (Q2.hfix147_139_2 i) _)
      colCert_147_139_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_139_23 (hp : 23 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 23 (transLenTr ⟨139, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 23 (transLenTr ⟨139, by decide⟩ 23 hp)) T147_139
      hfix147_139 hinj147_139 hcardT147_139
      (fun i => conj_mem_of_fixedPoints _ _ (T147_139 i) (hfix147_139 i) _)
      ⟨147, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 23 hp) Q2.T147_139_2 Q2.hfix147_139_2 Q2.hinj147_139_2
      Q2.hcardT147_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_139_2 i) (Q2.hfix147_139_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨139, by decide⟩ 23 (transLenTr ⟨139, by decide⟩ 23 hp) : ↥(reps ⟨139, by decide⟩)) : Coordinate 1)
        T147_139 = colFn colCertDiv_147_139_23.D1 (m := 1) from colCertDiv_147_139_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨139, by decide⟩ 23 hp : ↥(Q2.reps ⟨139, by decide⟩)) : Coordinate 2)
        Q2.T147_139_2 = colFn colCertDiv_147_139_23.D2 (m := 1) from colCertDiv_147_139_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_139_23_match


theorem leaf_147_139_24 (hp : 24 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 24 (transLenTr ⟨139, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 24 (transLenTr ⟨139, by decide⟩ 24 hp)) T147_139
      hfix147_139 hinj147_139 hcardT147_139
      (fun i => conj_mem_of_fixedPoints _ _ (T147_139 i) (hfix147_139 i) _)
      ⟨147, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 24 hp) Q2.T147_139_2 Q2.hfix147_139_2 Q2.hinj147_139_2
      Q2.hcardT147_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_139_2 i) (Q2.hfix147_139_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨139, by decide⟩ 24 (transLenTr ⟨139, by decide⟩ 24 hp) : ↥(reps ⟨139, by decide⟩)) : Coordinate 1)
        T147_139 = colFn colCertDiv_147_139_24.D1 (m := 1) from colCertDiv_147_139_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨139, by decide⟩ 24 hp : ↥(Q2.reps ⟨139, by decide⟩)) : Coordinate 2)
        Q2.T147_139_2 = colFn colCertDiv_147_139_24.D2 (m := 1) from colCertDiv_147_139_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_139_24_match


theorem leaf_147_140_0 (hp : 0 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 0 (transLenTr ⟨140, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 0 (transLenTr ⟨140, by decide⟩ 0 hp)) T147_140
      hfix147_140 hinj147_140 hcardT147_140
      (fun i => conj_mem_of_fixedPoints _ _ (T147_140 i) (hfix147_140 i) _)
      ⟨147, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 0 hp) Q2.T147_140_2 Q2.hfix147_140_2 Q2.hinj147_140_2
      Q2.hcardT147_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_140_2 i) (Q2.hfix147_140_2 i) _)
      colCert_147_140_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_140_1 (hp : 1 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 1 (transLenTr ⟨140, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 1 (transLenTr ⟨140, by decide⟩ 1 hp)) T147_140
      hfix147_140 hinj147_140 hcardT147_140
      (fun i => conj_mem_of_fixedPoints _ _ (T147_140 i) (hfix147_140 i) _)
      ⟨147, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 1 hp) Q2.T147_140_2 Q2.hfix147_140_2 Q2.hinj147_140_2
      Q2.hcardT147_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_140_2 i) (Q2.hfix147_140_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨140, by decide⟩ 1 (transLenTr ⟨140, by decide⟩ 1 hp) : ↥(reps ⟨140, by decide⟩)) : Coordinate 1)
        T147_140 = colFn colCertDiv_147_140_1.D1 (m := 1) from colCertDiv_147_140_1.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨140, by decide⟩ 1 hp : ↥(Q2.reps ⟨140, by decide⟩)) : Coordinate 2)
        Q2.T147_140_2 = colFn colCertDiv_147_140_1.D2 (m := 1) from colCertDiv_147_140_1.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_140_1_match


theorem leaf_147_140_2 (hp : 2 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 2 (transLenTr ⟨140, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 2 (transLenTr ⟨140, by decide⟩ 2 hp)) T147_140
      hfix147_140 hinj147_140 hcardT147_140
      (fun i => conj_mem_of_fixedPoints _ _ (T147_140 i) (hfix147_140 i) _)
      ⟨147, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 2 hp) Q2.T147_140_2 Q2.hfix147_140_2 Q2.hinj147_140_2
      Q2.hcardT147_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_140_2 i) (Q2.hfix147_140_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨140, by decide⟩ 2 (transLenTr ⟨140, by decide⟩ 2 hp) : ↥(reps ⟨140, by decide⟩)) : Coordinate 1)
        T147_140 = colFn colCertDiv_147_140_2.D1 (m := 1) from colCertDiv_147_140_2.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨140, by decide⟩ 2 hp : ↥(Q2.reps ⟨140, by decide⟩)) : Coordinate 2)
        Q2.T147_140_2 = colFn colCertDiv_147_140_2.D2 (m := 1) from colCertDiv_147_140_2.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_140_2_match


theorem leaf_147_140_3 (hp : 3 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 3 (transLenTr ⟨140, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 3 (transLenTr ⟨140, by decide⟩ 3 hp)) T147_140
      hfix147_140 hinj147_140 hcardT147_140
      (fun i => conj_mem_of_fixedPoints _ _ (T147_140 i) (hfix147_140 i) _)
      ⟨147, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 3 hp) Q2.T147_140_2 Q2.hfix147_140_2 Q2.hinj147_140_2
      Q2.hcardT147_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_140_2 i) (Q2.hfix147_140_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨140, by decide⟩ 3 (transLenTr ⟨140, by decide⟩ 3 hp) : ↥(reps ⟨140, by decide⟩)) : Coordinate 1)
        T147_140 = colFn colCertDiv_147_140_3.D1 (m := 1) from colCertDiv_147_140_3.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨140, by decide⟩ 3 hp : ↥(Q2.reps ⟨140, by decide⟩)) : Coordinate 2)
        Q2.T147_140_2 = colFn colCertDiv_147_140_3.D2 (m := 1) from colCertDiv_147_140_3.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_140_3_match


theorem leaf_147_140_4 (hp : 4 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 4 (transLenTr ⟨140, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 4 (transLenTr ⟨140, by decide⟩ 4 hp)) T147_140
      hfix147_140 hinj147_140 hcardT147_140
      (fun i => conj_mem_of_fixedPoints _ _ (T147_140 i) (hfix147_140 i) _)
      ⟨147, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 4 hp) Q2.T147_140_2 Q2.hfix147_140_2 Q2.hinj147_140_2
      Q2.hcardT147_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_140_2 i) (Q2.hfix147_140_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨140, by decide⟩ 4 (transLenTr ⟨140, by decide⟩ 4 hp) : ↥(reps ⟨140, by decide⟩)) : Coordinate 1)
        T147_140 = colFn colCertDiv_147_140_4.D1 (m := 1) from colCertDiv_147_140_4.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨140, by decide⟩ 4 hp : ↥(Q2.reps ⟨140, by decide⟩)) : Coordinate 2)
        Q2.T147_140_2 = colFn colCertDiv_147_140_4.D2 (m := 1) from colCertDiv_147_140_4.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_140_4_match


theorem leaf_147_140_5 (hp : 5 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 5 (transLenTr ⟨140, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 5 (transLenTr ⟨140, by decide⟩ 5 hp)) T147_140
      hfix147_140 hinj147_140 hcardT147_140
      (fun i => conj_mem_of_fixedPoints _ _ (T147_140 i) (hfix147_140 i) _)
      ⟨147, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 5 hp) Q2.T147_140_2 Q2.hfix147_140_2 Q2.hinj147_140_2
      Q2.hcardT147_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_140_2 i) (Q2.hfix147_140_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨140, by decide⟩ 5 (transLenTr ⟨140, by decide⟩ 5 hp) : ↥(reps ⟨140, by decide⟩)) : Coordinate 1)
        T147_140 = colFn colCertDiv_147_140_5.D1 (m := 1) from colCertDiv_147_140_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨140, by decide⟩ 5 hp : ↥(Q2.reps ⟨140, by decide⟩)) : Coordinate 2)
        Q2.T147_140_2 = colFn colCertDiv_147_140_5.D2 (m := 1) from colCertDiv_147_140_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_140_5_match


theorem leaf_147_140_6 (hp : 6 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 6 (transLenTr ⟨140, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 6 (transLenTr ⟨140, by decide⟩ 6 hp)) T147_140
      hfix147_140 hinj147_140 hcardT147_140
      (fun i => conj_mem_of_fixedPoints _ _ (T147_140 i) (hfix147_140 i) _)
      ⟨147, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 6 hp) Q2.T147_140_2 Q2.hfix147_140_2 Q2.hinj147_140_2
      Q2.hcardT147_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_140_2 i) (Q2.hfix147_140_2 i) _)
      colCert_147_140_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_140_7 (hp : 7 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 7 (transLenTr ⟨140, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 7 (transLenTr ⟨140, by decide⟩ 7 hp)) T147_140
      hfix147_140 hinj147_140 hcardT147_140
      (fun i => conj_mem_of_fixedPoints _ _ (T147_140 i) (hfix147_140 i) _)
      ⟨147, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 7 hp) Q2.T147_140_2 Q2.hfix147_140_2 Q2.hinj147_140_2
      Q2.hcardT147_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_140_2 i) (Q2.hfix147_140_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨140, by decide⟩ 7 (transLenTr ⟨140, by decide⟩ 7 hp) : ↥(reps ⟨140, by decide⟩)) : Coordinate 1)
        T147_140 = colFn colCertDiv_147_140_7.D1 (m := 1) from colCertDiv_147_140_7.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨140, by decide⟩ 7 hp : ↥(Q2.reps ⟨140, by decide⟩)) : Coordinate 2)
        Q2.T147_140_2 = colFn colCertDiv_147_140_7.D2 (m := 1) from colCertDiv_147_140_7.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_140_7_match


theorem leaf_147_140_8 (hp : 8 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 8 (transLenTr ⟨140, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 8 (transLenTr ⟨140, by decide⟩ 8 hp)) T147_140
      hfix147_140 hinj147_140 hcardT147_140
      (fun i => conj_mem_of_fixedPoints _ _ (T147_140 i) (hfix147_140 i) _)
      ⟨147, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 8 hp) Q2.T147_140_2 Q2.hfix147_140_2 Q2.hinj147_140_2
      Q2.hcardT147_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_140_2 i) (Q2.hfix147_140_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨140, by decide⟩ 8 (transLenTr ⟨140, by decide⟩ 8 hp) : ↥(reps ⟨140, by decide⟩)) : Coordinate 1)
        T147_140 = colFn colCertDiv_147_140_8.D1 (m := 1) from colCertDiv_147_140_8.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨140, by decide⟩ 8 hp : ↥(Q2.reps ⟨140, by decide⟩)) : Coordinate 2)
        Q2.T147_140_2 = colFn colCertDiv_147_140_8.D2 (m := 1) from colCertDiv_147_140_8.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_140_8_match


theorem leaf_147_140_9 (hp : 9 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 9 (transLenTr ⟨140, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 9 (transLenTr ⟨140, by decide⟩ 9 hp)) T147_140
      hfix147_140 hinj147_140 hcardT147_140
      (fun i => conj_mem_of_fixedPoints _ _ (T147_140 i) (hfix147_140 i) _)
      ⟨147, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 9 hp) Q2.T147_140_2 Q2.hfix147_140_2 Q2.hinj147_140_2
      Q2.hcardT147_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_140_2 i) (Q2.hfix147_140_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨140, by decide⟩ 9 (transLenTr ⟨140, by decide⟩ 9 hp) : ↥(reps ⟨140, by decide⟩)) : Coordinate 1)
        T147_140 = colFn colCertDiv_147_140_9.D1 (m := 1) from colCertDiv_147_140_9.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨140, by decide⟩ 9 hp : ↥(Q2.reps ⟨140, by decide⟩)) : Coordinate 2)
        Q2.T147_140_2 = colFn colCertDiv_147_140_9.D2 (m := 1) from colCertDiv_147_140_9.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_140_9_match


theorem leaf_147_140_10 (hp : 10 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 10 (transLenTr ⟨140, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 10 (transLenTr ⟨140, by decide⟩ 10 hp)) T147_140
      hfix147_140 hinj147_140 hcardT147_140
      (fun i => conj_mem_of_fixedPoints _ _ (T147_140 i) (hfix147_140 i) _)
      ⟨147, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 10 hp) Q2.T147_140_2 Q2.hfix147_140_2 Q2.hinj147_140_2
      Q2.hcardT147_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_140_2 i) (Q2.hfix147_140_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨140, by decide⟩ 10 (transLenTr ⟨140, by decide⟩ 10 hp) : ↥(reps ⟨140, by decide⟩)) : Coordinate 1)
        T147_140 = colFn colCertDiv_147_140_10.D1 (m := 1) from colCertDiv_147_140_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨140, by decide⟩ 10 hp : ↥(Q2.reps ⟨140, by decide⟩)) : Coordinate 2)
        Q2.T147_140_2 = colFn colCertDiv_147_140_10.D2 (m := 1) from colCertDiv_147_140_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_140_10_match


theorem leaf_147_140_11 (hp : 11 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 11 (transLenTr ⟨140, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 11 (transLenTr ⟨140, by decide⟩ 11 hp)) T147_140
      hfix147_140 hinj147_140 hcardT147_140
      (fun i => conj_mem_of_fixedPoints _ _ (T147_140 i) (hfix147_140 i) _)
      ⟨147, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 11 hp) Q2.T147_140_2 Q2.hfix147_140_2 Q2.hinj147_140_2
      Q2.hcardT147_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_140_2 i) (Q2.hfix147_140_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨140, by decide⟩ 11 (transLenTr ⟨140, by decide⟩ 11 hp) : ↥(reps ⟨140, by decide⟩)) : Coordinate 1)
        T147_140 = colFn colCertDiv_147_140_11.D1 (m := 1) from colCertDiv_147_140_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨140, by decide⟩ 11 hp : ↥(Q2.reps ⟨140, by decide⟩)) : Coordinate 2)
        Q2.T147_140_2 = colFn colCertDiv_147_140_11.D2 (m := 1) from colCertDiv_147_140_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_140_11_match


theorem leaf_147_140_12 (hp : 12 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 12 (transLenTr ⟨140, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 12 (transLenTr ⟨140, by decide⟩ 12 hp)) T147_140
      hfix147_140 hinj147_140 hcardT147_140
      (fun i => conj_mem_of_fixedPoints _ _ (T147_140 i) (hfix147_140 i) _)
      ⟨147, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 12 hp) Q2.T147_140_2 Q2.hfix147_140_2 Q2.hinj147_140_2
      Q2.hcardT147_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_140_2 i) (Q2.hfix147_140_2 i) _)
      colCert_147_140_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_140_13 (hp : 13 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 13 (transLenTr ⟨140, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 13 (transLenTr ⟨140, by decide⟩ 13 hp)) T147_140
      hfix147_140 hinj147_140 hcardT147_140
      (fun i => conj_mem_of_fixedPoints _ _ (T147_140 i) (hfix147_140 i) _)
      ⟨147, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 13 hp) Q2.T147_140_2 Q2.hfix147_140_2 Q2.hinj147_140_2
      Q2.hcardT147_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_140_2 i) (Q2.hfix147_140_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨140, by decide⟩ 13 (transLenTr ⟨140, by decide⟩ 13 hp) : ↥(reps ⟨140, by decide⟩)) : Coordinate 1)
        T147_140 = colFn colCertDiv_147_140_13.D1 (m := 1) from colCertDiv_147_140_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨140, by decide⟩ 13 hp : ↥(Q2.reps ⟨140, by decide⟩)) : Coordinate 2)
        Q2.T147_140_2 = colFn colCertDiv_147_140_13.D2 (m := 1) from colCertDiv_147_140_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_140_13_match


theorem leaf_147_140_14 (hp : 14 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 14 (transLenTr ⟨140, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 14 (transLenTr ⟨140, by decide⟩ 14 hp)) T147_140
      hfix147_140 hinj147_140 hcardT147_140
      (fun i => conj_mem_of_fixedPoints _ _ (T147_140 i) (hfix147_140 i) _)
      ⟨147, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 14 hp) Q2.T147_140_2 Q2.hfix147_140_2 Q2.hinj147_140_2
      Q2.hcardT147_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_140_2 i) (Q2.hfix147_140_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨140, by decide⟩ 14 (transLenTr ⟨140, by decide⟩ 14 hp) : ↥(reps ⟨140, by decide⟩)) : Coordinate 1)
        T147_140 = colFn colCertDiv_147_140_14.D1 (m := 1) from colCertDiv_147_140_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨140, by decide⟩ 14 hp : ↥(Q2.reps ⟨140, by decide⟩)) : Coordinate 2)
        Q2.T147_140_2 = colFn colCertDiv_147_140_14.D2 (m := 1) from colCertDiv_147_140_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_140_14_match


theorem leaf_147_140_15 (hp : 15 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 15 (transLenTr ⟨140, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 15 (transLenTr ⟨140, by decide⟩ 15 hp)) T147_140
      hfix147_140 hinj147_140 hcardT147_140
      (fun i => conj_mem_of_fixedPoints _ _ (T147_140 i) (hfix147_140 i) _)
      ⟨147, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 15 hp) Q2.T147_140_2 Q2.hfix147_140_2 Q2.hinj147_140_2
      Q2.hcardT147_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_140_2 i) (Q2.hfix147_140_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨140, by decide⟩ 15 (transLenTr ⟨140, by decide⟩ 15 hp) : ↥(reps ⟨140, by decide⟩)) : Coordinate 1)
        T147_140 = colFn colCertDiv_147_140_15.D1 (m := 1) from colCertDiv_147_140_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨140, by decide⟩ 15 hp : ↥(Q2.reps ⟨140, by decide⟩)) : Coordinate 2)
        Q2.T147_140_2 = colFn colCertDiv_147_140_15.D2 (m := 1) from colCertDiv_147_140_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_140_15_match


theorem leaf_147_140_16 (hp : 16 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 16 (transLenTr ⟨140, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 16 (transLenTr ⟨140, by decide⟩ 16 hp)) T147_140
      hfix147_140 hinj147_140 hcardT147_140
      (fun i => conj_mem_of_fixedPoints _ _ (T147_140 i) (hfix147_140 i) _)
      ⟨147, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 16 hp) Q2.T147_140_2 Q2.hfix147_140_2 Q2.hinj147_140_2
      Q2.hcardT147_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_140_2 i) (Q2.hfix147_140_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨140, by decide⟩ 16 (transLenTr ⟨140, by decide⟩ 16 hp) : ↥(reps ⟨140, by decide⟩)) : Coordinate 1)
        T147_140 = colFn colCertDiv_147_140_16.D1 (m := 1) from colCertDiv_147_140_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨140, by decide⟩ 16 hp : ↥(Q2.reps ⟨140, by decide⟩)) : Coordinate 2)
        Q2.T147_140_2 = colFn colCertDiv_147_140_16.D2 (m := 1) from colCertDiv_147_140_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_140_16_match


theorem leaf_147_140_17 (hp : 17 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 17 (transLenTr ⟨140, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 17 (transLenTr ⟨140, by decide⟩ 17 hp)) T147_140
      hfix147_140 hinj147_140 hcardT147_140
      (fun i => conj_mem_of_fixedPoints _ _ (T147_140 i) (hfix147_140 i) _)
      ⟨147, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 17 hp) Q2.T147_140_2 Q2.hfix147_140_2 Q2.hinj147_140_2
      Q2.hcardT147_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_140_2 i) (Q2.hfix147_140_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨140, by decide⟩ 17 (transLenTr ⟨140, by decide⟩ 17 hp) : ↥(reps ⟨140, by decide⟩)) : Coordinate 1)
        T147_140 = colFn colCertDiv_147_140_17.D1 (m := 1) from colCertDiv_147_140_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨140, by decide⟩ 17 hp : ↥(Q2.reps ⟨140, by decide⟩)) : Coordinate 2)
        Q2.T147_140_2 = colFn colCertDiv_147_140_17.D2 (m := 1) from colCertDiv_147_140_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_140_17_match


theorem leaf_147_140_18 (hp : 18 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 18 (transLenTr ⟨140, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 18 (transLenTr ⟨140, by decide⟩ 18 hp)) T147_140
      hfix147_140 hinj147_140 hcardT147_140
      (fun i => conj_mem_of_fixedPoints _ _ (T147_140 i) (hfix147_140 i) _)
      ⟨147, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 18 hp) Q2.T147_140_2 Q2.hfix147_140_2 Q2.hinj147_140_2
      Q2.hcardT147_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_140_2 i) (Q2.hfix147_140_2 i) _)
      colCert_147_140_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_140_19 (hp : 19 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 19 (transLenTr ⟨140, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 19 (transLenTr ⟨140, by decide⟩ 19 hp)) T147_140
      hfix147_140 hinj147_140 hcardT147_140
      (fun i => conj_mem_of_fixedPoints _ _ (T147_140 i) (hfix147_140 i) _)
      ⟨147, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 19 hp) Q2.T147_140_2 Q2.hfix147_140_2 Q2.hinj147_140_2
      Q2.hcardT147_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_140_2 i) (Q2.hfix147_140_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨140, by decide⟩ 19 (transLenTr ⟨140, by decide⟩ 19 hp) : ↥(reps ⟨140, by decide⟩)) : Coordinate 1)
        T147_140 = colFn colCertDiv_147_140_19.D1 (m := 1) from colCertDiv_147_140_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨140, by decide⟩ 19 hp : ↥(Q2.reps ⟨140, by decide⟩)) : Coordinate 2)
        Q2.T147_140_2 = colFn colCertDiv_147_140_19.D2 (m := 1) from colCertDiv_147_140_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_140_19_match


theorem leaf_147_140_20 (hp : 20 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 20 (transLenTr ⟨140, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 20 (transLenTr ⟨140, by decide⟩ 20 hp)) T147_140
      hfix147_140 hinj147_140 hcardT147_140
      (fun i => conj_mem_of_fixedPoints _ _ (T147_140 i) (hfix147_140 i) _)
      ⟨147, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 20 hp) Q2.T147_140_2 Q2.hfix147_140_2 Q2.hinj147_140_2
      Q2.hcardT147_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_140_2 i) (Q2.hfix147_140_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨140, by decide⟩ 20 (transLenTr ⟨140, by decide⟩ 20 hp) : ↥(reps ⟨140, by decide⟩)) : Coordinate 1)
        T147_140 = colFn colCertDiv_147_140_20.D1 (m := 1) from colCertDiv_147_140_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨140, by decide⟩ 20 hp : ↥(Q2.reps ⟨140, by decide⟩)) : Coordinate 2)
        Q2.T147_140_2 = colFn colCertDiv_147_140_20.D2 (m := 1) from colCertDiv_147_140_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_140_20_match


theorem leaf_147_140_21 (hp : 21 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 21 (transLenTr ⟨140, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 21 (transLenTr ⟨140, by decide⟩ 21 hp)) T147_140
      hfix147_140 hinj147_140 hcardT147_140
      (fun i => conj_mem_of_fixedPoints _ _ (T147_140 i) (hfix147_140 i) _)
      ⟨147, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 21 hp) Q2.T147_140_2 Q2.hfix147_140_2 Q2.hinj147_140_2
      Q2.hcardT147_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_140_2 i) (Q2.hfix147_140_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨140, by decide⟩ 21 (transLenTr ⟨140, by decide⟩ 21 hp) : ↥(reps ⟨140, by decide⟩)) : Coordinate 1)
        T147_140 = colFn colCertDiv_147_140_21.D1 (m := 1) from colCertDiv_147_140_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨140, by decide⟩ 21 hp : ↥(Q2.reps ⟨140, by decide⟩)) : Coordinate 2)
        Q2.T147_140_2 = colFn colCertDiv_147_140_21.D2 (m := 1) from colCertDiv_147_140_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_140_21_match


theorem leaf_147_140_22 (hp : 22 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 22 (transLenTr ⟨140, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 22 (transLenTr ⟨140, by decide⟩ 22 hp)) T147_140
      hfix147_140 hinj147_140 hcardT147_140
      (fun i => conj_mem_of_fixedPoints _ _ (T147_140 i) (hfix147_140 i) _)
      ⟨147, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 22 hp) Q2.T147_140_2 Q2.hfix147_140_2 Q2.hinj147_140_2
      Q2.hcardT147_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_140_2 i) (Q2.hfix147_140_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨140, by decide⟩ 22 (transLenTr ⟨140, by decide⟩ 22 hp) : ↥(reps ⟨140, by decide⟩)) : Coordinate 1)
        T147_140 = colFn colCertDiv_147_140_22.D1 (m := 1) from colCertDiv_147_140_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨140, by decide⟩ 22 hp : ↥(Q2.reps ⟨140, by decide⟩)) : Coordinate 2)
        Q2.T147_140_2 = colFn colCertDiv_147_140_22.D2 (m := 1) from colCertDiv_147_140_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_140_22_match


theorem leaf_147_140_23 (hp : 23 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 23 (transLenTr ⟨140, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 23 (transLenTr ⟨140, by decide⟩ 23 hp)) T147_140
      hfix147_140 hinj147_140 hcardT147_140
      (fun i => conj_mem_of_fixedPoints _ _ (T147_140 i) (hfix147_140 i) _)
      ⟨147, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 23 hp) Q2.T147_140_2 Q2.hfix147_140_2 Q2.hinj147_140_2
      Q2.hcardT147_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_140_2 i) (Q2.hfix147_140_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨140, by decide⟩ 23 (transLenTr ⟨140, by decide⟩ 23 hp) : ↥(reps ⟨140, by decide⟩)) : Coordinate 1)
        T147_140 = colFn colCertDiv_147_140_23.D1 (m := 1) from colCertDiv_147_140_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨140, by decide⟩ 23 hp : ↥(Q2.reps ⟨140, by decide⟩)) : Coordinate 2)
        Q2.T147_140_2 = colFn colCertDiv_147_140_23.D2 (m := 1) from colCertDiv_147_140_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_140_23_match


theorem leaf_147_140_24 (hp : 24 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 24 (transLenTr ⟨140, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 24 (transLenTr ⟨140, by decide⟩ 24 hp)) T147_140
      hfix147_140 hinj147_140 hcardT147_140
      (fun i => conj_mem_of_fixedPoints _ _ (T147_140 i) (hfix147_140 i) _)
      ⟨147, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 24 hp) Q2.T147_140_2 Q2.hfix147_140_2 Q2.hinj147_140_2
      Q2.hcardT147_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_140_2 i) (Q2.hfix147_140_2 i) _)
      colCert_147_140_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_0 (hp : 0 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 0 (transLenTr ⟨141, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 0 (transLenTr ⟨141, by decide⟩ 0 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 0 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_1 (hp : 1 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 1 (transLenTr ⟨141, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 1 (transLenTr ⟨141, by decide⟩ 1 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 1 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_2 (hp : 2 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 2 (transLenTr ⟨141, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 2 (transLenTr ⟨141, by decide⟩ 2 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 2 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_3 (hp : 3 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 3 (transLenTr ⟨141, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 3 (transLenTr ⟨141, by decide⟩ 3 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 3 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_4 (hp : 4 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 4 (transLenTr ⟨141, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 4 (transLenTr ⟨141, by decide⟩ 4 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 4 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_5 (hp : 5 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 5 (transLenTr ⟨141, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 5 (transLenTr ⟨141, by decide⟩ 5 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 5 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_6 (hp : 6 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 6 (transLenTr ⟨141, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 6 (transLenTr ⟨141, by decide⟩ 6 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 6 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_7 (hp : 7 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 7 (transLenTr ⟨141, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 7 (transLenTr ⟨141, by decide⟩ 7 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 7 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_8 (hp : 8 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 8 (transLenTr ⟨141, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 8 (transLenTr ⟨141, by decide⟩ 8 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 8 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_9 (hp : 9 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 9 (transLenTr ⟨141, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 9 (transLenTr ⟨141, by decide⟩ 9 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 9 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_10 (hp : 10 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 10 (transLenTr ⟨141, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 10 (transLenTr ⟨141, by decide⟩ 10 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 10 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_11 (hp : 11 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 11 (transLenTr ⟨141, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 11 (transLenTr ⟨141, by decide⟩ 11 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 11 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_12 (hp : 12 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 12 (transLenTr ⟨141, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 12 (transLenTr ⟨141, by decide⟩ 12 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 12 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_13 (hp : 13 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 13 (transLenTr ⟨141, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 13 (transLenTr ⟨141, by decide⟩ 13 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 13 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_14 (hp : 14 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 14 (transLenTr ⟨141, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 14 (transLenTr ⟨141, by decide⟩ 14 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 14 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_15 (hp : 15 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 15 (transLenTr ⟨141, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 15 (transLenTr ⟨141, by decide⟩ 15 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 15 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_16 (hp : 16 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 16 (transLenTr ⟨141, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 16 (transLenTr ⟨141, by decide⟩ 16 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 16 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_17 (hp : 17 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 17 (transLenTr ⟨141, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 17 (transLenTr ⟨141, by decide⟩ 17 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 17 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_18 (hp : 18 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 18 (transLenTr ⟨141, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 18 (transLenTr ⟨141, by decide⟩ 18 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 18 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_19 (hp : 19 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 19 (transLenTr ⟨141, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 19 (transLenTr ⟨141, by decide⟩ 19 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 19 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_20 (hp : 20 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 20 (transLenTr ⟨141, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 20 (transLenTr ⟨141, by decide⟩ 20 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 20 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_21 (hp : 21 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 21 (transLenTr ⟨141, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 21 (transLenTr ⟨141, by decide⟩ 21 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 21 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_22 (hp : 22 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 22 (transLenTr ⟨141, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 22 (transLenTr ⟨141, by decide⟩ 22 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 22 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_23 (hp : 23 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 23 (transLenTr ⟨141, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 23 (transLenTr ⟨141, by decide⟩ 23 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 23 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_24 (hp : 24 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 24 (transLenTr ⟨141, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 24 (transLenTr ⟨141, by decide⟩ 24 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 24 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_25 (hp : 25 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 25 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 25 (transLenTr ⟨141, by decide⟩ 25 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 25 (transLenTr ⟨141, by decide⟩ 25 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 25 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_25.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_30 (hp : 30 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 30 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 30 (transLenTr ⟨141, by decide⟩ 30 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 30 (transLenTr ⟨141, by decide⟩ 30 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 30 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_30.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_35 (hp : 35 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 35 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 35 (transLenTr ⟨141, by decide⟩ 35 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 35 (transLenTr ⟨141, by decide⟩ 35 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 35 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_35.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_40 (hp : 40 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 40 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 40 (transLenTr ⟨141, by decide⟩ 40 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 40 (transLenTr ⟨141, by decide⟩ 40 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 40 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_40.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_45 (hp : 45 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 45 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 45 (transLenTr ⟨141, by decide⟩ 45 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 45 (transLenTr ⟨141, by decide⟩ 45 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 45 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_45.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_50 (hp : 50 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 50 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 50 (transLenTr ⟨141, by decide⟩ 50 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 50 (transLenTr ⟨141, by decide⟩ 50 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 50 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_50.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_55 (hp : 55 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 55 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 55 (transLenTr ⟨141, by decide⟩ 55 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 55 (transLenTr ⟨141, by decide⟩ 55 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 55 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_55.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_60 (hp : 60 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 60 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 60 (transLenTr ⟨141, by decide⟩ 60 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 60 (transLenTr ⟨141, by decide⟩ 60 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 60 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_60.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_65 (hp : 65 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 65 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 65 (transLenTr ⟨141, by decide⟩ 65 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 65 (transLenTr ⟨141, by decide⟩ 65 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 65 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_65.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_70 (hp : 70 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 70 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 70 (transLenTr ⟨141, by decide⟩ 70 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 70 (transLenTr ⟨141, by decide⟩ 70 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 70 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_70.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_75 (hp : 75 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 75 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 75 (transLenTr ⟨141, by decide⟩ 75 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 75 (transLenTr ⟨141, by decide⟩ 75 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 75 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_75.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_80 (hp : 80 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 80 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 80 (transLenTr ⟨141, by decide⟩ 80 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 80 (transLenTr ⟨141, by decide⟩ 80 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 80 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_80.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_85 (hp : 85 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 85 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 85 (transLenTr ⟨141, by decide⟩ 85 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 85 (transLenTr ⟨141, by decide⟩ 85 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 85 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_85.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_90 (hp : 90 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 90 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 90 (transLenTr ⟨141, by decide⟩ 90 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 90 (transLenTr ⟨141, by decide⟩ 90 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 90 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_90.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_95 (hp : 95 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 95 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 95 (transLenTr ⟨141, by decide⟩ 95 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 95 (transLenTr ⟨141, by decide⟩ 95 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 95 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_95.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_100 (hp : 100 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 100 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 100 (transLenTr ⟨141, by decide⟩ 100 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 100 (transLenTr ⟨141, by decide⟩ 100 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 100 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_100.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_105 (hp : 105 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 105 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 105 (transLenTr ⟨141, by decide⟩ 105 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 105 (transLenTr ⟨141, by decide⟩ 105 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 105 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_105.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_110 (hp : 110 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 110 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 110 (transLenTr ⟨141, by decide⟩ 110 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 110 (transLenTr ⟨141, by decide⟩ 110 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 110 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_110.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_115 (hp : 115 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 115 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 115 (transLenTr ⟨141, by decide⟩ 115 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 115 (transLenTr ⟨141, by decide⟩ 115 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 115 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_115.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_141_120 (hp : 120 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 120 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 120 (transLenTr ⟨141, by decide⟩ 120 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 120 (transLenTr ⟨141, by decide⟩ 120 hp)) T147_141
      hfix147_141 hinj147_141 hcardT147_141
      (fun i => conj_mem_of_fixedPoints _ _ (T147_141 i) (hfix147_141 i) _)
      ⟨147, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 120 hp) Q2.T147_141_2 Q2.hfix147_141_2 Q2.hinj147_141_2
      Q2.hcardT147_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_141_2 i) (Q2.hfix147_141_2 i) _)
      colCert_147_141_120.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_142_0 (hp : 0 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 0 (transLenTr ⟨142, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 0 (transLenTr ⟨142, by decide⟩ 0 hp)) T147_142
      hfix147_142 hinj147_142 hcardT147_142
      (fun i => conj_mem_of_fixedPoints _ _ (T147_142 i) (hfix147_142 i) _)
      ⟨147, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 0 hp) Q2.T147_142_2 Q2.hfix147_142_2 Q2.hinj147_142_2
      Q2.hcardT147_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_142_2 i) (Q2.hfix147_142_2 i) _)
      colCert_147_142_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_142_1 (hp : 1 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 1 (transLenTr ⟨142, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 1 (transLenTr ⟨142, by decide⟩ 1 hp)) T147_142
      hfix147_142 hinj147_142 hcardT147_142
      (fun i => conj_mem_of_fixedPoints _ _ (T147_142 i) (hfix147_142 i) _)
      ⟨147, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 1 hp) Q2.T147_142_2 Q2.hfix147_142_2 Q2.hinj147_142_2
      Q2.hcardT147_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_142_2 i) (Q2.hfix147_142_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨142, by decide⟩ 1 (transLenTr ⟨142, by decide⟩ 1 hp) : ↥(reps ⟨142, by decide⟩)) : Coordinate 1)
        T147_142 = colFn colCertDiv_147_142_1.D1 (m := 1) from colCertDiv_147_142_1.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨142, by decide⟩ 1 hp : ↥(Q2.reps ⟨142, by decide⟩)) : Coordinate 2)
        Q2.T147_142_2 = colFn colCertDiv_147_142_1.D2 (m := 1) from colCertDiv_147_142_1.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_142_1_match


theorem leaf_147_142_2 (hp : 2 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 2 (transLenTr ⟨142, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 2 (transLenTr ⟨142, by decide⟩ 2 hp)) T147_142
      hfix147_142 hinj147_142 hcardT147_142
      (fun i => conj_mem_of_fixedPoints _ _ (T147_142 i) (hfix147_142 i) _)
      ⟨147, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 2 hp) Q2.T147_142_2 Q2.hfix147_142_2 Q2.hinj147_142_2
      Q2.hcardT147_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_142_2 i) (Q2.hfix147_142_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨142, by decide⟩ 2 (transLenTr ⟨142, by decide⟩ 2 hp) : ↥(reps ⟨142, by decide⟩)) : Coordinate 1)
        T147_142 = colFn colCertDiv_147_142_2.D1 (m := 1) from colCertDiv_147_142_2.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨142, by decide⟩ 2 hp : ↥(Q2.reps ⟨142, by decide⟩)) : Coordinate 2)
        Q2.T147_142_2 = colFn colCertDiv_147_142_2.D2 (m := 1) from colCertDiv_147_142_2.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_142_2_match


theorem leaf_147_142_3 (hp : 3 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 3 (transLenTr ⟨142, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 3 (transLenTr ⟨142, by decide⟩ 3 hp)) T147_142
      hfix147_142 hinj147_142 hcardT147_142
      (fun i => conj_mem_of_fixedPoints _ _ (T147_142 i) (hfix147_142 i) _)
      ⟨147, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 3 hp) Q2.T147_142_2 Q2.hfix147_142_2 Q2.hinj147_142_2
      Q2.hcardT147_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_142_2 i) (Q2.hfix147_142_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨142, by decide⟩ 3 (transLenTr ⟨142, by decide⟩ 3 hp) : ↥(reps ⟨142, by decide⟩)) : Coordinate 1)
        T147_142 = colFn colCertDiv_147_142_3.D1 (m := 1) from colCertDiv_147_142_3.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨142, by decide⟩ 3 hp : ↥(Q2.reps ⟨142, by decide⟩)) : Coordinate 2)
        Q2.T147_142_2 = colFn colCertDiv_147_142_3.D2 (m := 1) from colCertDiv_147_142_3.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_142_3_match


theorem leaf_147_142_4 (hp : 4 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 4 (transLenTr ⟨142, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 4 (transLenTr ⟨142, by decide⟩ 4 hp)) T147_142
      hfix147_142 hinj147_142 hcardT147_142
      (fun i => conj_mem_of_fixedPoints _ _ (T147_142 i) (hfix147_142 i) _)
      ⟨147, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 4 hp) Q2.T147_142_2 Q2.hfix147_142_2 Q2.hinj147_142_2
      Q2.hcardT147_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_142_2 i) (Q2.hfix147_142_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨142, by decide⟩ 4 (transLenTr ⟨142, by decide⟩ 4 hp) : ↥(reps ⟨142, by decide⟩)) : Coordinate 1)
        T147_142 = colFn colCertDiv_147_142_4.D1 (m := 1) from colCertDiv_147_142_4.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨142, by decide⟩ 4 hp : ↥(Q2.reps ⟨142, by decide⟩)) : Coordinate 2)
        Q2.T147_142_2 = colFn colCertDiv_147_142_4.D2 (m := 1) from colCertDiv_147_142_4.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_142_4_match


theorem leaf_147_142_5 (hp : 5 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 5 (transLenTr ⟨142, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 5 (transLenTr ⟨142, by decide⟩ 5 hp)) T147_142
      hfix147_142 hinj147_142 hcardT147_142
      (fun i => conj_mem_of_fixedPoints _ _ (T147_142 i) (hfix147_142 i) _)
      ⟨147, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 5 hp) Q2.T147_142_2 Q2.hfix147_142_2 Q2.hinj147_142_2
      Q2.hcardT147_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_142_2 i) (Q2.hfix147_142_2 i) _)
      colCert_147_142_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_142_6 (hp : 6 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 6 (transLenTr ⟨142, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 6 (transLenTr ⟨142, by decide⟩ 6 hp)) T147_142
      hfix147_142 hinj147_142 hcardT147_142
      (fun i => conj_mem_of_fixedPoints _ _ (T147_142 i) (hfix147_142 i) _)
      ⟨147, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 6 hp) Q2.T147_142_2 Q2.hfix147_142_2 Q2.hinj147_142_2
      Q2.hcardT147_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_142_2 i) (Q2.hfix147_142_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨142, by decide⟩ 6 (transLenTr ⟨142, by decide⟩ 6 hp) : ↥(reps ⟨142, by decide⟩)) : Coordinate 1)
        T147_142 = colFn colCertDiv_147_142_6.D1 (m := 1) from colCertDiv_147_142_6.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨142, by decide⟩ 6 hp : ↥(Q2.reps ⟨142, by decide⟩)) : Coordinate 2)
        Q2.T147_142_2 = colFn colCertDiv_147_142_6.D2 (m := 1) from colCertDiv_147_142_6.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_142_6_match


theorem leaf_147_142_7 (hp : 7 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 7 (transLenTr ⟨142, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 7 (transLenTr ⟨142, by decide⟩ 7 hp)) T147_142
      hfix147_142 hinj147_142 hcardT147_142
      (fun i => conj_mem_of_fixedPoints _ _ (T147_142 i) (hfix147_142 i) _)
      ⟨147, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 7 hp) Q2.T147_142_2 Q2.hfix147_142_2 Q2.hinj147_142_2
      Q2.hcardT147_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_142_2 i) (Q2.hfix147_142_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨142, by decide⟩ 7 (transLenTr ⟨142, by decide⟩ 7 hp) : ↥(reps ⟨142, by decide⟩)) : Coordinate 1)
        T147_142 = colFn colCertDiv_147_142_7.D1 (m := 1) from colCertDiv_147_142_7.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨142, by decide⟩ 7 hp : ↥(Q2.reps ⟨142, by decide⟩)) : Coordinate 2)
        Q2.T147_142_2 = colFn colCertDiv_147_142_7.D2 (m := 1) from colCertDiv_147_142_7.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_142_7_match


theorem leaf_147_142_8 (hp : 8 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 8 (transLenTr ⟨142, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 8 (transLenTr ⟨142, by decide⟩ 8 hp)) T147_142
      hfix147_142 hinj147_142 hcardT147_142
      (fun i => conj_mem_of_fixedPoints _ _ (T147_142 i) (hfix147_142 i) _)
      ⟨147, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 8 hp) Q2.T147_142_2 Q2.hfix147_142_2 Q2.hinj147_142_2
      Q2.hcardT147_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_142_2 i) (Q2.hfix147_142_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨142, by decide⟩ 8 (transLenTr ⟨142, by decide⟩ 8 hp) : ↥(reps ⟨142, by decide⟩)) : Coordinate 1)
        T147_142 = colFn colCertDiv_147_142_8.D1 (m := 1) from colCertDiv_147_142_8.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨142, by decide⟩ 8 hp : ↥(Q2.reps ⟨142, by decide⟩)) : Coordinate 2)
        Q2.T147_142_2 = colFn colCertDiv_147_142_8.D2 (m := 1) from colCertDiv_147_142_8.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_142_8_match


theorem leaf_147_142_9 (hp : 9 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 9 (transLenTr ⟨142, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 9 (transLenTr ⟨142, by decide⟩ 9 hp)) T147_142
      hfix147_142 hinj147_142 hcardT147_142
      (fun i => conj_mem_of_fixedPoints _ _ (T147_142 i) (hfix147_142 i) _)
      ⟨147, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 9 hp) Q2.T147_142_2 Q2.hfix147_142_2 Q2.hinj147_142_2
      Q2.hcardT147_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_142_2 i) (Q2.hfix147_142_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨142, by decide⟩ 9 (transLenTr ⟨142, by decide⟩ 9 hp) : ↥(reps ⟨142, by decide⟩)) : Coordinate 1)
        T147_142 = colFn colCertDiv_147_142_9.D1 (m := 1) from colCertDiv_147_142_9.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨142, by decide⟩ 9 hp : ↥(Q2.reps ⟨142, by decide⟩)) : Coordinate 2)
        Q2.T147_142_2 = colFn colCertDiv_147_142_9.D2 (m := 1) from colCertDiv_147_142_9.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_142_9_match


theorem leaf_147_142_10 (hp : 10 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 10 (transLenTr ⟨142, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 10 (transLenTr ⟨142, by decide⟩ 10 hp)) T147_142
      hfix147_142 hinj147_142 hcardT147_142
      (fun i => conj_mem_of_fixedPoints _ _ (T147_142 i) (hfix147_142 i) _)
      ⟨147, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 10 hp) Q2.T147_142_2 Q2.hfix147_142_2 Q2.hinj147_142_2
      Q2.hcardT147_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_142_2 i) (Q2.hfix147_142_2 i) _)
      colCert_147_142_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_142_11 (hp : 11 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 11 (transLenTr ⟨142, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 11 (transLenTr ⟨142, by decide⟩ 11 hp)) T147_142
      hfix147_142 hinj147_142 hcardT147_142
      (fun i => conj_mem_of_fixedPoints _ _ (T147_142 i) (hfix147_142 i) _)
      ⟨147, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 11 hp) Q2.T147_142_2 Q2.hfix147_142_2 Q2.hinj147_142_2
      Q2.hcardT147_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_142_2 i) (Q2.hfix147_142_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨142, by decide⟩ 11 (transLenTr ⟨142, by decide⟩ 11 hp) : ↥(reps ⟨142, by decide⟩)) : Coordinate 1)
        T147_142 = colFn colCertDiv_147_142_11.D1 (m := 1) from colCertDiv_147_142_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨142, by decide⟩ 11 hp : ↥(Q2.reps ⟨142, by decide⟩)) : Coordinate 2)
        Q2.T147_142_2 = colFn colCertDiv_147_142_11.D2 (m := 1) from colCertDiv_147_142_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_142_11_match


theorem leaf_147_142_12 (hp : 12 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 12 (transLenTr ⟨142, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 12 (transLenTr ⟨142, by decide⟩ 12 hp)) T147_142
      hfix147_142 hinj147_142 hcardT147_142
      (fun i => conj_mem_of_fixedPoints _ _ (T147_142 i) (hfix147_142 i) _)
      ⟨147, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 12 hp) Q2.T147_142_2 Q2.hfix147_142_2 Q2.hinj147_142_2
      Q2.hcardT147_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_142_2 i) (Q2.hfix147_142_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨142, by decide⟩ 12 (transLenTr ⟨142, by decide⟩ 12 hp) : ↥(reps ⟨142, by decide⟩)) : Coordinate 1)
        T147_142 = colFn colCertDiv_147_142_12.D1 (m := 1) from colCertDiv_147_142_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨142, by decide⟩ 12 hp : ↥(Q2.reps ⟨142, by decide⟩)) : Coordinate 2)
        Q2.T147_142_2 = colFn colCertDiv_147_142_12.D2 (m := 1) from colCertDiv_147_142_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_142_12_match


theorem leaf_147_142_13 (hp : 13 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 13 (transLenTr ⟨142, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 13 (transLenTr ⟨142, by decide⟩ 13 hp)) T147_142
      hfix147_142 hinj147_142 hcardT147_142
      (fun i => conj_mem_of_fixedPoints _ _ (T147_142 i) (hfix147_142 i) _)
      ⟨147, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 13 hp) Q2.T147_142_2 Q2.hfix147_142_2 Q2.hinj147_142_2
      Q2.hcardT147_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_142_2 i) (Q2.hfix147_142_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨142, by decide⟩ 13 (transLenTr ⟨142, by decide⟩ 13 hp) : ↥(reps ⟨142, by decide⟩)) : Coordinate 1)
        T147_142 = colFn colCertDiv_147_142_13.D1 (m := 1) from colCertDiv_147_142_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨142, by decide⟩ 13 hp : ↥(Q2.reps ⟨142, by decide⟩)) : Coordinate 2)
        Q2.T147_142_2 = colFn colCertDiv_147_142_13.D2 (m := 1) from colCertDiv_147_142_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_142_13_match


theorem leaf_147_142_14 (hp : 14 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 14 (transLenTr ⟨142, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 14 (transLenTr ⟨142, by decide⟩ 14 hp)) T147_142
      hfix147_142 hinj147_142 hcardT147_142
      (fun i => conj_mem_of_fixedPoints _ _ (T147_142 i) (hfix147_142 i) _)
      ⟨147, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 14 hp) Q2.T147_142_2 Q2.hfix147_142_2 Q2.hinj147_142_2
      Q2.hcardT147_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_142_2 i) (Q2.hfix147_142_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨142, by decide⟩ 14 (transLenTr ⟨142, by decide⟩ 14 hp) : ↥(reps ⟨142, by decide⟩)) : Coordinate 1)
        T147_142 = colFn colCertDiv_147_142_14.D1 (m := 1) from colCertDiv_147_142_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨142, by decide⟩ 14 hp : ↥(Q2.reps ⟨142, by decide⟩)) : Coordinate 2)
        Q2.T147_142_2 = colFn colCertDiv_147_142_14.D2 (m := 1) from colCertDiv_147_142_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_142_14_match


theorem leaf_147_142_15 (hp : 15 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 15 (transLenTr ⟨142, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 15 (transLenTr ⟨142, by decide⟩ 15 hp)) T147_142
      hfix147_142 hinj147_142 hcardT147_142
      (fun i => conj_mem_of_fixedPoints _ _ (T147_142 i) (hfix147_142 i) _)
      ⟨147, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 15 hp) Q2.T147_142_2 Q2.hfix147_142_2 Q2.hinj147_142_2
      Q2.hcardT147_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_142_2 i) (Q2.hfix147_142_2 i) _)
      colCert_147_142_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_142_16 (hp : 16 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 16 (transLenTr ⟨142, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 16 (transLenTr ⟨142, by decide⟩ 16 hp)) T147_142
      hfix147_142 hinj147_142 hcardT147_142
      (fun i => conj_mem_of_fixedPoints _ _ (T147_142 i) (hfix147_142 i) _)
      ⟨147, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 16 hp) Q2.T147_142_2 Q2.hfix147_142_2 Q2.hinj147_142_2
      Q2.hcardT147_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_142_2 i) (Q2.hfix147_142_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨142, by decide⟩ 16 (transLenTr ⟨142, by decide⟩ 16 hp) : ↥(reps ⟨142, by decide⟩)) : Coordinate 1)
        T147_142 = colFn colCertDiv_147_142_16.D1 (m := 1) from colCertDiv_147_142_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨142, by decide⟩ 16 hp : ↥(Q2.reps ⟨142, by decide⟩)) : Coordinate 2)
        Q2.T147_142_2 = colFn colCertDiv_147_142_16.D2 (m := 1) from colCertDiv_147_142_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_142_16_match


theorem leaf_147_142_17 (hp : 17 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 17 (transLenTr ⟨142, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 17 (transLenTr ⟨142, by decide⟩ 17 hp)) T147_142
      hfix147_142 hinj147_142 hcardT147_142
      (fun i => conj_mem_of_fixedPoints _ _ (T147_142 i) (hfix147_142 i) _)
      ⟨147, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 17 hp) Q2.T147_142_2 Q2.hfix147_142_2 Q2.hinj147_142_2
      Q2.hcardT147_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_142_2 i) (Q2.hfix147_142_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨142, by decide⟩ 17 (transLenTr ⟨142, by decide⟩ 17 hp) : ↥(reps ⟨142, by decide⟩)) : Coordinate 1)
        T147_142 = colFn colCertDiv_147_142_17.D1 (m := 1) from colCertDiv_147_142_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨142, by decide⟩ 17 hp : ↥(Q2.reps ⟨142, by decide⟩)) : Coordinate 2)
        Q2.T147_142_2 = colFn colCertDiv_147_142_17.D2 (m := 1) from colCertDiv_147_142_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_142_17_match


theorem leaf_147_142_18 (hp : 18 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 18 (transLenTr ⟨142, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 18 (transLenTr ⟨142, by decide⟩ 18 hp)) T147_142
      hfix147_142 hinj147_142 hcardT147_142
      (fun i => conj_mem_of_fixedPoints _ _ (T147_142 i) (hfix147_142 i) _)
      ⟨147, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 18 hp) Q2.T147_142_2 Q2.hfix147_142_2 Q2.hinj147_142_2
      Q2.hcardT147_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_142_2 i) (Q2.hfix147_142_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨142, by decide⟩ 18 (transLenTr ⟨142, by decide⟩ 18 hp) : ↥(reps ⟨142, by decide⟩)) : Coordinate 1)
        T147_142 = colFn colCertDiv_147_142_18.D1 (m := 1) from colCertDiv_147_142_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨142, by decide⟩ 18 hp : ↥(Q2.reps ⟨142, by decide⟩)) : Coordinate 2)
        Q2.T147_142_2 = colFn colCertDiv_147_142_18.D2 (m := 1) from colCertDiv_147_142_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_142_18_match


theorem leaf_147_142_19 (hp : 19 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 19 (transLenTr ⟨142, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 19 (transLenTr ⟨142, by decide⟩ 19 hp)) T147_142
      hfix147_142 hinj147_142 hcardT147_142
      (fun i => conj_mem_of_fixedPoints _ _ (T147_142 i) (hfix147_142 i) _)
      ⟨147, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 19 hp) Q2.T147_142_2 Q2.hfix147_142_2 Q2.hinj147_142_2
      Q2.hcardT147_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_142_2 i) (Q2.hfix147_142_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨142, by decide⟩ 19 (transLenTr ⟨142, by decide⟩ 19 hp) : ↥(reps ⟨142, by decide⟩)) : Coordinate 1)
        T147_142 = colFn colCertDiv_147_142_19.D1 (m := 1) from colCertDiv_147_142_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨142, by decide⟩ 19 hp : ↥(Q2.reps ⟨142, by decide⟩)) : Coordinate 2)
        Q2.T147_142_2 = colFn colCertDiv_147_142_19.D2 (m := 1) from colCertDiv_147_142_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_142_19_match


theorem leaf_147_142_20 (hp : 20 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 20 (transLenTr ⟨142, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 20 (transLenTr ⟨142, by decide⟩ 20 hp)) T147_142
      hfix147_142 hinj147_142 hcardT147_142
      (fun i => conj_mem_of_fixedPoints _ _ (T147_142 i) (hfix147_142 i) _)
      ⟨147, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 20 hp) Q2.T147_142_2 Q2.hfix147_142_2 Q2.hinj147_142_2
      Q2.hcardT147_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_142_2 i) (Q2.hfix147_142_2 i) _)
      colCert_147_142_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_142_21 (hp : 21 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 21 (transLenTr ⟨142, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 21 (transLenTr ⟨142, by decide⟩ 21 hp)) T147_142
      hfix147_142 hinj147_142 hcardT147_142
      (fun i => conj_mem_of_fixedPoints _ _ (T147_142 i) (hfix147_142 i) _)
      ⟨147, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 21 hp) Q2.T147_142_2 Q2.hfix147_142_2 Q2.hinj147_142_2
      Q2.hcardT147_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_142_2 i) (Q2.hfix147_142_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨142, by decide⟩ 21 (transLenTr ⟨142, by decide⟩ 21 hp) : ↥(reps ⟨142, by decide⟩)) : Coordinate 1)
        T147_142 = colFn colCertDiv_147_142_21.D1 (m := 1) from colCertDiv_147_142_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨142, by decide⟩ 21 hp : ↥(Q2.reps ⟨142, by decide⟩)) : Coordinate 2)
        Q2.T147_142_2 = colFn colCertDiv_147_142_21.D2 (m := 1) from colCertDiv_147_142_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_142_21_match


theorem leaf_147_142_22 (hp : 22 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 22 (transLenTr ⟨142, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 22 (transLenTr ⟨142, by decide⟩ 22 hp)) T147_142
      hfix147_142 hinj147_142 hcardT147_142
      (fun i => conj_mem_of_fixedPoints _ _ (T147_142 i) (hfix147_142 i) _)
      ⟨147, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 22 hp) Q2.T147_142_2 Q2.hfix147_142_2 Q2.hinj147_142_2
      Q2.hcardT147_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_142_2 i) (Q2.hfix147_142_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨142, by decide⟩ 22 (transLenTr ⟨142, by decide⟩ 22 hp) : ↥(reps ⟨142, by decide⟩)) : Coordinate 1)
        T147_142 = colFn colCertDiv_147_142_22.D1 (m := 1) from colCertDiv_147_142_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨142, by decide⟩ 22 hp : ↥(Q2.reps ⟨142, by decide⟩)) : Coordinate 2)
        Q2.T147_142_2 = colFn colCertDiv_147_142_22.D2 (m := 1) from colCertDiv_147_142_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_142_22_match


theorem leaf_147_142_23 (hp : 23 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 23 (transLenTr ⟨142, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 23 (transLenTr ⟨142, by decide⟩ 23 hp)) T147_142
      hfix147_142 hinj147_142 hcardT147_142
      (fun i => conj_mem_of_fixedPoints _ _ (T147_142 i) (hfix147_142 i) _)
      ⟨147, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 23 hp) Q2.T147_142_2 Q2.hfix147_142_2 Q2.hinj147_142_2
      Q2.hcardT147_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_142_2 i) (Q2.hfix147_142_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨142, by decide⟩ 23 (transLenTr ⟨142, by decide⟩ 23 hp) : ↥(reps ⟨142, by decide⟩)) : Coordinate 1)
        T147_142 = colFn colCertDiv_147_142_23.D1 (m := 1) from colCertDiv_147_142_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨142, by decide⟩ 23 hp : ↥(Q2.reps ⟨142, by decide⟩)) : Coordinate 2)
        Q2.T147_142_2 = colFn colCertDiv_147_142_23.D2 (m := 1) from colCertDiv_147_142_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_142_23_match


theorem leaf_147_142_24 (hp : 24 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 24 (transLenTr ⟨142, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 24 (transLenTr ⟨142, by decide⟩ 24 hp)) T147_142
      hfix147_142 hinj147_142 hcardT147_142
      (fun i => conj_mem_of_fixedPoints _ _ (T147_142 i) (hfix147_142 i) _)
      ⟨147, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 24 hp) Q2.T147_142_2 Q2.hfix147_142_2 Q2.hinj147_142_2
      Q2.hcardT147_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_142_2 i) (Q2.hfix147_142_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨142, by decide⟩ 24 (transLenTr ⟨142, by decide⟩ 24 hp) : ↥(reps ⟨142, by decide⟩)) : Coordinate 1)
        T147_142 = colFn colCertDiv_147_142_24.D1 (m := 1) from colCertDiv_147_142_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨142, by decide⟩ 24 hp : ↥(Q2.reps ⟨142, by decide⟩)) : Coordinate 2)
        Q2.T147_142_2 = colFn colCertDiv_147_142_24.D2 (m := 1) from colCertDiv_147_142_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_142_24_match


theorem leaf_147_143_0 (hp : 0 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 0 (transLenTr ⟨143, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 0 (transLenTr ⟨143, by decide⟩ 0 hp)) T147_143
      hfix147_143 hinj147_143 hcardT147_143
      (fun i => conj_mem_of_fixedPoints _ _ (T147_143 i) (hfix147_143 i) _)
      ⟨147, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 0 hp) Q2.T147_143_2 Q2.hfix147_143_2 Q2.hinj147_143_2
      Q2.hcardT147_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_143_2 i) (Q2.hfix147_143_2 i) _)
      colCert_147_143_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_143_1 (hp : 1 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 1 (transLenTr ⟨143, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 1 (transLenTr ⟨143, by decide⟩ 1 hp)) T147_143
      hfix147_143 hinj147_143 hcardT147_143
      (fun i => conj_mem_of_fixedPoints _ _ (T147_143 i) (hfix147_143 i) _)
      ⟨147, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 1 hp) Q2.T147_143_2 Q2.hfix147_143_2 Q2.hinj147_143_2
      Q2.hcardT147_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_143_2 i) (Q2.hfix147_143_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨143, by decide⟩ 1 (transLenTr ⟨143, by decide⟩ 1 hp) : ↥(reps ⟨143, by decide⟩)) : Coordinate 1)
        T147_143 = colFn colCertDiv_147_143_1.D1 (m := 1) from colCertDiv_147_143_1.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨143, by decide⟩ 1 hp : ↥(Q2.reps ⟨143, by decide⟩)) : Coordinate 2)
        Q2.T147_143_2 = colFn colCertDiv_147_143_1.D2 (m := 1) from colCertDiv_147_143_1.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_143_1_match


theorem leaf_147_143_2 (hp : 2 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 2 (transLenTr ⟨143, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 2 (transLenTr ⟨143, by decide⟩ 2 hp)) T147_143
      hfix147_143 hinj147_143 hcardT147_143
      (fun i => conj_mem_of_fixedPoints _ _ (T147_143 i) (hfix147_143 i) _)
      ⟨147, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 2 hp) Q2.T147_143_2 Q2.hfix147_143_2 Q2.hinj147_143_2
      Q2.hcardT147_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_143_2 i) (Q2.hfix147_143_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨143, by decide⟩ 2 (transLenTr ⟨143, by decide⟩ 2 hp) : ↥(reps ⟨143, by decide⟩)) : Coordinate 1)
        T147_143 = colFn colCertDiv_147_143_2.D1 (m := 1) from colCertDiv_147_143_2.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨143, by decide⟩ 2 hp : ↥(Q2.reps ⟨143, by decide⟩)) : Coordinate 2)
        Q2.T147_143_2 = colFn colCertDiv_147_143_2.D2 (m := 1) from colCertDiv_147_143_2.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_143_2_match


theorem leaf_147_143_3 (hp : 3 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 3 (transLenTr ⟨143, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 3 (transLenTr ⟨143, by decide⟩ 3 hp)) T147_143
      hfix147_143 hinj147_143 hcardT147_143
      (fun i => conj_mem_of_fixedPoints _ _ (T147_143 i) (hfix147_143 i) _)
      ⟨147, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 3 hp) Q2.T147_143_2 Q2.hfix147_143_2 Q2.hinj147_143_2
      Q2.hcardT147_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_143_2 i) (Q2.hfix147_143_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨143, by decide⟩ 3 (transLenTr ⟨143, by decide⟩ 3 hp) : ↥(reps ⟨143, by decide⟩)) : Coordinate 1)
        T147_143 = colFn colCertDiv_147_143_3.D1 (m := 1) from colCertDiv_147_143_3.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨143, by decide⟩ 3 hp : ↥(Q2.reps ⟨143, by decide⟩)) : Coordinate 2)
        Q2.T147_143_2 = colFn colCertDiv_147_143_3.D2 (m := 1) from colCertDiv_147_143_3.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_143_3_match


theorem leaf_147_143_4 (hp : 4 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 4 (transLenTr ⟨143, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 4 (transLenTr ⟨143, by decide⟩ 4 hp)) T147_143
      hfix147_143 hinj147_143 hcardT147_143
      (fun i => conj_mem_of_fixedPoints _ _ (T147_143 i) (hfix147_143 i) _)
      ⟨147, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 4 hp) Q2.T147_143_2 Q2.hfix147_143_2 Q2.hinj147_143_2
      Q2.hcardT147_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_143_2 i) (Q2.hfix147_143_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨143, by decide⟩ 4 (transLenTr ⟨143, by decide⟩ 4 hp) : ↥(reps ⟨143, by decide⟩)) : Coordinate 1)
        T147_143 = colFn colCertDiv_147_143_4.D1 (m := 1) from colCertDiv_147_143_4.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨143, by decide⟩ 4 hp : ↥(Q2.reps ⟨143, by decide⟩)) : Coordinate 2)
        Q2.T147_143_2 = colFn colCertDiv_147_143_4.D2 (m := 1) from colCertDiv_147_143_4.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_143_4_match


theorem leaf_147_143_5 (hp : 5 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 5 (transLenTr ⟨143, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 5 (transLenTr ⟨143, by decide⟩ 5 hp)) T147_143
      hfix147_143 hinj147_143 hcardT147_143
      (fun i => conj_mem_of_fixedPoints _ _ (T147_143 i) (hfix147_143 i) _)
      ⟨147, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 5 hp) Q2.T147_143_2 Q2.hfix147_143_2 Q2.hinj147_143_2
      Q2.hcardT147_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_143_2 i) (Q2.hfix147_143_2 i) _)
      colCert_147_143_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_143_6 (hp : 6 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 6 (transLenTr ⟨143, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 6 (transLenTr ⟨143, by decide⟩ 6 hp)) T147_143
      hfix147_143 hinj147_143 hcardT147_143
      (fun i => conj_mem_of_fixedPoints _ _ (T147_143 i) (hfix147_143 i) _)
      ⟨147, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 6 hp) Q2.T147_143_2 Q2.hfix147_143_2 Q2.hinj147_143_2
      Q2.hcardT147_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_143_2 i) (Q2.hfix147_143_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨143, by decide⟩ 6 (transLenTr ⟨143, by decide⟩ 6 hp) : ↥(reps ⟨143, by decide⟩)) : Coordinate 1)
        T147_143 = colFn colCertDiv_147_143_6.D1 (m := 1) from colCertDiv_147_143_6.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨143, by decide⟩ 6 hp : ↥(Q2.reps ⟨143, by decide⟩)) : Coordinate 2)
        Q2.T147_143_2 = colFn colCertDiv_147_143_6.D2 (m := 1) from colCertDiv_147_143_6.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_143_6_match


theorem leaf_147_143_7 (hp : 7 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 7 (transLenTr ⟨143, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 7 (transLenTr ⟨143, by decide⟩ 7 hp)) T147_143
      hfix147_143 hinj147_143 hcardT147_143
      (fun i => conj_mem_of_fixedPoints _ _ (T147_143 i) (hfix147_143 i) _)
      ⟨147, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 7 hp) Q2.T147_143_2 Q2.hfix147_143_2 Q2.hinj147_143_2
      Q2.hcardT147_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_143_2 i) (Q2.hfix147_143_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨143, by decide⟩ 7 (transLenTr ⟨143, by decide⟩ 7 hp) : ↥(reps ⟨143, by decide⟩)) : Coordinate 1)
        T147_143 = colFn colCertDiv_147_143_7.D1 (m := 1) from colCertDiv_147_143_7.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨143, by decide⟩ 7 hp : ↥(Q2.reps ⟨143, by decide⟩)) : Coordinate 2)
        Q2.T147_143_2 = colFn colCertDiv_147_143_7.D2 (m := 1) from colCertDiv_147_143_7.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_143_7_match


theorem leaf_147_143_8 (hp : 8 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 8 (transLenTr ⟨143, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 8 (transLenTr ⟨143, by decide⟩ 8 hp)) T147_143
      hfix147_143 hinj147_143 hcardT147_143
      (fun i => conj_mem_of_fixedPoints _ _ (T147_143 i) (hfix147_143 i) _)
      ⟨147, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 8 hp) Q2.T147_143_2 Q2.hfix147_143_2 Q2.hinj147_143_2
      Q2.hcardT147_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_143_2 i) (Q2.hfix147_143_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨143, by decide⟩ 8 (transLenTr ⟨143, by decide⟩ 8 hp) : ↥(reps ⟨143, by decide⟩)) : Coordinate 1)
        T147_143 = colFn colCertDiv_147_143_8.D1 (m := 1) from colCertDiv_147_143_8.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨143, by decide⟩ 8 hp : ↥(Q2.reps ⟨143, by decide⟩)) : Coordinate 2)
        Q2.T147_143_2 = colFn colCertDiv_147_143_8.D2 (m := 1) from colCertDiv_147_143_8.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_143_8_match


theorem leaf_147_143_9 (hp : 9 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 9 (transLenTr ⟨143, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 9 (transLenTr ⟨143, by decide⟩ 9 hp)) T147_143
      hfix147_143 hinj147_143 hcardT147_143
      (fun i => conj_mem_of_fixedPoints _ _ (T147_143 i) (hfix147_143 i) _)
      ⟨147, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 9 hp) Q2.T147_143_2 Q2.hfix147_143_2 Q2.hinj147_143_2
      Q2.hcardT147_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_143_2 i) (Q2.hfix147_143_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨143, by decide⟩ 9 (transLenTr ⟨143, by decide⟩ 9 hp) : ↥(reps ⟨143, by decide⟩)) : Coordinate 1)
        T147_143 = colFn colCertDiv_147_143_9.D1 (m := 1) from colCertDiv_147_143_9.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨143, by decide⟩ 9 hp : ↥(Q2.reps ⟨143, by decide⟩)) : Coordinate 2)
        Q2.T147_143_2 = colFn colCertDiv_147_143_9.D2 (m := 1) from colCertDiv_147_143_9.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_143_9_match


theorem leaf_147_143_10 (hp : 10 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 10 (transLenTr ⟨143, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 10 (transLenTr ⟨143, by decide⟩ 10 hp)) T147_143
      hfix147_143 hinj147_143 hcardT147_143
      (fun i => conj_mem_of_fixedPoints _ _ (T147_143 i) (hfix147_143 i) _)
      ⟨147, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 10 hp) Q2.T147_143_2 Q2.hfix147_143_2 Q2.hinj147_143_2
      Q2.hcardT147_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_143_2 i) (Q2.hfix147_143_2 i) _)
      colCert_147_143_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_143_11 (hp : 11 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 11 (transLenTr ⟨143, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 11 (transLenTr ⟨143, by decide⟩ 11 hp)) T147_143
      hfix147_143 hinj147_143 hcardT147_143
      (fun i => conj_mem_of_fixedPoints _ _ (T147_143 i) (hfix147_143 i) _)
      ⟨147, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 11 hp) Q2.T147_143_2 Q2.hfix147_143_2 Q2.hinj147_143_2
      Q2.hcardT147_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_143_2 i) (Q2.hfix147_143_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨143, by decide⟩ 11 (transLenTr ⟨143, by decide⟩ 11 hp) : ↥(reps ⟨143, by decide⟩)) : Coordinate 1)
        T147_143 = colFn colCertDiv_147_143_11.D1 (m := 1) from colCertDiv_147_143_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨143, by decide⟩ 11 hp : ↥(Q2.reps ⟨143, by decide⟩)) : Coordinate 2)
        Q2.T147_143_2 = colFn colCertDiv_147_143_11.D2 (m := 1) from colCertDiv_147_143_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_143_11_match


theorem leaf_147_143_12 (hp : 12 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 12 (transLenTr ⟨143, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 12 (transLenTr ⟨143, by decide⟩ 12 hp)) T147_143
      hfix147_143 hinj147_143 hcardT147_143
      (fun i => conj_mem_of_fixedPoints _ _ (T147_143 i) (hfix147_143 i) _)
      ⟨147, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 12 hp) Q2.T147_143_2 Q2.hfix147_143_2 Q2.hinj147_143_2
      Q2.hcardT147_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_143_2 i) (Q2.hfix147_143_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨143, by decide⟩ 12 (transLenTr ⟨143, by decide⟩ 12 hp) : ↥(reps ⟨143, by decide⟩)) : Coordinate 1)
        T147_143 = colFn colCertDiv_147_143_12.D1 (m := 1) from colCertDiv_147_143_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨143, by decide⟩ 12 hp : ↥(Q2.reps ⟨143, by decide⟩)) : Coordinate 2)
        Q2.T147_143_2 = colFn colCertDiv_147_143_12.D2 (m := 1) from colCertDiv_147_143_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_143_12_match


theorem leaf_147_143_13 (hp : 13 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 13 (transLenTr ⟨143, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 13 (transLenTr ⟨143, by decide⟩ 13 hp)) T147_143
      hfix147_143 hinj147_143 hcardT147_143
      (fun i => conj_mem_of_fixedPoints _ _ (T147_143 i) (hfix147_143 i) _)
      ⟨147, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 13 hp) Q2.T147_143_2 Q2.hfix147_143_2 Q2.hinj147_143_2
      Q2.hcardT147_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_143_2 i) (Q2.hfix147_143_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨143, by decide⟩ 13 (transLenTr ⟨143, by decide⟩ 13 hp) : ↥(reps ⟨143, by decide⟩)) : Coordinate 1)
        T147_143 = colFn colCertDiv_147_143_13.D1 (m := 1) from colCertDiv_147_143_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨143, by decide⟩ 13 hp : ↥(Q2.reps ⟨143, by decide⟩)) : Coordinate 2)
        Q2.T147_143_2 = colFn colCertDiv_147_143_13.D2 (m := 1) from colCertDiv_147_143_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_143_13_match


theorem leaf_147_143_14 (hp : 14 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 14 (transLenTr ⟨143, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 14 (transLenTr ⟨143, by decide⟩ 14 hp)) T147_143
      hfix147_143 hinj147_143 hcardT147_143
      (fun i => conj_mem_of_fixedPoints _ _ (T147_143 i) (hfix147_143 i) _)
      ⟨147, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 14 hp) Q2.T147_143_2 Q2.hfix147_143_2 Q2.hinj147_143_2
      Q2.hcardT147_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_143_2 i) (Q2.hfix147_143_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨143, by decide⟩ 14 (transLenTr ⟨143, by decide⟩ 14 hp) : ↥(reps ⟨143, by decide⟩)) : Coordinate 1)
        T147_143 = colFn colCertDiv_147_143_14.D1 (m := 1) from colCertDiv_147_143_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨143, by decide⟩ 14 hp : ↥(Q2.reps ⟨143, by decide⟩)) : Coordinate 2)
        Q2.T147_143_2 = colFn colCertDiv_147_143_14.D2 (m := 1) from colCertDiv_147_143_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_143_14_match


theorem leaf_147_143_15 (hp : 15 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 15 (transLenTr ⟨143, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 15 (transLenTr ⟨143, by decide⟩ 15 hp)) T147_143
      hfix147_143 hinj147_143 hcardT147_143
      (fun i => conj_mem_of_fixedPoints _ _ (T147_143 i) (hfix147_143 i) _)
      ⟨147, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 15 hp) Q2.T147_143_2 Q2.hfix147_143_2 Q2.hinj147_143_2
      Q2.hcardT147_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_143_2 i) (Q2.hfix147_143_2 i) _)
      colCert_147_143_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_143_16 (hp : 16 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 16 (transLenTr ⟨143, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 16 (transLenTr ⟨143, by decide⟩ 16 hp)) T147_143
      hfix147_143 hinj147_143 hcardT147_143
      (fun i => conj_mem_of_fixedPoints _ _ (T147_143 i) (hfix147_143 i) _)
      ⟨147, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 16 hp) Q2.T147_143_2 Q2.hfix147_143_2 Q2.hinj147_143_2
      Q2.hcardT147_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_143_2 i) (Q2.hfix147_143_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨143, by decide⟩ 16 (transLenTr ⟨143, by decide⟩ 16 hp) : ↥(reps ⟨143, by decide⟩)) : Coordinate 1)
        T147_143 = colFn colCertDiv_147_143_16.D1 (m := 1) from colCertDiv_147_143_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨143, by decide⟩ 16 hp : ↥(Q2.reps ⟨143, by decide⟩)) : Coordinate 2)
        Q2.T147_143_2 = colFn colCertDiv_147_143_16.D2 (m := 1) from colCertDiv_147_143_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_143_16_match


theorem leaf_147_143_17 (hp : 17 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 17 (transLenTr ⟨143, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 17 (transLenTr ⟨143, by decide⟩ 17 hp)) T147_143
      hfix147_143 hinj147_143 hcardT147_143
      (fun i => conj_mem_of_fixedPoints _ _ (T147_143 i) (hfix147_143 i) _)
      ⟨147, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 17 hp) Q2.T147_143_2 Q2.hfix147_143_2 Q2.hinj147_143_2
      Q2.hcardT147_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_143_2 i) (Q2.hfix147_143_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨143, by decide⟩ 17 (transLenTr ⟨143, by decide⟩ 17 hp) : ↥(reps ⟨143, by decide⟩)) : Coordinate 1)
        T147_143 = colFn colCertDiv_147_143_17.D1 (m := 1) from colCertDiv_147_143_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨143, by decide⟩ 17 hp : ↥(Q2.reps ⟨143, by decide⟩)) : Coordinate 2)
        Q2.T147_143_2 = colFn colCertDiv_147_143_17.D2 (m := 1) from colCertDiv_147_143_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_143_17_match


theorem leaf_147_143_18 (hp : 18 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 18 (transLenTr ⟨143, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 18 (transLenTr ⟨143, by decide⟩ 18 hp)) T147_143
      hfix147_143 hinj147_143 hcardT147_143
      (fun i => conj_mem_of_fixedPoints _ _ (T147_143 i) (hfix147_143 i) _)
      ⟨147, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 18 hp) Q2.T147_143_2 Q2.hfix147_143_2 Q2.hinj147_143_2
      Q2.hcardT147_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_143_2 i) (Q2.hfix147_143_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨143, by decide⟩ 18 (transLenTr ⟨143, by decide⟩ 18 hp) : ↥(reps ⟨143, by decide⟩)) : Coordinate 1)
        T147_143 = colFn colCertDiv_147_143_18.D1 (m := 1) from colCertDiv_147_143_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨143, by decide⟩ 18 hp : ↥(Q2.reps ⟨143, by decide⟩)) : Coordinate 2)
        Q2.T147_143_2 = colFn colCertDiv_147_143_18.D2 (m := 1) from colCertDiv_147_143_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_143_18_match


theorem leaf_147_143_19 (hp : 19 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 19 (transLenTr ⟨143, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 19 (transLenTr ⟨143, by decide⟩ 19 hp)) T147_143
      hfix147_143 hinj147_143 hcardT147_143
      (fun i => conj_mem_of_fixedPoints _ _ (T147_143 i) (hfix147_143 i) _)
      ⟨147, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 19 hp) Q2.T147_143_2 Q2.hfix147_143_2 Q2.hinj147_143_2
      Q2.hcardT147_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_143_2 i) (Q2.hfix147_143_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨143, by decide⟩ 19 (transLenTr ⟨143, by decide⟩ 19 hp) : ↥(reps ⟨143, by decide⟩)) : Coordinate 1)
        T147_143 = colFn colCertDiv_147_143_19.D1 (m := 1) from colCertDiv_147_143_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨143, by decide⟩ 19 hp : ↥(Q2.reps ⟨143, by decide⟩)) : Coordinate 2)
        Q2.T147_143_2 = colFn colCertDiv_147_143_19.D2 (m := 1) from colCertDiv_147_143_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_143_19_match


theorem leaf_147_143_20 (hp : 20 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 20 (transLenTr ⟨143, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 20 (transLenTr ⟨143, by decide⟩ 20 hp)) T147_143
      hfix147_143 hinj147_143 hcardT147_143
      (fun i => conj_mem_of_fixedPoints _ _ (T147_143 i) (hfix147_143 i) _)
      ⟨147, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 20 hp) Q2.T147_143_2 Q2.hfix147_143_2 Q2.hinj147_143_2
      Q2.hcardT147_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_143_2 i) (Q2.hfix147_143_2 i) _)
      colCert_147_143_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_143_21 (hp : 21 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 21 (transLenTr ⟨143, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 21 (transLenTr ⟨143, by decide⟩ 21 hp)) T147_143
      hfix147_143 hinj147_143 hcardT147_143
      (fun i => conj_mem_of_fixedPoints _ _ (T147_143 i) (hfix147_143 i) _)
      ⟨147, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 21 hp) Q2.T147_143_2 Q2.hfix147_143_2 Q2.hinj147_143_2
      Q2.hcardT147_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_143_2 i) (Q2.hfix147_143_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨143, by decide⟩ 21 (transLenTr ⟨143, by decide⟩ 21 hp) : ↥(reps ⟨143, by decide⟩)) : Coordinate 1)
        T147_143 = colFn colCertDiv_147_143_21.D1 (m := 1) from colCertDiv_147_143_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨143, by decide⟩ 21 hp : ↥(Q2.reps ⟨143, by decide⟩)) : Coordinate 2)
        Q2.T147_143_2 = colFn colCertDiv_147_143_21.D2 (m := 1) from colCertDiv_147_143_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_143_21_match


end LeanDring.P5Presentation
