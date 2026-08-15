/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C029
import LeanDring.P5.Data.ColCdd.C030
import LeanDring.P5.Data.ColCdd.C031
import LeanDring.P5.Data.ColRestCheap.C119
import LeanDring.P5.Data.ColRestCheap.C120
import LeanDring.P5.Data.ColRestCheap.C121
import LeanDring.P5.Data.EntryK.C044
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C039
import LeanDring.P5.Data.SpeciesDiv.C041

/-! # Stage-5 leaves, chunk 52 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_147_72_21 (hp : 21 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 21 (transLenTr ⟨72, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 21 (transLenTr ⟨72, by decide⟩ 21 hp)) T147_72
      hfix147_72 hinj147_72 hcardT147_72
      (fun i => conj_mem_of_fixedPoints _ _ (T147_72 i) (hfix147_72 i) _)
      ⟨147, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 21 hp) Q2.T147_72_2 Q2.hfix147_72_2 Q2.hinj147_72_2
      Q2.hcardT147_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_72_2 i) (Q2.hfix147_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 21 (transLenTr ⟨72, by decide⟩ 21 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T147_72 = colFn colCertDiv_147_72_21.D1 (m := 1) from colCertDiv_147_72_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 21 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T147_72_2 = colFn colCertDiv_147_72_21.D2 (m := 1) from colCertDiv_147_72_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_72_21_match


theorem leaf_147_72_22 (hp : 22 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 22 (transLenTr ⟨72, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 22 (transLenTr ⟨72, by decide⟩ 22 hp)) T147_72
      hfix147_72 hinj147_72 hcardT147_72
      (fun i => conj_mem_of_fixedPoints _ _ (T147_72 i) (hfix147_72 i) _)
      ⟨147, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 22 hp) Q2.T147_72_2 Q2.hfix147_72_2 Q2.hinj147_72_2
      Q2.hcardT147_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_72_2 i) (Q2.hfix147_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 22 (transLenTr ⟨72, by decide⟩ 22 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T147_72 = colFn colCertDiv_147_72_22.D1 (m := 1) from colCertDiv_147_72_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 22 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T147_72_2 = colFn colCertDiv_147_72_22.D2 (m := 1) from colCertDiv_147_72_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_72_22_match


theorem leaf_147_72_23 (hp : 23 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 23 (transLenTr ⟨72, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 23 (transLenTr ⟨72, by decide⟩ 23 hp)) T147_72
      hfix147_72 hinj147_72 hcardT147_72
      (fun i => conj_mem_of_fixedPoints _ _ (T147_72 i) (hfix147_72 i) _)
      ⟨147, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 23 hp) Q2.T147_72_2 Q2.hfix147_72_2 Q2.hinj147_72_2
      Q2.hcardT147_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_72_2 i) (Q2.hfix147_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 23 (transLenTr ⟨72, by decide⟩ 23 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T147_72 = colFn colCertDiv_147_72_23.D1 (m := 1) from colCertDiv_147_72_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 23 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T147_72_2 = colFn colCertDiv_147_72_23.D2 (m := 1) from colCertDiv_147_72_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_72_23_match


theorem leaf_147_72_24 (hp : 24 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 24 (transLenTr ⟨72, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 24 (transLenTr ⟨72, by decide⟩ 24 hp)) T147_72
      hfix147_72 hinj147_72 hcardT147_72
      (fun i => conj_mem_of_fixedPoints _ _ (T147_72 i) (hfix147_72 i) _)
      ⟨147, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 24 hp) Q2.T147_72_2 Q2.hfix147_72_2 Q2.hinj147_72_2
      Q2.hcardT147_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_72_2 i) (Q2.hfix147_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 24 (transLenTr ⟨72, by decide⟩ 24 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T147_72 = colFn colCertDiv_147_72_24.D1 (m := 1) from colCertDiv_147_72_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 24 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T147_72_2 = colFn colCertDiv_147_72_24.D2 (m := 1) from colCertDiv_147_72_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_72_24_match


theorem leaf_147_73_0 (hp : 0 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 0 (transLenTr ⟨73, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 0 (transLenTr ⟨73, by decide⟩ 0 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 0 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_1 (hp : 1 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 1 (transLenTr ⟨73, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 1 (transLenTr ⟨73, by decide⟩ 1 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 1 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_2 (hp : 2 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 2 (transLenTr ⟨73, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 2 (transLenTr ⟨73, by decide⟩ 2 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 2 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_3 (hp : 3 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 3 (transLenTr ⟨73, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 3 (transLenTr ⟨73, by decide⟩ 3 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 3 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_4 (hp : 4 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 4 (transLenTr ⟨73, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 4 (transLenTr ⟨73, by decide⟩ 4 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 4 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_5 (hp : 5 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 5 (transLenTr ⟨73, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 5 (transLenTr ⟨73, by decide⟩ 5 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 5 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_6 (hp : 6 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 6 (transLenTr ⟨73, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 6 (transLenTr ⟨73, by decide⟩ 6 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 6 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_7 (hp : 7 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 7 (transLenTr ⟨73, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 7 (transLenTr ⟨73, by decide⟩ 7 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 7 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_8 (hp : 8 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 8 (transLenTr ⟨73, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 8 (transLenTr ⟨73, by decide⟩ 8 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 8 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_9 (hp : 9 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 9 (transLenTr ⟨73, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 9 (transLenTr ⟨73, by decide⟩ 9 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 9 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_10 (hp : 10 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 10 (transLenTr ⟨73, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 10 (transLenTr ⟨73, by decide⟩ 10 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 10 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_11 (hp : 11 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 11 (transLenTr ⟨73, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 11 (transLenTr ⟨73, by decide⟩ 11 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 11 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_12 (hp : 12 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 12 (transLenTr ⟨73, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 12 (transLenTr ⟨73, by decide⟩ 12 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 12 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_13 (hp : 13 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 13 (transLenTr ⟨73, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 13 (transLenTr ⟨73, by decide⟩ 13 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 13 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_14 (hp : 14 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 14 (transLenTr ⟨73, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 14 (transLenTr ⟨73, by decide⟩ 14 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 14 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_15 (hp : 15 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 15 (transLenTr ⟨73, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 15 (transLenTr ⟨73, by decide⟩ 15 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 15 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_16 (hp : 16 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 16 (transLenTr ⟨73, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 16 (transLenTr ⟨73, by decide⟩ 16 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 16 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_17 (hp : 17 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 17 (transLenTr ⟨73, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 17 (transLenTr ⟨73, by decide⟩ 17 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 17 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_18 (hp : 18 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 18 (transLenTr ⟨73, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 18 (transLenTr ⟨73, by decide⟩ 18 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 18 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_19 (hp : 19 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 19 (transLenTr ⟨73, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 19 (transLenTr ⟨73, by decide⟩ 19 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 19 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_20 (hp : 20 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 20 (transLenTr ⟨73, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 20 (transLenTr ⟨73, by decide⟩ 20 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 20 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_21 (hp : 21 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 21 (transLenTr ⟨73, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 21 (transLenTr ⟨73, by decide⟩ 21 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 21 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_22 (hp : 22 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 22 (transLenTr ⟨73, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 22 (transLenTr ⟨73, by decide⟩ 22 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 22 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_23 (hp : 23 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 23 (transLenTr ⟨73, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 23 (transLenTr ⟨73, by decide⟩ 23 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 23 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_24 (hp : 24 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 24 (transLenTr ⟨73, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 24 (transLenTr ⟨73, by decide⟩ 24 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 24 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_25 (hp : 25 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 25 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 25 (transLenTr ⟨73, by decide⟩ 25 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 25 (transLenTr ⟨73, by decide⟩ 25 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 25 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_25.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_30 (hp : 30 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 30 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 30 (transLenTr ⟨73, by decide⟩ 30 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 30 (transLenTr ⟨73, by decide⟩ 30 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 30 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_30.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_35 (hp : 35 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 35 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 35 (transLenTr ⟨73, by decide⟩ 35 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 35 (transLenTr ⟨73, by decide⟩ 35 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 35 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_35.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_40 (hp : 40 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 40 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 40 (transLenTr ⟨73, by decide⟩ 40 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 40 (transLenTr ⟨73, by decide⟩ 40 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 40 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_40.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_45 (hp : 45 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 45 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 45 (transLenTr ⟨73, by decide⟩ 45 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 45 (transLenTr ⟨73, by decide⟩ 45 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 45 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      colCert_147_73_45.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_73_50 (hp : 50 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 50 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 50 (transLenTr ⟨73, by decide⟩ 50 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 50 (transLenTr ⟨73, by decide⟩ 50 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 50 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 50 (transLenTr ⟨73, by decide⟩ 50 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T147_73 = colFn colCertDiv_147_73_50.D1 (m := 1) from colCertDiv_147_73_50.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 50 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T147_73_2 = colFn colCertDiv_147_73_50.D2 (m := 1) from colCertDiv_147_73_50.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_73_50_match


theorem leaf_147_73_55 (hp : 55 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 55 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 55 (transLenTr ⟨73, by decide⟩ 55 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 55 (transLenTr ⟨73, by decide⟩ 55 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 55 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 55 (transLenTr ⟨73, by decide⟩ 55 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T147_73 = colFn colCertDiv_147_73_55.D1 (m := 1) from colCertDiv_147_73_55.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 55 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T147_73_2 = colFn colCertDiv_147_73_55.D2 (m := 1) from colCertDiv_147_73_55.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_73_55_match


theorem leaf_147_73_60 (hp : 60 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 60 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 60 (transLenTr ⟨73, by decide⟩ 60 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 60 (transLenTr ⟨73, by decide⟩ 60 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 60 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 60 (transLenTr ⟨73, by decide⟩ 60 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T147_73 = colFn colCertDiv_147_73_60.D1 (m := 1) from colCertDiv_147_73_60.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 60 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T147_73_2 = colFn colCertDiv_147_73_60.D2 (m := 1) from colCertDiv_147_73_60.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_73_60_match


theorem leaf_147_73_65 (hp : 65 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 65 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 65 (transLenTr ⟨73, by decide⟩ 65 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 65 (transLenTr ⟨73, by decide⟩ 65 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 65 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 65 (transLenTr ⟨73, by decide⟩ 65 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T147_73 = colFn colCertDiv_147_73_65.D1 (m := 1) from colCertDiv_147_73_65.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 65 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T147_73_2 = colFn colCertDiv_147_73_65.D2 (m := 1) from colCertDiv_147_73_65.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_73_65_match


theorem leaf_147_73_70 (hp : 70 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 70 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 70 (transLenTr ⟨73, by decide⟩ 70 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 70 (transLenTr ⟨73, by decide⟩ 70 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 70 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 70 (transLenTr ⟨73, by decide⟩ 70 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T147_73 = colFn colCertDiv_147_73_70.D1 (m := 1) from colCertDiv_147_73_70.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 70 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T147_73_2 = colFn colCertDiv_147_73_70.D2 (m := 1) from colCertDiv_147_73_70.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_73_70_match


theorem leaf_147_73_75 (hp : 75 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 75 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 75 (transLenTr ⟨73, by decide⟩ 75 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 75 (transLenTr ⟨73, by decide⟩ 75 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 75 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 75 (transLenTr ⟨73, by decide⟩ 75 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T147_73 = colFn colCertDiv_147_73_75.D1 (m := 1) from colCertDiv_147_73_75.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 75 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T147_73_2 = colFn colCertDiv_147_73_75.D2 (m := 1) from colCertDiv_147_73_75.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_73_75_match


theorem leaf_147_73_80 (hp : 80 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 80 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 80 (transLenTr ⟨73, by decide⟩ 80 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 80 (transLenTr ⟨73, by decide⟩ 80 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 80 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 80 (transLenTr ⟨73, by decide⟩ 80 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T147_73 = colFn colCertDiv_147_73_80.D1 (m := 1) from colCertDiv_147_73_80.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 80 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T147_73_2 = colFn colCertDiv_147_73_80.D2 (m := 1) from colCertDiv_147_73_80.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_73_80_match


theorem leaf_147_73_85 (hp : 85 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 85 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 85 (transLenTr ⟨73, by decide⟩ 85 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 85 (transLenTr ⟨73, by decide⟩ 85 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 85 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 85 (transLenTr ⟨73, by decide⟩ 85 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T147_73 = colFn colCertDiv_147_73_85.D1 (m := 1) from colCertDiv_147_73_85.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 85 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T147_73_2 = colFn colCertDiv_147_73_85.D2 (m := 1) from colCertDiv_147_73_85.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_73_85_match


theorem leaf_147_73_90 (hp : 90 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 90 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 90 (transLenTr ⟨73, by decide⟩ 90 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 90 (transLenTr ⟨73, by decide⟩ 90 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 90 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 90 (transLenTr ⟨73, by decide⟩ 90 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T147_73 = colFn colCertDiv_147_73_90.D1 (m := 1) from colCertDiv_147_73_90.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 90 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T147_73_2 = colFn colCertDiv_147_73_90.D2 (m := 1) from colCertDiv_147_73_90.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_73_90_match


theorem leaf_147_73_95 (hp : 95 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 95 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 95 (transLenTr ⟨73, by decide⟩ 95 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 95 (transLenTr ⟨73, by decide⟩ 95 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 95 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 95 (transLenTr ⟨73, by decide⟩ 95 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T147_73 = colFn colCertDiv_147_73_95.D1 (m := 1) from colCertDiv_147_73_95.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 95 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T147_73_2 = colFn colCertDiv_147_73_95.D2 (m := 1) from colCertDiv_147_73_95.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_73_95_match


theorem leaf_147_73_100 (hp : 100 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 100 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 100 (transLenTr ⟨73, by decide⟩ 100 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 100 (transLenTr ⟨73, by decide⟩ 100 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 100 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 100 (transLenTr ⟨73, by decide⟩ 100 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T147_73 = colFn colCertDiv_147_73_100.D1 (m := 1) from colCertDiv_147_73_100.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 100 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T147_73_2 = colFn colCertDiv_147_73_100.D2 (m := 1) from colCertDiv_147_73_100.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_73_100_match


theorem leaf_147_73_105 (hp : 105 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 105 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 105 (transLenTr ⟨73, by decide⟩ 105 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 105 (transLenTr ⟨73, by decide⟩ 105 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 105 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 105 (transLenTr ⟨73, by decide⟩ 105 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T147_73 = colFn colCertDiv_147_73_105.D1 (m := 1) from colCertDiv_147_73_105.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 105 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T147_73_2 = colFn colCertDiv_147_73_105.D2 (m := 1) from colCertDiv_147_73_105.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_73_105_match


theorem leaf_147_73_110 (hp : 110 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 110 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 110 (transLenTr ⟨73, by decide⟩ 110 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 110 (transLenTr ⟨73, by decide⟩ 110 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 110 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 110 (transLenTr ⟨73, by decide⟩ 110 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T147_73 = colFn colCertDiv_147_73_110.D1 (m := 1) from colCertDiv_147_73_110.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 110 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T147_73_2 = colFn colCertDiv_147_73_110.D2 (m := 1) from colCertDiv_147_73_110.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_73_110_match


theorem leaf_147_73_115 (hp : 115 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 115 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 115 (transLenTr ⟨73, by decide⟩ 115 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 115 (transLenTr ⟨73, by decide⟩ 115 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 115 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 115 (transLenTr ⟨73, by decide⟩ 115 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T147_73 = colFn colCertDiv_147_73_115.D1 (m := 1) from colCertDiv_147_73_115.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 115 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T147_73_2 = colFn colCertDiv_147_73_115.D2 (m := 1) from colCertDiv_147_73_115.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_73_115_match


theorem leaf_147_73_120 (hp : 120 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 120 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 120 (transLenTr ⟨73, by decide⟩ 120 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 120 (transLenTr ⟨73, by decide⟩ 120 hp)) T147_73
      hfix147_73 hinj147_73 hcardT147_73
      (fun i => conj_mem_of_fixedPoints _ _ (T147_73 i) (hfix147_73 i) _)
      ⟨147, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 120 hp) Q2.T147_73_2 Q2.hfix147_73_2 Q2.hinj147_73_2
      Q2.hcardT147_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_73_2 i) (Q2.hfix147_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 120 (transLenTr ⟨73, by decide⟩ 120 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T147_73 = colFn colCertDiv_147_73_120.D1 (m := 1) from colCertDiv_147_73_120.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 120 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T147_73_2 = colFn colCertDiv_147_73_120.D2 (m := 1) from colCertDiv_147_73_120.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_73_120_match


theorem leaf_147_74_0 (hp : 0 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 0 (transLenTr ⟨74, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 0 (transLenTr ⟨74, by decide⟩ 0 hp)) T147_74
      hfix147_74 hinj147_74 hcardT147_74
      (fun i => conj_mem_of_fixedPoints _ _ (T147_74 i) (hfix147_74 i) _)
      ⟨147, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 0 hp) Q2.T147_74_2 Q2.hfix147_74_2 Q2.hinj147_74_2
      Q2.hcardT147_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_74_2 i) (Q2.hfix147_74_2 i) _)
      colCert_147_74_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_74_1 (hp : 1 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 1 (transLenTr ⟨74, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 1 (transLenTr ⟨74, by decide⟩ 1 hp)) T147_74
      hfix147_74 hinj147_74 hcardT147_74
      (fun i => conj_mem_of_fixedPoints _ _ (T147_74 i) (hfix147_74 i) _)
      ⟨147, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 1 hp) Q2.T147_74_2 Q2.hfix147_74_2 Q2.hinj147_74_2
      Q2.hcardT147_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_74_2 i) (Q2.hfix147_74_2 i) _)
      colCert_147_74_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_74_2 (hp : 2 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 2 (transLenTr ⟨74, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 2 (transLenTr ⟨74, by decide⟩ 2 hp)) T147_74
      hfix147_74 hinj147_74 hcardT147_74
      (fun i => conj_mem_of_fixedPoints _ _ (T147_74 i) (hfix147_74 i) _)
      ⟨147, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 2 hp) Q2.T147_74_2 Q2.hfix147_74_2 Q2.hinj147_74_2
      Q2.hcardT147_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_74_2 i) (Q2.hfix147_74_2 i) _)
      colCert_147_74_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_74_3 (hp : 3 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 3 (transLenTr ⟨74, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 3 (transLenTr ⟨74, by decide⟩ 3 hp)) T147_74
      hfix147_74 hinj147_74 hcardT147_74
      (fun i => conj_mem_of_fixedPoints _ _ (T147_74 i) (hfix147_74 i) _)
      ⟨147, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 3 hp) Q2.T147_74_2 Q2.hfix147_74_2 Q2.hinj147_74_2
      Q2.hcardT147_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_74_2 i) (Q2.hfix147_74_2 i) _)
      colCert_147_74_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_74_4 (hp : 4 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 4 (transLenTr ⟨74, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 4 (transLenTr ⟨74, by decide⟩ 4 hp)) T147_74
      hfix147_74 hinj147_74 hcardT147_74
      (fun i => conj_mem_of_fixedPoints _ _ (T147_74 i) (hfix147_74 i) _)
      ⟨147, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 4 hp) Q2.T147_74_2 Q2.hfix147_74_2 Q2.hinj147_74_2
      Q2.hcardT147_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_74_2 i) (Q2.hfix147_74_2 i) _)
      colCert_147_74_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_74_5 (hp : 5 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 5 (transLenTr ⟨74, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 5 (transLenTr ⟨74, by decide⟩ 5 hp)) T147_74
      hfix147_74 hinj147_74 hcardT147_74
      (fun i => conj_mem_of_fixedPoints _ _ (T147_74 i) (hfix147_74 i) _)
      ⟨147, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 5 hp) Q2.T147_74_2 Q2.hfix147_74_2 Q2.hinj147_74_2
      Q2.hcardT147_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_74_2 i) (Q2.hfix147_74_2 i) _)
      colCert_147_74_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_74_6 (hp : 6 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 6 (transLenTr ⟨74, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 6 (transLenTr ⟨74, by decide⟩ 6 hp)) T147_74
      hfix147_74 hinj147_74 hcardT147_74
      (fun i => conj_mem_of_fixedPoints _ _ (T147_74 i) (hfix147_74 i) _)
      ⟨147, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 6 hp) Q2.T147_74_2 Q2.hfix147_74_2 Q2.hinj147_74_2
      Q2.hcardT147_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_74_2 i) (Q2.hfix147_74_2 i) _)
      colCert_147_74_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_74_7 (hp : 7 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 7 (transLenTr ⟨74, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 7 (transLenTr ⟨74, by decide⟩ 7 hp)) T147_74
      hfix147_74 hinj147_74 hcardT147_74
      (fun i => conj_mem_of_fixedPoints _ _ (T147_74 i) (hfix147_74 i) _)
      ⟨147, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 7 hp) Q2.T147_74_2 Q2.hfix147_74_2 Q2.hinj147_74_2
      Q2.hcardT147_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_74_2 i) (Q2.hfix147_74_2 i) _)
      colCert_147_74_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_74_8 (hp : 8 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 8 (transLenTr ⟨74, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 8 (transLenTr ⟨74, by decide⟩ 8 hp)) T147_74
      hfix147_74 hinj147_74 hcardT147_74
      (fun i => conj_mem_of_fixedPoints _ _ (T147_74 i) (hfix147_74 i) _)
      ⟨147, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 8 hp) Q2.T147_74_2 Q2.hfix147_74_2 Q2.hinj147_74_2
      Q2.hcardT147_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_74_2 i) (Q2.hfix147_74_2 i) _)
      colCert_147_74_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_74_9 (hp : 9 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 9 (transLenTr ⟨74, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 9 (transLenTr ⟨74, by decide⟩ 9 hp)) T147_74
      hfix147_74 hinj147_74 hcardT147_74
      (fun i => conj_mem_of_fixedPoints _ _ (T147_74 i) (hfix147_74 i) _)
      ⟨147, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 9 hp) Q2.T147_74_2 Q2.hfix147_74_2 Q2.hinj147_74_2
      Q2.hcardT147_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_74_2 i) (Q2.hfix147_74_2 i) _)
      colCert_147_74_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_74_10 (hp : 10 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 10 (transLenTr ⟨74, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 10 (transLenTr ⟨74, by decide⟩ 10 hp)) T147_74
      hfix147_74 hinj147_74 hcardT147_74
      (fun i => conj_mem_of_fixedPoints _ _ (T147_74 i) (hfix147_74 i) _)
      ⟨147, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 10 hp) Q2.T147_74_2 Q2.hfix147_74_2 Q2.hinj147_74_2
      Q2.hcardT147_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_74_2 i) (Q2.hfix147_74_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨74, by decide⟩ 10 (transLenTr ⟨74, by decide⟩ 10 hp) : ↥(reps ⟨74, by decide⟩)) : Coordinate 1)
        T147_74 = colFn colCertDiv_147_74_10.D1 (m := 1) from colCertDiv_147_74_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨74, by decide⟩ 10 hp : ↥(Q2.reps ⟨74, by decide⟩)) : Coordinate 2)
        Q2.T147_74_2 = colFn colCertDiv_147_74_10.D2 (m := 1) from colCertDiv_147_74_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_74_10_match


theorem leaf_147_74_11 (hp : 11 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 11 (transLenTr ⟨74, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 11 (transLenTr ⟨74, by decide⟩ 11 hp)) T147_74
      hfix147_74 hinj147_74 hcardT147_74
      (fun i => conj_mem_of_fixedPoints _ _ (T147_74 i) (hfix147_74 i) _)
      ⟨147, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 11 hp) Q2.T147_74_2 Q2.hfix147_74_2 Q2.hinj147_74_2
      Q2.hcardT147_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_74_2 i) (Q2.hfix147_74_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨74, by decide⟩ 11 (transLenTr ⟨74, by decide⟩ 11 hp) : ↥(reps ⟨74, by decide⟩)) : Coordinate 1)
        T147_74 = colFn colCertDiv_147_74_11.D1 (m := 1) from colCertDiv_147_74_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨74, by decide⟩ 11 hp : ↥(Q2.reps ⟨74, by decide⟩)) : Coordinate 2)
        Q2.T147_74_2 = colFn colCertDiv_147_74_11.D2 (m := 1) from colCertDiv_147_74_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_74_11_match


theorem leaf_147_74_12 (hp : 12 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 12 (transLenTr ⟨74, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 12 (transLenTr ⟨74, by decide⟩ 12 hp)) T147_74
      hfix147_74 hinj147_74 hcardT147_74
      (fun i => conj_mem_of_fixedPoints _ _ (T147_74 i) (hfix147_74 i) _)
      ⟨147, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 12 hp) Q2.T147_74_2 Q2.hfix147_74_2 Q2.hinj147_74_2
      Q2.hcardT147_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_74_2 i) (Q2.hfix147_74_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨74, by decide⟩ 12 (transLenTr ⟨74, by decide⟩ 12 hp) : ↥(reps ⟨74, by decide⟩)) : Coordinate 1)
        T147_74 = colFn colCertDiv_147_74_12.D1 (m := 1) from colCertDiv_147_74_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨74, by decide⟩ 12 hp : ↥(Q2.reps ⟨74, by decide⟩)) : Coordinate 2)
        Q2.T147_74_2 = colFn colCertDiv_147_74_12.D2 (m := 1) from colCertDiv_147_74_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_74_12_match


theorem leaf_147_74_13 (hp : 13 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 13 (transLenTr ⟨74, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 13 (transLenTr ⟨74, by decide⟩ 13 hp)) T147_74
      hfix147_74 hinj147_74 hcardT147_74
      (fun i => conj_mem_of_fixedPoints _ _ (T147_74 i) (hfix147_74 i) _)
      ⟨147, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 13 hp) Q2.T147_74_2 Q2.hfix147_74_2 Q2.hinj147_74_2
      Q2.hcardT147_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_74_2 i) (Q2.hfix147_74_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨74, by decide⟩ 13 (transLenTr ⟨74, by decide⟩ 13 hp) : ↥(reps ⟨74, by decide⟩)) : Coordinate 1)
        T147_74 = colFn colCertDiv_147_74_13.D1 (m := 1) from colCertDiv_147_74_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨74, by decide⟩ 13 hp : ↥(Q2.reps ⟨74, by decide⟩)) : Coordinate 2)
        Q2.T147_74_2 = colFn colCertDiv_147_74_13.D2 (m := 1) from colCertDiv_147_74_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_74_13_match


theorem leaf_147_74_14 (hp : 14 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 14 (transLenTr ⟨74, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 14 (transLenTr ⟨74, by decide⟩ 14 hp)) T147_74
      hfix147_74 hinj147_74 hcardT147_74
      (fun i => conj_mem_of_fixedPoints _ _ (T147_74 i) (hfix147_74 i) _)
      ⟨147, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 14 hp) Q2.T147_74_2 Q2.hfix147_74_2 Q2.hinj147_74_2
      Q2.hcardT147_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_74_2 i) (Q2.hfix147_74_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨74, by decide⟩ 14 (transLenTr ⟨74, by decide⟩ 14 hp) : ↥(reps ⟨74, by decide⟩)) : Coordinate 1)
        T147_74 = colFn colCertDiv_147_74_14.D1 (m := 1) from colCertDiv_147_74_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨74, by decide⟩ 14 hp : ↥(Q2.reps ⟨74, by decide⟩)) : Coordinate 2)
        Q2.T147_74_2 = colFn colCertDiv_147_74_14.D2 (m := 1) from colCertDiv_147_74_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_74_14_match


theorem leaf_147_74_15 (hp : 15 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 15 (transLenTr ⟨74, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 15 (transLenTr ⟨74, by decide⟩ 15 hp)) T147_74
      hfix147_74 hinj147_74 hcardT147_74
      (fun i => conj_mem_of_fixedPoints _ _ (T147_74 i) (hfix147_74 i) _)
      ⟨147, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 15 hp) Q2.T147_74_2 Q2.hfix147_74_2 Q2.hinj147_74_2
      Q2.hcardT147_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_74_2 i) (Q2.hfix147_74_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨74, by decide⟩ 15 (transLenTr ⟨74, by decide⟩ 15 hp) : ↥(reps ⟨74, by decide⟩)) : Coordinate 1)
        T147_74 = colFn colCertDiv_147_74_15.D1 (m := 1) from colCertDiv_147_74_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨74, by decide⟩ 15 hp : ↥(Q2.reps ⟨74, by decide⟩)) : Coordinate 2)
        Q2.T147_74_2 = colFn colCertDiv_147_74_15.D2 (m := 1) from colCertDiv_147_74_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_74_15_match


theorem leaf_147_74_16 (hp : 16 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 16 (transLenTr ⟨74, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 16 (transLenTr ⟨74, by decide⟩ 16 hp)) T147_74
      hfix147_74 hinj147_74 hcardT147_74
      (fun i => conj_mem_of_fixedPoints _ _ (T147_74 i) (hfix147_74 i) _)
      ⟨147, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 16 hp) Q2.T147_74_2 Q2.hfix147_74_2 Q2.hinj147_74_2
      Q2.hcardT147_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_74_2 i) (Q2.hfix147_74_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨74, by decide⟩ 16 (transLenTr ⟨74, by decide⟩ 16 hp) : ↥(reps ⟨74, by decide⟩)) : Coordinate 1)
        T147_74 = colFn colCertDiv_147_74_16.D1 (m := 1) from colCertDiv_147_74_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨74, by decide⟩ 16 hp : ↥(Q2.reps ⟨74, by decide⟩)) : Coordinate 2)
        Q2.T147_74_2 = colFn colCertDiv_147_74_16.D2 (m := 1) from colCertDiv_147_74_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_74_16_match


theorem leaf_147_74_17 (hp : 17 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 17 (transLenTr ⟨74, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 17 (transLenTr ⟨74, by decide⟩ 17 hp)) T147_74
      hfix147_74 hinj147_74 hcardT147_74
      (fun i => conj_mem_of_fixedPoints _ _ (T147_74 i) (hfix147_74 i) _)
      ⟨147, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 17 hp) Q2.T147_74_2 Q2.hfix147_74_2 Q2.hinj147_74_2
      Q2.hcardT147_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_74_2 i) (Q2.hfix147_74_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨74, by decide⟩ 17 (transLenTr ⟨74, by decide⟩ 17 hp) : ↥(reps ⟨74, by decide⟩)) : Coordinate 1)
        T147_74 = colFn colCertDiv_147_74_17.D1 (m := 1) from colCertDiv_147_74_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨74, by decide⟩ 17 hp : ↥(Q2.reps ⟨74, by decide⟩)) : Coordinate 2)
        Q2.T147_74_2 = colFn colCertDiv_147_74_17.D2 (m := 1) from colCertDiv_147_74_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_74_17_match


theorem leaf_147_74_18 (hp : 18 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 18 (transLenTr ⟨74, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 18 (transLenTr ⟨74, by decide⟩ 18 hp)) T147_74
      hfix147_74 hinj147_74 hcardT147_74
      (fun i => conj_mem_of_fixedPoints _ _ (T147_74 i) (hfix147_74 i) _)
      ⟨147, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 18 hp) Q2.T147_74_2 Q2.hfix147_74_2 Q2.hinj147_74_2
      Q2.hcardT147_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_74_2 i) (Q2.hfix147_74_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨74, by decide⟩ 18 (transLenTr ⟨74, by decide⟩ 18 hp) : ↥(reps ⟨74, by decide⟩)) : Coordinate 1)
        T147_74 = colFn colCertDiv_147_74_18.D1 (m := 1) from colCertDiv_147_74_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨74, by decide⟩ 18 hp : ↥(Q2.reps ⟨74, by decide⟩)) : Coordinate 2)
        Q2.T147_74_2 = colFn colCertDiv_147_74_18.D2 (m := 1) from colCertDiv_147_74_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_74_18_match


theorem leaf_147_74_19 (hp : 19 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 19 (transLenTr ⟨74, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 19 (transLenTr ⟨74, by decide⟩ 19 hp)) T147_74
      hfix147_74 hinj147_74 hcardT147_74
      (fun i => conj_mem_of_fixedPoints _ _ (T147_74 i) (hfix147_74 i) _)
      ⟨147, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 19 hp) Q2.T147_74_2 Q2.hfix147_74_2 Q2.hinj147_74_2
      Q2.hcardT147_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_74_2 i) (Q2.hfix147_74_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨74, by decide⟩ 19 (transLenTr ⟨74, by decide⟩ 19 hp) : ↥(reps ⟨74, by decide⟩)) : Coordinate 1)
        T147_74 = colFn colCertDiv_147_74_19.D1 (m := 1) from colCertDiv_147_74_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨74, by decide⟩ 19 hp : ↥(Q2.reps ⟨74, by decide⟩)) : Coordinate 2)
        Q2.T147_74_2 = colFn colCertDiv_147_74_19.D2 (m := 1) from colCertDiv_147_74_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_74_19_match


theorem leaf_147_74_20 (hp : 20 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 20 (transLenTr ⟨74, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 20 (transLenTr ⟨74, by decide⟩ 20 hp)) T147_74
      hfix147_74 hinj147_74 hcardT147_74
      (fun i => conj_mem_of_fixedPoints _ _ (T147_74 i) (hfix147_74 i) _)
      ⟨147, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 20 hp) Q2.T147_74_2 Q2.hfix147_74_2 Q2.hinj147_74_2
      Q2.hcardT147_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_74_2 i) (Q2.hfix147_74_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨74, by decide⟩ 20 (transLenTr ⟨74, by decide⟩ 20 hp) : ↥(reps ⟨74, by decide⟩)) : Coordinate 1)
        T147_74 = colFn colCertDiv_147_74_20.D1 (m := 1) from colCertDiv_147_74_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨74, by decide⟩ 20 hp : ↥(Q2.reps ⟨74, by decide⟩)) : Coordinate 2)
        Q2.T147_74_2 = colFn colCertDiv_147_74_20.D2 (m := 1) from colCertDiv_147_74_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_74_20_match


theorem leaf_147_74_21 (hp : 21 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 21 (transLenTr ⟨74, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 21 (transLenTr ⟨74, by decide⟩ 21 hp)) T147_74
      hfix147_74 hinj147_74 hcardT147_74
      (fun i => conj_mem_of_fixedPoints _ _ (T147_74 i) (hfix147_74 i) _)
      ⟨147, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 21 hp) Q2.T147_74_2 Q2.hfix147_74_2 Q2.hinj147_74_2
      Q2.hcardT147_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_74_2 i) (Q2.hfix147_74_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨74, by decide⟩ 21 (transLenTr ⟨74, by decide⟩ 21 hp) : ↥(reps ⟨74, by decide⟩)) : Coordinate 1)
        T147_74 = colFn colCertDiv_147_74_21.D1 (m := 1) from colCertDiv_147_74_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨74, by decide⟩ 21 hp : ↥(Q2.reps ⟨74, by decide⟩)) : Coordinate 2)
        Q2.T147_74_2 = colFn colCertDiv_147_74_21.D2 (m := 1) from colCertDiv_147_74_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_74_21_match


theorem leaf_147_74_22 (hp : 22 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 22 (transLenTr ⟨74, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 22 (transLenTr ⟨74, by decide⟩ 22 hp)) T147_74
      hfix147_74 hinj147_74 hcardT147_74
      (fun i => conj_mem_of_fixedPoints _ _ (T147_74 i) (hfix147_74 i) _)
      ⟨147, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 22 hp) Q2.T147_74_2 Q2.hfix147_74_2 Q2.hinj147_74_2
      Q2.hcardT147_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_74_2 i) (Q2.hfix147_74_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨74, by decide⟩ 22 (transLenTr ⟨74, by decide⟩ 22 hp) : ↥(reps ⟨74, by decide⟩)) : Coordinate 1)
        T147_74 = colFn colCertDiv_147_74_22.D1 (m := 1) from colCertDiv_147_74_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨74, by decide⟩ 22 hp : ↥(Q2.reps ⟨74, by decide⟩)) : Coordinate 2)
        Q2.T147_74_2 = colFn colCertDiv_147_74_22.D2 (m := 1) from colCertDiv_147_74_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_74_22_match


theorem leaf_147_74_23 (hp : 23 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 23 (transLenTr ⟨74, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 23 (transLenTr ⟨74, by decide⟩ 23 hp)) T147_74
      hfix147_74 hinj147_74 hcardT147_74
      (fun i => conj_mem_of_fixedPoints _ _ (T147_74 i) (hfix147_74 i) _)
      ⟨147, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 23 hp) Q2.T147_74_2 Q2.hfix147_74_2 Q2.hinj147_74_2
      Q2.hcardT147_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_74_2 i) (Q2.hfix147_74_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨74, by decide⟩ 23 (transLenTr ⟨74, by decide⟩ 23 hp) : ↥(reps ⟨74, by decide⟩)) : Coordinate 1)
        T147_74 = colFn colCertDiv_147_74_23.D1 (m := 1) from colCertDiv_147_74_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨74, by decide⟩ 23 hp : ↥(Q2.reps ⟨74, by decide⟩)) : Coordinate 2)
        Q2.T147_74_2 = colFn colCertDiv_147_74_23.D2 (m := 1) from colCertDiv_147_74_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_74_23_match


theorem leaf_147_74_24 (hp : 24 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 24 (transLenTr ⟨74, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 24 (transLenTr ⟨74, by decide⟩ 24 hp)) T147_74
      hfix147_74 hinj147_74 hcardT147_74
      (fun i => conj_mem_of_fixedPoints _ _ (T147_74 i) (hfix147_74 i) _)
      ⟨147, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 24 hp) Q2.T147_74_2 Q2.hfix147_74_2 Q2.hinj147_74_2
      Q2.hcardT147_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_74_2 i) (Q2.hfix147_74_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨74, by decide⟩ 24 (transLenTr ⟨74, by decide⟩ 24 hp) : ↥(reps ⟨74, by decide⟩)) : Coordinate 1)
        T147_74 = colFn colCertDiv_147_74_24.D1 (m := 1) from colCertDiv_147_74_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨74, by decide⟩ 24 hp : ↥(Q2.reps ⟨74, by decide⟩)) : Coordinate 2)
        Q2.T147_74_2 = colFn colCertDiv_147_74_24.D2 (m := 1) from colCertDiv_147_74_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_74_24_match


theorem leaf_147_75_0 (hp : 0 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 0 (transLenTr ⟨75, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 0 (transLenTr ⟨75, by decide⟩ 0 hp)) T147_75
      hfix147_75 hinj147_75 hcardT147_75
      (fun i => conj_mem_of_fixedPoints _ _ (T147_75 i) (hfix147_75 i) _)
      ⟨147, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 0 hp) Q2.T147_75_2 Q2.hfix147_75_2 Q2.hinj147_75_2
      Q2.hcardT147_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_75_2 i) (Q2.hfix147_75_2 i) _)
      colCert_147_75_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_75_1 (hp : 1 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 1 (transLenTr ⟨75, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 1 (transLenTr ⟨75, by decide⟩ 1 hp)) T147_75
      hfix147_75 hinj147_75 hcardT147_75
      (fun i => conj_mem_of_fixedPoints _ _ (T147_75 i) (hfix147_75 i) _)
      ⟨147, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 1 hp) Q2.T147_75_2 Q2.hfix147_75_2 Q2.hinj147_75_2
      Q2.hcardT147_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_75_2 i) (Q2.hfix147_75_2 i) _)
      colCert_147_75_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_75_2 (hp : 2 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 2 (transLenTr ⟨75, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 2 (transLenTr ⟨75, by decide⟩ 2 hp)) T147_75
      hfix147_75 hinj147_75 hcardT147_75
      (fun i => conj_mem_of_fixedPoints _ _ (T147_75 i) (hfix147_75 i) _)
      ⟨147, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 2 hp) Q2.T147_75_2 Q2.hfix147_75_2 Q2.hinj147_75_2
      Q2.hcardT147_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_75_2 i) (Q2.hfix147_75_2 i) _)
      colCert_147_75_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_75_3 (hp : 3 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 3 (transLenTr ⟨75, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 3 (transLenTr ⟨75, by decide⟩ 3 hp)) T147_75
      hfix147_75 hinj147_75 hcardT147_75
      (fun i => conj_mem_of_fixedPoints _ _ (T147_75 i) (hfix147_75 i) _)
      ⟨147, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 3 hp) Q2.T147_75_2 Q2.hfix147_75_2 Q2.hinj147_75_2
      Q2.hcardT147_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_75_2 i) (Q2.hfix147_75_2 i) _)
      colCert_147_75_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_75_4 (hp : 4 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 4 (transLenTr ⟨75, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 4 (transLenTr ⟨75, by decide⟩ 4 hp)) T147_75
      hfix147_75 hinj147_75 hcardT147_75
      (fun i => conj_mem_of_fixedPoints _ _ (T147_75 i) (hfix147_75 i) _)
      ⟨147, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 4 hp) Q2.T147_75_2 Q2.hfix147_75_2 Q2.hinj147_75_2
      Q2.hcardT147_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_75_2 i) (Q2.hfix147_75_2 i) _)
      colCert_147_75_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_75_5 (hp : 5 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 5 (transLenTr ⟨75, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 5 (transLenTr ⟨75, by decide⟩ 5 hp)) T147_75
      hfix147_75 hinj147_75 hcardT147_75
      (fun i => conj_mem_of_fixedPoints _ _ (T147_75 i) (hfix147_75 i) _)
      ⟨147, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 5 hp) Q2.T147_75_2 Q2.hfix147_75_2 Q2.hinj147_75_2
      Q2.hcardT147_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_75_2 i) (Q2.hfix147_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 5 (transLenTr ⟨75, by decide⟩ 5 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T147_75 = colFn colCertDiv_147_75_5.D1 (m := 1) from colCertDiv_147_75_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 5 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T147_75_2 = colFn colCertDiv_147_75_5.D2 (m := 1) from colCertDiv_147_75_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_75_5_match


theorem leaf_147_75_6 (hp : 6 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 6 (transLenTr ⟨75, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 6 (transLenTr ⟨75, by decide⟩ 6 hp)) T147_75
      hfix147_75 hinj147_75 hcardT147_75
      (fun i => conj_mem_of_fixedPoints _ _ (T147_75 i) (hfix147_75 i) _)
      ⟨147, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 6 hp) Q2.T147_75_2 Q2.hfix147_75_2 Q2.hinj147_75_2
      Q2.hcardT147_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_75_2 i) (Q2.hfix147_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 6 (transLenTr ⟨75, by decide⟩ 6 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T147_75 = colFn colCertDiv_147_75_6.D1 (m := 1) from colCertDiv_147_75_6.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 6 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T147_75_2 = colFn colCertDiv_147_75_6.D2 (m := 1) from colCertDiv_147_75_6.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_75_6_match


theorem leaf_147_75_7 (hp : 7 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 7 (transLenTr ⟨75, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 7 (transLenTr ⟨75, by decide⟩ 7 hp)) T147_75
      hfix147_75 hinj147_75 hcardT147_75
      (fun i => conj_mem_of_fixedPoints _ _ (T147_75 i) (hfix147_75 i) _)
      ⟨147, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 7 hp) Q2.T147_75_2 Q2.hfix147_75_2 Q2.hinj147_75_2
      Q2.hcardT147_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_75_2 i) (Q2.hfix147_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 7 (transLenTr ⟨75, by decide⟩ 7 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T147_75 = colFn colCertDiv_147_75_7.D1 (m := 1) from colCertDiv_147_75_7.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 7 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T147_75_2 = colFn colCertDiv_147_75_7.D2 (m := 1) from colCertDiv_147_75_7.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_75_7_match


theorem leaf_147_75_8 (hp : 8 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 8 (transLenTr ⟨75, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 8 (transLenTr ⟨75, by decide⟩ 8 hp)) T147_75
      hfix147_75 hinj147_75 hcardT147_75
      (fun i => conj_mem_of_fixedPoints _ _ (T147_75 i) (hfix147_75 i) _)
      ⟨147, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 8 hp) Q2.T147_75_2 Q2.hfix147_75_2 Q2.hinj147_75_2
      Q2.hcardT147_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_75_2 i) (Q2.hfix147_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 8 (transLenTr ⟨75, by decide⟩ 8 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T147_75 = colFn colCertDiv_147_75_8.D1 (m := 1) from colCertDiv_147_75_8.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 8 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T147_75_2 = colFn colCertDiv_147_75_8.D2 (m := 1) from colCertDiv_147_75_8.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_75_8_match


theorem leaf_147_75_9 (hp : 9 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 9 (transLenTr ⟨75, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 9 (transLenTr ⟨75, by decide⟩ 9 hp)) T147_75
      hfix147_75 hinj147_75 hcardT147_75
      (fun i => conj_mem_of_fixedPoints _ _ (T147_75 i) (hfix147_75 i) _)
      ⟨147, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 9 hp) Q2.T147_75_2 Q2.hfix147_75_2 Q2.hinj147_75_2
      Q2.hcardT147_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_75_2 i) (Q2.hfix147_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 9 (transLenTr ⟨75, by decide⟩ 9 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T147_75 = colFn colCertDiv_147_75_9.D1 (m := 1) from colCertDiv_147_75_9.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 9 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T147_75_2 = colFn colCertDiv_147_75_9.D2 (m := 1) from colCertDiv_147_75_9.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_75_9_match


theorem leaf_147_75_10 (hp : 10 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 10 (transLenTr ⟨75, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 10 (transLenTr ⟨75, by decide⟩ 10 hp)) T147_75
      hfix147_75 hinj147_75 hcardT147_75
      (fun i => conj_mem_of_fixedPoints _ _ (T147_75 i) (hfix147_75 i) _)
      ⟨147, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 10 hp) Q2.T147_75_2 Q2.hfix147_75_2 Q2.hinj147_75_2
      Q2.hcardT147_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_75_2 i) (Q2.hfix147_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 10 (transLenTr ⟨75, by decide⟩ 10 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T147_75 = colFn colCertDiv_147_75_10.D1 (m := 1) from colCertDiv_147_75_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 10 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T147_75_2 = colFn colCertDiv_147_75_10.D2 (m := 1) from colCertDiv_147_75_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_75_10_match


theorem leaf_147_75_11 (hp : 11 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 11 (transLenTr ⟨75, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 11 (transLenTr ⟨75, by decide⟩ 11 hp)) T147_75
      hfix147_75 hinj147_75 hcardT147_75
      (fun i => conj_mem_of_fixedPoints _ _ (T147_75 i) (hfix147_75 i) _)
      ⟨147, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 11 hp) Q2.T147_75_2 Q2.hfix147_75_2 Q2.hinj147_75_2
      Q2.hcardT147_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_75_2 i) (Q2.hfix147_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 11 (transLenTr ⟨75, by decide⟩ 11 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T147_75 = colFn colCertDiv_147_75_11.D1 (m := 1) from colCertDiv_147_75_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 11 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T147_75_2 = colFn colCertDiv_147_75_11.D2 (m := 1) from colCertDiv_147_75_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_75_11_match


theorem leaf_147_75_12 (hp : 12 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 12 (transLenTr ⟨75, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 12 (transLenTr ⟨75, by decide⟩ 12 hp)) T147_75
      hfix147_75 hinj147_75 hcardT147_75
      (fun i => conj_mem_of_fixedPoints _ _ (T147_75 i) (hfix147_75 i) _)
      ⟨147, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 12 hp) Q2.T147_75_2 Q2.hfix147_75_2 Q2.hinj147_75_2
      Q2.hcardT147_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_75_2 i) (Q2.hfix147_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 12 (transLenTr ⟨75, by decide⟩ 12 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T147_75 = colFn colCertDiv_147_75_12.D1 (m := 1) from colCertDiv_147_75_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 12 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T147_75_2 = colFn colCertDiv_147_75_12.D2 (m := 1) from colCertDiv_147_75_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_75_12_match


theorem leaf_147_75_13 (hp : 13 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 13 (transLenTr ⟨75, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 13 (transLenTr ⟨75, by decide⟩ 13 hp)) T147_75
      hfix147_75 hinj147_75 hcardT147_75
      (fun i => conj_mem_of_fixedPoints _ _ (T147_75 i) (hfix147_75 i) _)
      ⟨147, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 13 hp) Q2.T147_75_2 Q2.hfix147_75_2 Q2.hinj147_75_2
      Q2.hcardT147_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_75_2 i) (Q2.hfix147_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 13 (transLenTr ⟨75, by decide⟩ 13 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T147_75 = colFn colCertDiv_147_75_13.D1 (m := 1) from colCertDiv_147_75_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 13 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T147_75_2 = colFn colCertDiv_147_75_13.D2 (m := 1) from colCertDiv_147_75_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_75_13_match


theorem leaf_147_75_14 (hp : 14 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 14 (transLenTr ⟨75, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 14 (transLenTr ⟨75, by decide⟩ 14 hp)) T147_75
      hfix147_75 hinj147_75 hcardT147_75
      (fun i => conj_mem_of_fixedPoints _ _ (T147_75 i) (hfix147_75 i) _)
      ⟨147, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 14 hp) Q2.T147_75_2 Q2.hfix147_75_2 Q2.hinj147_75_2
      Q2.hcardT147_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_75_2 i) (Q2.hfix147_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 14 (transLenTr ⟨75, by decide⟩ 14 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T147_75 = colFn colCertDiv_147_75_14.D1 (m := 1) from colCertDiv_147_75_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 14 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T147_75_2 = colFn colCertDiv_147_75_14.D2 (m := 1) from colCertDiv_147_75_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_75_14_match


theorem leaf_147_75_15 (hp : 15 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 15 (transLenTr ⟨75, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 15 (transLenTr ⟨75, by decide⟩ 15 hp)) T147_75
      hfix147_75 hinj147_75 hcardT147_75
      (fun i => conj_mem_of_fixedPoints _ _ (T147_75 i) (hfix147_75 i) _)
      ⟨147, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 15 hp) Q2.T147_75_2 Q2.hfix147_75_2 Q2.hinj147_75_2
      Q2.hcardT147_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_75_2 i) (Q2.hfix147_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 15 (transLenTr ⟨75, by decide⟩ 15 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T147_75 = colFn colCertDiv_147_75_15.D1 (m := 1) from colCertDiv_147_75_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 15 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T147_75_2 = colFn colCertDiv_147_75_15.D2 (m := 1) from colCertDiv_147_75_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_75_15_match


theorem leaf_147_75_16 (hp : 16 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 16 (transLenTr ⟨75, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 16 (transLenTr ⟨75, by decide⟩ 16 hp)) T147_75
      hfix147_75 hinj147_75 hcardT147_75
      (fun i => conj_mem_of_fixedPoints _ _ (T147_75 i) (hfix147_75 i) _)
      ⟨147, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 16 hp) Q2.T147_75_2 Q2.hfix147_75_2 Q2.hinj147_75_2
      Q2.hcardT147_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_75_2 i) (Q2.hfix147_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 16 (transLenTr ⟨75, by decide⟩ 16 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T147_75 = colFn colCertDiv_147_75_16.D1 (m := 1) from colCertDiv_147_75_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 16 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T147_75_2 = colFn colCertDiv_147_75_16.D2 (m := 1) from colCertDiv_147_75_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_75_16_match


theorem leaf_147_75_17 (hp : 17 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 17 (transLenTr ⟨75, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 17 (transLenTr ⟨75, by decide⟩ 17 hp)) T147_75
      hfix147_75 hinj147_75 hcardT147_75
      (fun i => conj_mem_of_fixedPoints _ _ (T147_75 i) (hfix147_75 i) _)
      ⟨147, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 17 hp) Q2.T147_75_2 Q2.hfix147_75_2 Q2.hinj147_75_2
      Q2.hcardT147_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_75_2 i) (Q2.hfix147_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 17 (transLenTr ⟨75, by decide⟩ 17 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T147_75 = colFn colCertDiv_147_75_17.D1 (m := 1) from colCertDiv_147_75_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 17 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T147_75_2 = colFn colCertDiv_147_75_17.D2 (m := 1) from colCertDiv_147_75_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_75_17_match


theorem leaf_147_75_18 (hp : 18 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 18 (transLenTr ⟨75, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 18 (transLenTr ⟨75, by decide⟩ 18 hp)) T147_75
      hfix147_75 hinj147_75 hcardT147_75
      (fun i => conj_mem_of_fixedPoints _ _ (T147_75 i) (hfix147_75 i) _)
      ⟨147, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 18 hp) Q2.T147_75_2 Q2.hfix147_75_2 Q2.hinj147_75_2
      Q2.hcardT147_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_75_2 i) (Q2.hfix147_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 18 (transLenTr ⟨75, by decide⟩ 18 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T147_75 = colFn colCertDiv_147_75_18.D1 (m := 1) from colCertDiv_147_75_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 18 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T147_75_2 = colFn colCertDiv_147_75_18.D2 (m := 1) from colCertDiv_147_75_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_75_18_match


theorem leaf_147_75_19 (hp : 19 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 19 (transLenTr ⟨75, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 19 (transLenTr ⟨75, by decide⟩ 19 hp)) T147_75
      hfix147_75 hinj147_75 hcardT147_75
      (fun i => conj_mem_of_fixedPoints _ _ (T147_75 i) (hfix147_75 i) _)
      ⟨147, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 19 hp) Q2.T147_75_2 Q2.hfix147_75_2 Q2.hinj147_75_2
      Q2.hcardT147_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_75_2 i) (Q2.hfix147_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 19 (transLenTr ⟨75, by decide⟩ 19 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T147_75 = colFn colCertDiv_147_75_19.D1 (m := 1) from colCertDiv_147_75_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 19 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T147_75_2 = colFn colCertDiv_147_75_19.D2 (m := 1) from colCertDiv_147_75_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_75_19_match


theorem leaf_147_75_20 (hp : 20 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 20 (transLenTr ⟨75, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 20 (transLenTr ⟨75, by decide⟩ 20 hp)) T147_75
      hfix147_75 hinj147_75 hcardT147_75
      (fun i => conj_mem_of_fixedPoints _ _ (T147_75 i) (hfix147_75 i) _)
      ⟨147, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 20 hp) Q2.T147_75_2 Q2.hfix147_75_2 Q2.hinj147_75_2
      Q2.hcardT147_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_75_2 i) (Q2.hfix147_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 20 (transLenTr ⟨75, by decide⟩ 20 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T147_75 = colFn colCertDiv_147_75_20.D1 (m := 1) from colCertDiv_147_75_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 20 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T147_75_2 = colFn colCertDiv_147_75_20.D2 (m := 1) from colCertDiv_147_75_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_75_20_match


theorem leaf_147_75_21 (hp : 21 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 21 (transLenTr ⟨75, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 21 (transLenTr ⟨75, by decide⟩ 21 hp)) T147_75
      hfix147_75 hinj147_75 hcardT147_75
      (fun i => conj_mem_of_fixedPoints _ _ (T147_75 i) (hfix147_75 i) _)
      ⟨147, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 21 hp) Q2.T147_75_2 Q2.hfix147_75_2 Q2.hinj147_75_2
      Q2.hcardT147_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_75_2 i) (Q2.hfix147_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 21 (transLenTr ⟨75, by decide⟩ 21 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T147_75 = colFn colCertDiv_147_75_21.D1 (m := 1) from colCertDiv_147_75_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 21 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T147_75_2 = colFn colCertDiv_147_75_21.D2 (m := 1) from colCertDiv_147_75_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_75_21_match


theorem leaf_147_75_22 (hp : 22 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 22 (transLenTr ⟨75, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 22 (transLenTr ⟨75, by decide⟩ 22 hp)) T147_75
      hfix147_75 hinj147_75 hcardT147_75
      (fun i => conj_mem_of_fixedPoints _ _ (T147_75 i) (hfix147_75 i) _)
      ⟨147, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 22 hp) Q2.T147_75_2 Q2.hfix147_75_2 Q2.hinj147_75_2
      Q2.hcardT147_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_75_2 i) (Q2.hfix147_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 22 (transLenTr ⟨75, by decide⟩ 22 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T147_75 = colFn colCertDiv_147_75_22.D1 (m := 1) from colCertDiv_147_75_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 22 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T147_75_2 = colFn colCertDiv_147_75_22.D2 (m := 1) from colCertDiv_147_75_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_75_22_match


theorem leaf_147_75_23 (hp : 23 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 23 (transLenTr ⟨75, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 23 (transLenTr ⟨75, by decide⟩ 23 hp)) T147_75
      hfix147_75 hinj147_75 hcardT147_75
      (fun i => conj_mem_of_fixedPoints _ _ (T147_75 i) (hfix147_75 i) _)
      ⟨147, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 23 hp) Q2.T147_75_2 Q2.hfix147_75_2 Q2.hinj147_75_2
      Q2.hcardT147_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_75_2 i) (Q2.hfix147_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 23 (transLenTr ⟨75, by decide⟩ 23 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T147_75 = colFn colCertDiv_147_75_23.D1 (m := 1) from colCertDiv_147_75_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 23 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T147_75_2 = colFn colCertDiv_147_75_23.D2 (m := 1) from colCertDiv_147_75_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_75_23_match


theorem leaf_147_75_24 (hp : 24 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 24 (transLenTr ⟨75, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 24 (transLenTr ⟨75, by decide⟩ 24 hp)) T147_75
      hfix147_75 hinj147_75 hcardT147_75
      (fun i => conj_mem_of_fixedPoints _ _ (T147_75 i) (hfix147_75 i) _)
      ⟨147, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 24 hp) Q2.T147_75_2 Q2.hfix147_75_2 Q2.hinj147_75_2
      Q2.hcardT147_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_75_2 i) (Q2.hfix147_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 24 (transLenTr ⟨75, by decide⟩ 24 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T147_75 = colFn colCertDiv_147_75_24.D1 (m := 1) from colCertDiv_147_75_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 24 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T147_75_2 = colFn colCertDiv_147_75_24.D2 (m := 1) from colCertDiv_147_75_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_75_24_match


theorem leaf_147_76_0 (hp : 0 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 0 (transLenTr ⟨76, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 0 (transLenTr ⟨76, by decide⟩ 0 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 0 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      colCert_147_76_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_76_1 (hp : 1 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 1 (transLenTr ⟨76, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 1 (transLenTr ⟨76, by decide⟩ 1 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 1 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      colCert_147_76_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_76_2 (hp : 2 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 2 (transLenTr ⟨76, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 2 (transLenTr ⟨76, by decide⟩ 2 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 2 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      colCert_147_76_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_76_3 (hp : 3 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 3 (transLenTr ⟨76, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 3 (transLenTr ⟨76, by decide⟩ 3 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 3 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      colCert_147_76_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_76_4 (hp : 4 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 4 (transLenTr ⟨76, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 4 (transLenTr ⟨76, by decide⟩ 4 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 4 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      colCert_147_76_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_76_5 (hp : 5 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 5 (transLenTr ⟨76, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 5 (transLenTr ⟨76, by decide⟩ 5 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 5 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      colCert_147_76_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_76_6 (hp : 6 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 6 (transLenTr ⟨76, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 6 (transLenTr ⟨76, by decide⟩ 6 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 6 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      colCert_147_76_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_76_7 (hp : 7 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 7 (transLenTr ⟨76, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 7 (transLenTr ⟨76, by decide⟩ 7 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 7 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      colCert_147_76_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_76_8 (hp : 8 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 8 (transLenTr ⟨76, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 8 (transLenTr ⟨76, by decide⟩ 8 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 8 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      colCert_147_76_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_76_9 (hp : 9 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 9 (transLenTr ⟨76, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 9 (transLenTr ⟨76, by decide⟩ 9 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 9 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      colCert_147_76_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_76_10 (hp : 10 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 10 (transLenTr ⟨76, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 10 (transLenTr ⟨76, by decide⟩ 10 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 10 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      colCert_147_76_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_76_11 (hp : 11 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 11 (transLenTr ⟨76, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 11 (transLenTr ⟨76, by decide⟩ 11 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 11 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      colCert_147_76_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_76_12 (hp : 12 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 12 (transLenTr ⟨76, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 12 (transLenTr ⟨76, by decide⟩ 12 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 12 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      colCert_147_76_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_76_13 (hp : 13 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 13 (transLenTr ⟨76, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 13 (transLenTr ⟨76, by decide⟩ 13 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 13 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      colCert_147_76_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_76_14 (hp : 14 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 14 (transLenTr ⟨76, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 14 (transLenTr ⟨76, by decide⟩ 14 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 14 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      colCert_147_76_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_76_15 (hp : 15 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 15 (transLenTr ⟨76, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 15 (transLenTr ⟨76, by decide⟩ 15 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 15 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      colCert_147_76_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_76_16 (hp : 16 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 16 (transLenTr ⟨76, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 16 (transLenTr ⟨76, by decide⟩ 16 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 16 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      colCert_147_76_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_76_17 (hp : 17 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 17 (transLenTr ⟨76, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 17 (transLenTr ⟨76, by decide⟩ 17 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 17 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      colCert_147_76_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_76_18 (hp : 18 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 18 (transLenTr ⟨76, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 18 (transLenTr ⟨76, by decide⟩ 18 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 18 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      colCert_147_76_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_76_19 (hp : 19 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 19 (transLenTr ⟨76, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 19 (transLenTr ⟨76, by decide⟩ 19 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 19 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      colCert_147_76_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_76_20 (hp : 20 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 20 (transLenTr ⟨76, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 20 (transLenTr ⟨76, by decide⟩ 20 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 20 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      colCert_147_76_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_76_21 (hp : 21 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 21 (transLenTr ⟨76, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 21 (transLenTr ⟨76, by decide⟩ 21 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 21 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      colCert_147_76_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_76_22 (hp : 22 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 22 (transLenTr ⟨76, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 22 (transLenTr ⟨76, by decide⟩ 22 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 22 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      colCert_147_76_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_76_23 (hp : 23 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 23 (transLenTr ⟨76, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 23 (transLenTr ⟨76, by decide⟩ 23 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 23 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      colCert_147_76_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_76_24 (hp : 24 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 24 (transLenTr ⟨76, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 24 (transLenTr ⟨76, by decide⟩ 24 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 24 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      colCert_147_76_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_76_25 (hp : 25 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 25 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 25 (transLenTr ⟨76, by decide⟩ 25 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 25 (transLenTr ⟨76, by decide⟩ 25 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 25 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 25 (transLenTr ⟨76, by decide⟩ 25 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T147_76 = colFn colCertDiv_147_76_25.D1 (m := 1) from colCertDiv_147_76_25.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 25 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T147_76_2 = colFn colCertDiv_147_76_25.D2 (m := 1) from colCertDiv_147_76_25.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_76_25_match


theorem leaf_147_76_30 (hp : 30 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 30 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 30 (transLenTr ⟨76, by decide⟩ 30 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 30 (transLenTr ⟨76, by decide⟩ 30 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 30 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 30 (transLenTr ⟨76, by decide⟩ 30 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T147_76 = colFn colCertDiv_147_76_30.D1 (m := 1) from colCertDiv_147_76_30.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 30 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T147_76_2 = colFn colCertDiv_147_76_30.D2 (m := 1) from colCertDiv_147_76_30.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_76_30_match


theorem leaf_147_76_35 (hp : 35 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 35 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 35 (transLenTr ⟨76, by decide⟩ 35 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 35 (transLenTr ⟨76, by decide⟩ 35 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 35 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 35 (transLenTr ⟨76, by decide⟩ 35 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T147_76 = colFn colCertDiv_147_76_35.D1 (m := 1) from colCertDiv_147_76_35.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 35 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T147_76_2 = colFn colCertDiv_147_76_35.D2 (m := 1) from colCertDiv_147_76_35.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_76_35_match


theorem leaf_147_76_40 (hp : 40 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 40 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 40 (transLenTr ⟨76, by decide⟩ 40 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 40 (transLenTr ⟨76, by decide⟩ 40 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 40 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 40 (transLenTr ⟨76, by decide⟩ 40 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T147_76 = colFn colCertDiv_147_76_40.D1 (m := 1) from colCertDiv_147_76_40.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 40 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T147_76_2 = colFn colCertDiv_147_76_40.D2 (m := 1) from colCertDiv_147_76_40.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_76_40_match


theorem leaf_147_76_45 (hp : 45 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 45 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 45 (transLenTr ⟨76, by decide⟩ 45 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 45 (transLenTr ⟨76, by decide⟩ 45 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 45 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 45 (transLenTr ⟨76, by decide⟩ 45 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T147_76 = colFn colCertDiv_147_76_45.D1 (m := 1) from colCertDiv_147_76_45.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 45 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T147_76_2 = colFn colCertDiv_147_76_45.D2 (m := 1) from colCertDiv_147_76_45.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_76_45_match


theorem leaf_147_76_50 (hp : 50 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 50 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 50 (transLenTr ⟨76, by decide⟩ 50 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 50 (transLenTr ⟨76, by decide⟩ 50 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 50 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 50 (transLenTr ⟨76, by decide⟩ 50 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T147_76 = colFn colCertDiv_147_76_50.D1 (m := 1) from colCertDiv_147_76_50.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 50 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T147_76_2 = colFn colCertDiv_147_76_50.D2 (m := 1) from colCertDiv_147_76_50.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_76_50_match


theorem leaf_147_76_55 (hp : 55 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 55 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 55 (transLenTr ⟨76, by decide⟩ 55 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 55 (transLenTr ⟨76, by decide⟩ 55 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 55 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 55 (transLenTr ⟨76, by decide⟩ 55 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T147_76 = colFn colCertDiv_147_76_55.D1 (m := 1) from colCertDiv_147_76_55.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 55 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T147_76_2 = colFn colCertDiv_147_76_55.D2 (m := 1) from colCertDiv_147_76_55.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_76_55_match


theorem leaf_147_76_60 (hp : 60 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 60 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 60 (transLenTr ⟨76, by decide⟩ 60 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 60 (transLenTr ⟨76, by decide⟩ 60 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 60 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 60 (transLenTr ⟨76, by decide⟩ 60 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T147_76 = colFn colCertDiv_147_76_60.D1 (m := 1) from colCertDiv_147_76_60.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 60 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T147_76_2 = colFn colCertDiv_147_76_60.D2 (m := 1) from colCertDiv_147_76_60.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_76_60_match


theorem leaf_147_76_65 (hp : 65 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 65 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 65 (transLenTr ⟨76, by decide⟩ 65 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 65 (transLenTr ⟨76, by decide⟩ 65 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 65 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 65 (transLenTr ⟨76, by decide⟩ 65 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T147_76 = colFn colCertDiv_147_76_65.D1 (m := 1) from colCertDiv_147_76_65.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 65 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T147_76_2 = colFn colCertDiv_147_76_65.D2 (m := 1) from colCertDiv_147_76_65.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_76_65_match


theorem leaf_147_76_70 (hp : 70 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 70 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 70 (transLenTr ⟨76, by decide⟩ 70 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 70 (transLenTr ⟨76, by decide⟩ 70 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 70 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 70 (transLenTr ⟨76, by decide⟩ 70 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T147_76 = colFn colCertDiv_147_76_70.D1 (m := 1) from colCertDiv_147_76_70.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 70 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T147_76_2 = colFn colCertDiv_147_76_70.D2 (m := 1) from colCertDiv_147_76_70.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_76_70_match


theorem leaf_147_76_75 (hp : 75 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 75 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 75 (transLenTr ⟨76, by decide⟩ 75 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 75 (transLenTr ⟨76, by decide⟩ 75 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 75 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 75 (transLenTr ⟨76, by decide⟩ 75 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T147_76 = colFn colCertDiv_147_76_75.D1 (m := 1) from colCertDiv_147_76_75.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 75 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T147_76_2 = colFn colCertDiv_147_76_75.D2 (m := 1) from colCertDiv_147_76_75.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_76_75_match


theorem leaf_147_76_80 (hp : 80 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 80 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 80 (transLenTr ⟨76, by decide⟩ 80 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 80 (transLenTr ⟨76, by decide⟩ 80 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 80 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 80 (transLenTr ⟨76, by decide⟩ 80 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T147_76 = colFn colCertDiv_147_76_80.D1 (m := 1) from colCertDiv_147_76_80.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 80 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T147_76_2 = colFn colCertDiv_147_76_80.D2 (m := 1) from colCertDiv_147_76_80.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_76_80_match


theorem leaf_147_76_85 (hp : 85 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 85 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 85 (transLenTr ⟨76, by decide⟩ 85 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 85 (transLenTr ⟨76, by decide⟩ 85 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 85 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 85 (transLenTr ⟨76, by decide⟩ 85 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T147_76 = colFn colCertDiv_147_76_85.D1 (m := 1) from colCertDiv_147_76_85.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 85 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T147_76_2 = colFn colCertDiv_147_76_85.D2 (m := 1) from colCertDiv_147_76_85.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_76_85_match


theorem leaf_147_76_90 (hp : 90 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 90 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 90 (transLenTr ⟨76, by decide⟩ 90 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 90 (transLenTr ⟨76, by decide⟩ 90 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 90 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 90 (transLenTr ⟨76, by decide⟩ 90 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T147_76 = colFn colCertDiv_147_76_90.D1 (m := 1) from colCertDiv_147_76_90.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 90 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T147_76_2 = colFn colCertDiv_147_76_90.D2 (m := 1) from colCertDiv_147_76_90.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_76_90_match


theorem leaf_147_76_95 (hp : 95 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 95 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 95 (transLenTr ⟨76, by decide⟩ 95 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 95 (transLenTr ⟨76, by decide⟩ 95 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 95 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 95 (transLenTr ⟨76, by decide⟩ 95 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T147_76 = colFn colCertDiv_147_76_95.D1 (m := 1) from colCertDiv_147_76_95.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 95 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T147_76_2 = colFn colCertDiv_147_76_95.D2 (m := 1) from colCertDiv_147_76_95.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_76_95_match


theorem leaf_147_76_100 (hp : 100 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 100 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 100 (transLenTr ⟨76, by decide⟩ 100 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 100 (transLenTr ⟨76, by decide⟩ 100 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 100 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 100 (transLenTr ⟨76, by decide⟩ 100 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T147_76 = colFn colCertDiv_147_76_100.D1 (m := 1) from colCertDiv_147_76_100.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 100 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T147_76_2 = colFn colCertDiv_147_76_100.D2 (m := 1) from colCertDiv_147_76_100.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_76_100_match


theorem leaf_147_76_105 (hp : 105 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 105 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 105 (transLenTr ⟨76, by decide⟩ 105 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 105 (transLenTr ⟨76, by decide⟩ 105 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 105 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 105 (transLenTr ⟨76, by decide⟩ 105 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T147_76 = colFn colCertDiv_147_76_105.D1 (m := 1) from colCertDiv_147_76_105.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 105 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T147_76_2 = colFn colCertDiv_147_76_105.D2 (m := 1) from colCertDiv_147_76_105.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_76_105_match


theorem leaf_147_76_110 (hp : 110 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 110 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 110 (transLenTr ⟨76, by decide⟩ 110 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 110 (transLenTr ⟨76, by decide⟩ 110 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 110 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 110 (transLenTr ⟨76, by decide⟩ 110 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T147_76 = colFn colCertDiv_147_76_110.D1 (m := 1) from colCertDiv_147_76_110.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 110 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T147_76_2 = colFn colCertDiv_147_76_110.D2 (m := 1) from colCertDiv_147_76_110.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_76_110_match


theorem leaf_147_76_115 (hp : 115 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 115 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 115 (transLenTr ⟨76, by decide⟩ 115 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 115 (transLenTr ⟨76, by decide⟩ 115 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 115 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 115 (transLenTr ⟨76, by decide⟩ 115 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T147_76 = colFn colCertDiv_147_76_115.D1 (m := 1) from colCertDiv_147_76_115.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 115 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T147_76_2 = colFn colCertDiv_147_76_115.D2 (m := 1) from colCertDiv_147_76_115.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_76_115_match


theorem leaf_147_76_120 (hp : 120 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 120 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 120 (transLenTr ⟨76, by decide⟩ 120 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 120 (transLenTr ⟨76, by decide⟩ 120 hp)) T147_76
      hfix147_76 hinj147_76 hcardT147_76
      (fun i => conj_mem_of_fixedPoints _ _ (T147_76 i) (hfix147_76 i) _)
      ⟨147, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 120 hp) Q2.T147_76_2 Q2.hfix147_76_2 Q2.hinj147_76_2
      Q2.hcardT147_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_76_2 i) (Q2.hfix147_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 120 (transLenTr ⟨76, by decide⟩ 120 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T147_76 = colFn colCertDiv_147_76_120.D1 (m := 1) from colCertDiv_147_76_120.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 120 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T147_76_2 = colFn colCertDiv_147_76_120.D2 (m := 1) from colCertDiv_147_76_120.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_76_120_match


theorem leaf_147_77_0 (hp : 0 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 0 (transLenTr ⟨77, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 0 (transLenTr ⟨77, by decide⟩ 0 hp)) T147_77
      hfix147_77 hinj147_77 hcardT147_77
      (fun i => conj_mem_of_fixedPoints _ _ (T147_77 i) (hfix147_77 i) _)
      ⟨147, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 0 hp) Q2.T147_77_2 Q2.hfix147_77_2 Q2.hinj147_77_2
      Q2.hcardT147_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_77_2 i) (Q2.hfix147_77_2 i) _)
      colCert_147_77_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_77_1 (hp : 1 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 1 (transLenTr ⟨77, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 1 (transLenTr ⟨77, by decide⟩ 1 hp)) T147_77
      hfix147_77 hinj147_77 hcardT147_77
      (fun i => conj_mem_of_fixedPoints _ _ (T147_77 i) (hfix147_77 i) _)
      ⟨147, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 1 hp) Q2.T147_77_2 Q2.hfix147_77_2 Q2.hinj147_77_2
      Q2.hcardT147_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_77_2 i) (Q2.hfix147_77_2 i) _)
      colCert_147_77_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_77_2 (hp : 2 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 2 (transLenTr ⟨77, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 2 (transLenTr ⟨77, by decide⟩ 2 hp)) T147_77
      hfix147_77 hinj147_77 hcardT147_77
      (fun i => conj_mem_of_fixedPoints _ _ (T147_77 i) (hfix147_77 i) _)
      ⟨147, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 2 hp) Q2.T147_77_2 Q2.hfix147_77_2 Q2.hinj147_77_2
      Q2.hcardT147_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_77_2 i) (Q2.hfix147_77_2 i) _)
      colCert_147_77_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_77_3 (hp : 3 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 3 (transLenTr ⟨77, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 3 (transLenTr ⟨77, by decide⟩ 3 hp)) T147_77
      hfix147_77 hinj147_77 hcardT147_77
      (fun i => conj_mem_of_fixedPoints _ _ (T147_77 i) (hfix147_77 i) _)
      ⟨147, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 3 hp) Q2.T147_77_2 Q2.hfix147_77_2 Q2.hinj147_77_2
      Q2.hcardT147_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_77_2 i) (Q2.hfix147_77_2 i) _)
      colCert_147_77_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_77_4 (hp : 4 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 4 (transLenTr ⟨77, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 4 (transLenTr ⟨77, by decide⟩ 4 hp)) T147_77
      hfix147_77 hinj147_77 hcardT147_77
      (fun i => conj_mem_of_fixedPoints _ _ (T147_77 i) (hfix147_77 i) _)
      ⟨147, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 4 hp) Q2.T147_77_2 Q2.hfix147_77_2 Q2.hinj147_77_2
      Q2.hcardT147_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_77_2 i) (Q2.hfix147_77_2 i) _)
      colCert_147_77_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_77_5 (hp : 5 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 5 (transLenTr ⟨77, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 5 (transLenTr ⟨77, by decide⟩ 5 hp)) T147_77
      hfix147_77 hinj147_77 hcardT147_77
      (fun i => conj_mem_of_fixedPoints _ _ (T147_77 i) (hfix147_77 i) _)
      ⟨147, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 5 hp) Q2.T147_77_2 Q2.hfix147_77_2 Q2.hinj147_77_2
      Q2.hcardT147_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_77_2 i) (Q2.hfix147_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 5 (transLenTr ⟨77, by decide⟩ 5 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T147_77 = colFn colCertDiv_147_77_5.D1 (m := 1) from colCertDiv_147_77_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 5 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T147_77_2 = colFn colCertDiv_147_77_5.D2 (m := 1) from colCertDiv_147_77_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_77_5_match


theorem leaf_147_77_6 (hp : 6 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 6 (transLenTr ⟨77, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 6 (transLenTr ⟨77, by decide⟩ 6 hp)) T147_77
      hfix147_77 hinj147_77 hcardT147_77
      (fun i => conj_mem_of_fixedPoints _ _ (T147_77 i) (hfix147_77 i) _)
      ⟨147, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 6 hp) Q2.T147_77_2 Q2.hfix147_77_2 Q2.hinj147_77_2
      Q2.hcardT147_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_77_2 i) (Q2.hfix147_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 6 (transLenTr ⟨77, by decide⟩ 6 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T147_77 = colFn colCertDiv_147_77_6.D1 (m := 1) from colCertDiv_147_77_6.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 6 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T147_77_2 = colFn colCertDiv_147_77_6.D2 (m := 1) from colCertDiv_147_77_6.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_77_6_match


theorem leaf_147_77_7 (hp : 7 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 7 (transLenTr ⟨77, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 7 (transLenTr ⟨77, by decide⟩ 7 hp)) T147_77
      hfix147_77 hinj147_77 hcardT147_77
      (fun i => conj_mem_of_fixedPoints _ _ (T147_77 i) (hfix147_77 i) _)
      ⟨147, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 7 hp) Q2.T147_77_2 Q2.hfix147_77_2 Q2.hinj147_77_2
      Q2.hcardT147_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_77_2 i) (Q2.hfix147_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 7 (transLenTr ⟨77, by decide⟩ 7 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T147_77 = colFn colCertDiv_147_77_7.D1 (m := 1) from colCertDiv_147_77_7.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 7 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T147_77_2 = colFn colCertDiv_147_77_7.D2 (m := 1) from colCertDiv_147_77_7.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_77_7_match


theorem leaf_147_77_8 (hp : 8 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 8 (transLenTr ⟨77, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 8 (transLenTr ⟨77, by decide⟩ 8 hp)) T147_77
      hfix147_77 hinj147_77 hcardT147_77
      (fun i => conj_mem_of_fixedPoints _ _ (T147_77 i) (hfix147_77 i) _)
      ⟨147, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 8 hp) Q2.T147_77_2 Q2.hfix147_77_2 Q2.hinj147_77_2
      Q2.hcardT147_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_77_2 i) (Q2.hfix147_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 8 (transLenTr ⟨77, by decide⟩ 8 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T147_77 = colFn colCertDiv_147_77_8.D1 (m := 1) from colCertDiv_147_77_8.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 8 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T147_77_2 = colFn colCertDiv_147_77_8.D2 (m := 1) from colCertDiv_147_77_8.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_77_8_match


theorem leaf_147_77_9 (hp : 9 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 9 (transLenTr ⟨77, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 9 (transLenTr ⟨77, by decide⟩ 9 hp)) T147_77
      hfix147_77 hinj147_77 hcardT147_77
      (fun i => conj_mem_of_fixedPoints _ _ (T147_77 i) (hfix147_77 i) _)
      ⟨147, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 9 hp) Q2.T147_77_2 Q2.hfix147_77_2 Q2.hinj147_77_2
      Q2.hcardT147_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_77_2 i) (Q2.hfix147_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 9 (transLenTr ⟨77, by decide⟩ 9 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T147_77 = colFn colCertDiv_147_77_9.D1 (m := 1) from colCertDiv_147_77_9.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 9 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T147_77_2 = colFn colCertDiv_147_77_9.D2 (m := 1) from colCertDiv_147_77_9.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_77_9_match


theorem leaf_147_77_10 (hp : 10 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 10 (transLenTr ⟨77, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 10 (transLenTr ⟨77, by decide⟩ 10 hp)) T147_77
      hfix147_77 hinj147_77 hcardT147_77
      (fun i => conj_mem_of_fixedPoints _ _ (T147_77 i) (hfix147_77 i) _)
      ⟨147, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 10 hp) Q2.T147_77_2 Q2.hfix147_77_2 Q2.hinj147_77_2
      Q2.hcardT147_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_77_2 i) (Q2.hfix147_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 10 (transLenTr ⟨77, by decide⟩ 10 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T147_77 = colFn colCertDiv_147_77_10.D1 (m := 1) from colCertDiv_147_77_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 10 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T147_77_2 = colFn colCertDiv_147_77_10.D2 (m := 1) from colCertDiv_147_77_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_77_10_match


theorem leaf_147_77_11 (hp : 11 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 11 (transLenTr ⟨77, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 11 (transLenTr ⟨77, by decide⟩ 11 hp)) T147_77
      hfix147_77 hinj147_77 hcardT147_77
      (fun i => conj_mem_of_fixedPoints _ _ (T147_77 i) (hfix147_77 i) _)
      ⟨147, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 11 hp) Q2.T147_77_2 Q2.hfix147_77_2 Q2.hinj147_77_2
      Q2.hcardT147_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_77_2 i) (Q2.hfix147_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 11 (transLenTr ⟨77, by decide⟩ 11 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T147_77 = colFn colCertDiv_147_77_11.D1 (m := 1) from colCertDiv_147_77_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 11 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T147_77_2 = colFn colCertDiv_147_77_11.D2 (m := 1) from colCertDiv_147_77_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_77_11_match


theorem leaf_147_77_12 (hp : 12 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 12 (transLenTr ⟨77, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 12 (transLenTr ⟨77, by decide⟩ 12 hp)) T147_77
      hfix147_77 hinj147_77 hcardT147_77
      (fun i => conj_mem_of_fixedPoints _ _ (T147_77 i) (hfix147_77 i) _)
      ⟨147, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 12 hp) Q2.T147_77_2 Q2.hfix147_77_2 Q2.hinj147_77_2
      Q2.hcardT147_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_77_2 i) (Q2.hfix147_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 12 (transLenTr ⟨77, by decide⟩ 12 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T147_77 = colFn colCertDiv_147_77_12.D1 (m := 1) from colCertDiv_147_77_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 12 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T147_77_2 = colFn colCertDiv_147_77_12.D2 (m := 1) from colCertDiv_147_77_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_77_12_match


theorem leaf_147_77_13 (hp : 13 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 13 (transLenTr ⟨77, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 13 (transLenTr ⟨77, by decide⟩ 13 hp)) T147_77
      hfix147_77 hinj147_77 hcardT147_77
      (fun i => conj_mem_of_fixedPoints _ _ (T147_77 i) (hfix147_77 i) _)
      ⟨147, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 13 hp) Q2.T147_77_2 Q2.hfix147_77_2 Q2.hinj147_77_2
      Q2.hcardT147_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_77_2 i) (Q2.hfix147_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 13 (transLenTr ⟨77, by decide⟩ 13 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T147_77 = colFn colCertDiv_147_77_13.D1 (m := 1) from colCertDiv_147_77_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 13 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T147_77_2 = colFn colCertDiv_147_77_13.D2 (m := 1) from colCertDiv_147_77_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_77_13_match


theorem leaf_147_77_14 (hp : 14 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 14 (transLenTr ⟨77, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 14 (transLenTr ⟨77, by decide⟩ 14 hp)) T147_77
      hfix147_77 hinj147_77 hcardT147_77
      (fun i => conj_mem_of_fixedPoints _ _ (T147_77 i) (hfix147_77 i) _)
      ⟨147, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 14 hp) Q2.T147_77_2 Q2.hfix147_77_2 Q2.hinj147_77_2
      Q2.hcardT147_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_77_2 i) (Q2.hfix147_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 14 (transLenTr ⟨77, by decide⟩ 14 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T147_77 = colFn colCertDiv_147_77_14.D1 (m := 1) from colCertDiv_147_77_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 14 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T147_77_2 = colFn colCertDiv_147_77_14.D2 (m := 1) from colCertDiv_147_77_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_77_14_match


theorem leaf_147_77_15 (hp : 15 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 15 (transLenTr ⟨77, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 15 (transLenTr ⟨77, by decide⟩ 15 hp)) T147_77
      hfix147_77 hinj147_77 hcardT147_77
      (fun i => conj_mem_of_fixedPoints _ _ (T147_77 i) (hfix147_77 i) _)
      ⟨147, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 15 hp) Q2.T147_77_2 Q2.hfix147_77_2 Q2.hinj147_77_2
      Q2.hcardT147_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_77_2 i) (Q2.hfix147_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 15 (transLenTr ⟨77, by decide⟩ 15 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T147_77 = colFn colCertDiv_147_77_15.D1 (m := 1) from colCertDiv_147_77_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 15 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T147_77_2 = colFn colCertDiv_147_77_15.D2 (m := 1) from colCertDiv_147_77_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_77_15_match


theorem leaf_147_77_16 (hp : 16 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 16 (transLenTr ⟨77, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 16 (transLenTr ⟨77, by decide⟩ 16 hp)) T147_77
      hfix147_77 hinj147_77 hcardT147_77
      (fun i => conj_mem_of_fixedPoints _ _ (T147_77 i) (hfix147_77 i) _)
      ⟨147, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 16 hp) Q2.T147_77_2 Q2.hfix147_77_2 Q2.hinj147_77_2
      Q2.hcardT147_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_77_2 i) (Q2.hfix147_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 16 (transLenTr ⟨77, by decide⟩ 16 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T147_77 = colFn colCertDiv_147_77_16.D1 (m := 1) from colCertDiv_147_77_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 16 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T147_77_2 = colFn colCertDiv_147_77_16.D2 (m := 1) from colCertDiv_147_77_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_77_16_match


theorem leaf_147_77_17 (hp : 17 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 17 (transLenTr ⟨77, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 17 (transLenTr ⟨77, by decide⟩ 17 hp)) T147_77
      hfix147_77 hinj147_77 hcardT147_77
      (fun i => conj_mem_of_fixedPoints _ _ (T147_77 i) (hfix147_77 i) _)
      ⟨147, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 17 hp) Q2.T147_77_2 Q2.hfix147_77_2 Q2.hinj147_77_2
      Q2.hcardT147_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_77_2 i) (Q2.hfix147_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 17 (transLenTr ⟨77, by decide⟩ 17 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T147_77 = colFn colCertDiv_147_77_17.D1 (m := 1) from colCertDiv_147_77_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 17 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T147_77_2 = colFn colCertDiv_147_77_17.D2 (m := 1) from colCertDiv_147_77_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_77_17_match


theorem leaf_147_77_18 (hp : 18 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 18 (transLenTr ⟨77, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 18 (transLenTr ⟨77, by decide⟩ 18 hp)) T147_77
      hfix147_77 hinj147_77 hcardT147_77
      (fun i => conj_mem_of_fixedPoints _ _ (T147_77 i) (hfix147_77 i) _)
      ⟨147, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 18 hp) Q2.T147_77_2 Q2.hfix147_77_2 Q2.hinj147_77_2
      Q2.hcardT147_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_77_2 i) (Q2.hfix147_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 18 (transLenTr ⟨77, by decide⟩ 18 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T147_77 = colFn colCertDiv_147_77_18.D1 (m := 1) from colCertDiv_147_77_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 18 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T147_77_2 = colFn colCertDiv_147_77_18.D2 (m := 1) from colCertDiv_147_77_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_77_18_match


theorem leaf_147_77_19 (hp : 19 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 19 (transLenTr ⟨77, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 19 (transLenTr ⟨77, by decide⟩ 19 hp)) T147_77
      hfix147_77 hinj147_77 hcardT147_77
      (fun i => conj_mem_of_fixedPoints _ _ (T147_77 i) (hfix147_77 i) _)
      ⟨147, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 19 hp) Q2.T147_77_2 Q2.hfix147_77_2 Q2.hinj147_77_2
      Q2.hcardT147_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_77_2 i) (Q2.hfix147_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 19 (transLenTr ⟨77, by decide⟩ 19 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T147_77 = colFn colCertDiv_147_77_19.D1 (m := 1) from colCertDiv_147_77_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 19 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T147_77_2 = colFn colCertDiv_147_77_19.D2 (m := 1) from colCertDiv_147_77_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_77_19_match


theorem leaf_147_77_20 (hp : 20 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 20 (transLenTr ⟨77, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 20 (transLenTr ⟨77, by decide⟩ 20 hp)) T147_77
      hfix147_77 hinj147_77 hcardT147_77
      (fun i => conj_mem_of_fixedPoints _ _ (T147_77 i) (hfix147_77 i) _)
      ⟨147, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 20 hp) Q2.T147_77_2 Q2.hfix147_77_2 Q2.hinj147_77_2
      Q2.hcardT147_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_77_2 i) (Q2.hfix147_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 20 (transLenTr ⟨77, by decide⟩ 20 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T147_77 = colFn colCertDiv_147_77_20.D1 (m := 1) from colCertDiv_147_77_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 20 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T147_77_2 = colFn colCertDiv_147_77_20.D2 (m := 1) from colCertDiv_147_77_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_77_20_match


theorem leaf_147_77_21 (hp : 21 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 21 (transLenTr ⟨77, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 21 (transLenTr ⟨77, by decide⟩ 21 hp)) T147_77
      hfix147_77 hinj147_77 hcardT147_77
      (fun i => conj_mem_of_fixedPoints _ _ (T147_77 i) (hfix147_77 i) _)
      ⟨147, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 21 hp) Q2.T147_77_2 Q2.hfix147_77_2 Q2.hinj147_77_2
      Q2.hcardT147_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_77_2 i) (Q2.hfix147_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 21 (transLenTr ⟨77, by decide⟩ 21 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T147_77 = colFn colCertDiv_147_77_21.D1 (m := 1) from colCertDiv_147_77_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 21 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T147_77_2 = colFn colCertDiv_147_77_21.D2 (m := 1) from colCertDiv_147_77_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_77_21_match


theorem leaf_147_77_22 (hp : 22 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 22 (transLenTr ⟨77, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 22 (transLenTr ⟨77, by decide⟩ 22 hp)) T147_77
      hfix147_77 hinj147_77 hcardT147_77
      (fun i => conj_mem_of_fixedPoints _ _ (T147_77 i) (hfix147_77 i) _)
      ⟨147, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 22 hp) Q2.T147_77_2 Q2.hfix147_77_2 Q2.hinj147_77_2
      Q2.hcardT147_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_77_2 i) (Q2.hfix147_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 22 (transLenTr ⟨77, by decide⟩ 22 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T147_77 = colFn colCertDiv_147_77_22.D1 (m := 1) from colCertDiv_147_77_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 22 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T147_77_2 = colFn colCertDiv_147_77_22.D2 (m := 1) from colCertDiv_147_77_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_77_22_match


theorem leaf_147_77_23 (hp : 23 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 23 (transLenTr ⟨77, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 23 (transLenTr ⟨77, by decide⟩ 23 hp)) T147_77
      hfix147_77 hinj147_77 hcardT147_77
      (fun i => conj_mem_of_fixedPoints _ _ (T147_77 i) (hfix147_77 i) _)
      ⟨147, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 23 hp) Q2.T147_77_2 Q2.hfix147_77_2 Q2.hinj147_77_2
      Q2.hcardT147_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_77_2 i) (Q2.hfix147_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 23 (transLenTr ⟨77, by decide⟩ 23 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T147_77 = colFn colCertDiv_147_77_23.D1 (m := 1) from colCertDiv_147_77_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 23 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T147_77_2 = colFn colCertDiv_147_77_23.D2 (m := 1) from colCertDiv_147_77_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_77_23_match


theorem leaf_147_77_24 (hp : 24 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 24 (transLenTr ⟨77, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 24 (transLenTr ⟨77, by decide⟩ 24 hp)) T147_77
      hfix147_77 hinj147_77 hcardT147_77
      (fun i => conj_mem_of_fixedPoints _ _ (T147_77 i) (hfix147_77 i) _)
      ⟨147, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 24 hp) Q2.T147_77_2 Q2.hfix147_77_2 Q2.hinj147_77_2
      Q2.hcardT147_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_77_2 i) (Q2.hfix147_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 24 (transLenTr ⟨77, by decide⟩ 24 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T147_77 = colFn colCertDiv_147_77_24.D1 (m := 1) from colCertDiv_147_77_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 24 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T147_77_2 = colFn colCertDiv_147_77_24.D2 (m := 1) from colCertDiv_147_77_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_77_24_match


theorem leaf_147_78_0 (hp : 0 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 0 (transLenTr ⟨78, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 0 (transLenTr ⟨78, by decide⟩ 0 hp)) T147_78
      hfix147_78 hinj147_78 hcardT147_78
      (fun i => conj_mem_of_fixedPoints _ _ (T147_78 i) (hfix147_78 i) _)
      ⟨147, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 0 hp) Q2.T147_78_2 Q2.hfix147_78_2 Q2.hinj147_78_2
      Q2.hcardT147_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_78_2 i) (Q2.hfix147_78_2 i) _)
      colCert_147_78_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_78_1 (hp : 1 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 1 (transLenTr ⟨78, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 1 (transLenTr ⟨78, by decide⟩ 1 hp)) T147_78
      hfix147_78 hinj147_78 hcardT147_78
      (fun i => conj_mem_of_fixedPoints _ _ (T147_78 i) (hfix147_78 i) _)
      ⟨147, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 1 hp) Q2.T147_78_2 Q2.hfix147_78_2 Q2.hinj147_78_2
      Q2.hcardT147_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_78_2 i) (Q2.hfix147_78_2 i) _)
      colCert_147_78_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_78_2 (hp : 2 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 2 (transLenTr ⟨78, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 2 (transLenTr ⟨78, by decide⟩ 2 hp)) T147_78
      hfix147_78 hinj147_78 hcardT147_78
      (fun i => conj_mem_of_fixedPoints _ _ (T147_78 i) (hfix147_78 i) _)
      ⟨147, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 2 hp) Q2.T147_78_2 Q2.hfix147_78_2 Q2.hinj147_78_2
      Q2.hcardT147_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_78_2 i) (Q2.hfix147_78_2 i) _)
      colCert_147_78_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_78_3 (hp : 3 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 3 (transLenTr ⟨78, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 3 (transLenTr ⟨78, by decide⟩ 3 hp)) T147_78
      hfix147_78 hinj147_78 hcardT147_78
      (fun i => conj_mem_of_fixedPoints _ _ (T147_78 i) (hfix147_78 i) _)
      ⟨147, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 3 hp) Q2.T147_78_2 Q2.hfix147_78_2 Q2.hinj147_78_2
      Q2.hcardT147_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_78_2 i) (Q2.hfix147_78_2 i) _)
      colCert_147_78_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_78_4 (hp : 4 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 4 (transLenTr ⟨78, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 4 (transLenTr ⟨78, by decide⟩ 4 hp)) T147_78
      hfix147_78 hinj147_78 hcardT147_78
      (fun i => conj_mem_of_fixedPoints _ _ (T147_78 i) (hfix147_78 i) _)
      ⟨147, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 4 hp) Q2.T147_78_2 Q2.hfix147_78_2 Q2.hinj147_78_2
      Q2.hcardT147_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_78_2 i) (Q2.hfix147_78_2 i) _)
      colCert_147_78_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_78_5 (hp : 5 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 5 (transLenTr ⟨78, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 5 (transLenTr ⟨78, by decide⟩ 5 hp)) T147_78
      hfix147_78 hinj147_78 hcardT147_78
      (fun i => conj_mem_of_fixedPoints _ _ (T147_78 i) (hfix147_78 i) _)
      ⟨147, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 5 hp) Q2.T147_78_2 Q2.hfix147_78_2 Q2.hinj147_78_2
      Q2.hcardT147_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_78_2 i) (Q2.hfix147_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 5 (transLenTr ⟨78, by decide⟩ 5 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T147_78 = colFn colCertDiv_147_78_5.D1 (m := 1) from colCertDiv_147_78_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 5 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T147_78_2 = colFn colCertDiv_147_78_5.D2 (m := 1) from colCertDiv_147_78_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_78_5_match


theorem leaf_147_78_6 (hp : 6 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 6 (transLenTr ⟨78, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 6 (transLenTr ⟨78, by decide⟩ 6 hp)) T147_78
      hfix147_78 hinj147_78 hcardT147_78
      (fun i => conj_mem_of_fixedPoints _ _ (T147_78 i) (hfix147_78 i) _)
      ⟨147, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 6 hp) Q2.T147_78_2 Q2.hfix147_78_2 Q2.hinj147_78_2
      Q2.hcardT147_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_78_2 i) (Q2.hfix147_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 6 (transLenTr ⟨78, by decide⟩ 6 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T147_78 = colFn colCertDiv_147_78_6.D1 (m := 1) from colCertDiv_147_78_6.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 6 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T147_78_2 = colFn colCertDiv_147_78_6.D2 (m := 1) from colCertDiv_147_78_6.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_78_6_match


theorem leaf_147_78_7 (hp : 7 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 7 (transLenTr ⟨78, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 7 (transLenTr ⟨78, by decide⟩ 7 hp)) T147_78
      hfix147_78 hinj147_78 hcardT147_78
      (fun i => conj_mem_of_fixedPoints _ _ (T147_78 i) (hfix147_78 i) _)
      ⟨147, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 7 hp) Q2.T147_78_2 Q2.hfix147_78_2 Q2.hinj147_78_2
      Q2.hcardT147_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_78_2 i) (Q2.hfix147_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 7 (transLenTr ⟨78, by decide⟩ 7 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T147_78 = colFn colCertDiv_147_78_7.D1 (m := 1) from colCertDiv_147_78_7.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 7 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T147_78_2 = colFn colCertDiv_147_78_7.D2 (m := 1) from colCertDiv_147_78_7.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_78_7_match


theorem leaf_147_78_8 (hp : 8 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 8 (transLenTr ⟨78, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 8 (transLenTr ⟨78, by decide⟩ 8 hp)) T147_78
      hfix147_78 hinj147_78 hcardT147_78
      (fun i => conj_mem_of_fixedPoints _ _ (T147_78 i) (hfix147_78 i) _)
      ⟨147, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 8 hp) Q2.T147_78_2 Q2.hfix147_78_2 Q2.hinj147_78_2
      Q2.hcardT147_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_78_2 i) (Q2.hfix147_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 8 (transLenTr ⟨78, by decide⟩ 8 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T147_78 = colFn colCertDiv_147_78_8.D1 (m := 1) from colCertDiv_147_78_8.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 8 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T147_78_2 = colFn colCertDiv_147_78_8.D2 (m := 1) from colCertDiv_147_78_8.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_78_8_match


theorem leaf_147_78_9 (hp : 9 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 9 (transLenTr ⟨78, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 9 (transLenTr ⟨78, by decide⟩ 9 hp)) T147_78
      hfix147_78 hinj147_78 hcardT147_78
      (fun i => conj_mem_of_fixedPoints _ _ (T147_78 i) (hfix147_78 i) _)
      ⟨147, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 9 hp) Q2.T147_78_2 Q2.hfix147_78_2 Q2.hinj147_78_2
      Q2.hcardT147_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_78_2 i) (Q2.hfix147_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 9 (transLenTr ⟨78, by decide⟩ 9 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T147_78 = colFn colCertDiv_147_78_9.D1 (m := 1) from colCertDiv_147_78_9.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 9 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T147_78_2 = colFn colCertDiv_147_78_9.D2 (m := 1) from colCertDiv_147_78_9.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_78_9_match


theorem leaf_147_78_10 (hp : 10 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 10 (transLenTr ⟨78, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 10 (transLenTr ⟨78, by decide⟩ 10 hp)) T147_78
      hfix147_78 hinj147_78 hcardT147_78
      (fun i => conj_mem_of_fixedPoints _ _ (T147_78 i) (hfix147_78 i) _)
      ⟨147, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 10 hp) Q2.T147_78_2 Q2.hfix147_78_2 Q2.hinj147_78_2
      Q2.hcardT147_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_78_2 i) (Q2.hfix147_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 10 (transLenTr ⟨78, by decide⟩ 10 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T147_78 = colFn colCertDiv_147_78_10.D1 (m := 1) from colCertDiv_147_78_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 10 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T147_78_2 = colFn colCertDiv_147_78_10.D2 (m := 1) from colCertDiv_147_78_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_78_10_match


theorem leaf_147_78_11 (hp : 11 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 11 (transLenTr ⟨78, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 11 (transLenTr ⟨78, by decide⟩ 11 hp)) T147_78
      hfix147_78 hinj147_78 hcardT147_78
      (fun i => conj_mem_of_fixedPoints _ _ (T147_78 i) (hfix147_78 i) _)
      ⟨147, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 11 hp) Q2.T147_78_2 Q2.hfix147_78_2 Q2.hinj147_78_2
      Q2.hcardT147_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_78_2 i) (Q2.hfix147_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 11 (transLenTr ⟨78, by decide⟩ 11 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T147_78 = colFn colCertDiv_147_78_11.D1 (m := 1) from colCertDiv_147_78_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 11 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T147_78_2 = colFn colCertDiv_147_78_11.D2 (m := 1) from colCertDiv_147_78_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_78_11_match


theorem leaf_147_78_12 (hp : 12 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 12 (transLenTr ⟨78, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 12 (transLenTr ⟨78, by decide⟩ 12 hp)) T147_78
      hfix147_78 hinj147_78 hcardT147_78
      (fun i => conj_mem_of_fixedPoints _ _ (T147_78 i) (hfix147_78 i) _)
      ⟨147, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 12 hp) Q2.T147_78_2 Q2.hfix147_78_2 Q2.hinj147_78_2
      Q2.hcardT147_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_78_2 i) (Q2.hfix147_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 12 (transLenTr ⟨78, by decide⟩ 12 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T147_78 = colFn colCertDiv_147_78_12.D1 (m := 1) from colCertDiv_147_78_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 12 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T147_78_2 = colFn colCertDiv_147_78_12.D2 (m := 1) from colCertDiv_147_78_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_78_12_match


theorem leaf_147_78_13 (hp : 13 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 13 (transLenTr ⟨78, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 13 (transLenTr ⟨78, by decide⟩ 13 hp)) T147_78
      hfix147_78 hinj147_78 hcardT147_78
      (fun i => conj_mem_of_fixedPoints _ _ (T147_78 i) (hfix147_78 i) _)
      ⟨147, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 13 hp) Q2.T147_78_2 Q2.hfix147_78_2 Q2.hinj147_78_2
      Q2.hcardT147_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_78_2 i) (Q2.hfix147_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 13 (transLenTr ⟨78, by decide⟩ 13 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T147_78 = colFn colCertDiv_147_78_13.D1 (m := 1) from colCertDiv_147_78_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 13 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T147_78_2 = colFn colCertDiv_147_78_13.D2 (m := 1) from colCertDiv_147_78_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_78_13_match


theorem leaf_147_78_14 (hp : 14 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 14 (transLenTr ⟨78, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 14 (transLenTr ⟨78, by decide⟩ 14 hp)) T147_78
      hfix147_78 hinj147_78 hcardT147_78
      (fun i => conj_mem_of_fixedPoints _ _ (T147_78 i) (hfix147_78 i) _)
      ⟨147, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 14 hp) Q2.T147_78_2 Q2.hfix147_78_2 Q2.hinj147_78_2
      Q2.hcardT147_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_78_2 i) (Q2.hfix147_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 14 (transLenTr ⟨78, by decide⟩ 14 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T147_78 = colFn colCertDiv_147_78_14.D1 (m := 1) from colCertDiv_147_78_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 14 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T147_78_2 = colFn colCertDiv_147_78_14.D2 (m := 1) from colCertDiv_147_78_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_78_14_match


theorem leaf_147_78_15 (hp : 15 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 15 (transLenTr ⟨78, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 15 (transLenTr ⟨78, by decide⟩ 15 hp)) T147_78
      hfix147_78 hinj147_78 hcardT147_78
      (fun i => conj_mem_of_fixedPoints _ _ (T147_78 i) (hfix147_78 i) _)
      ⟨147, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 15 hp) Q2.T147_78_2 Q2.hfix147_78_2 Q2.hinj147_78_2
      Q2.hcardT147_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_78_2 i) (Q2.hfix147_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 15 (transLenTr ⟨78, by decide⟩ 15 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T147_78 = colFn colCertDiv_147_78_15.D1 (m := 1) from colCertDiv_147_78_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 15 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T147_78_2 = colFn colCertDiv_147_78_15.D2 (m := 1) from colCertDiv_147_78_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_78_15_match


theorem leaf_147_78_16 (hp : 16 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 16 (transLenTr ⟨78, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 16 (transLenTr ⟨78, by decide⟩ 16 hp)) T147_78
      hfix147_78 hinj147_78 hcardT147_78
      (fun i => conj_mem_of_fixedPoints _ _ (T147_78 i) (hfix147_78 i) _)
      ⟨147, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 16 hp) Q2.T147_78_2 Q2.hfix147_78_2 Q2.hinj147_78_2
      Q2.hcardT147_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_78_2 i) (Q2.hfix147_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 16 (transLenTr ⟨78, by decide⟩ 16 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T147_78 = colFn colCertDiv_147_78_16.D1 (m := 1) from colCertDiv_147_78_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 16 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T147_78_2 = colFn colCertDiv_147_78_16.D2 (m := 1) from colCertDiv_147_78_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_78_16_match


theorem leaf_147_78_17 (hp : 17 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 17 (transLenTr ⟨78, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 17 (transLenTr ⟨78, by decide⟩ 17 hp)) T147_78
      hfix147_78 hinj147_78 hcardT147_78
      (fun i => conj_mem_of_fixedPoints _ _ (T147_78 i) (hfix147_78 i) _)
      ⟨147, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 17 hp) Q2.T147_78_2 Q2.hfix147_78_2 Q2.hinj147_78_2
      Q2.hcardT147_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_78_2 i) (Q2.hfix147_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 17 (transLenTr ⟨78, by decide⟩ 17 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T147_78 = colFn colCertDiv_147_78_17.D1 (m := 1) from colCertDiv_147_78_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 17 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T147_78_2 = colFn colCertDiv_147_78_17.D2 (m := 1) from colCertDiv_147_78_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_78_17_match


theorem leaf_147_78_18 (hp : 18 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 18 (transLenTr ⟨78, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 18 (transLenTr ⟨78, by decide⟩ 18 hp)) T147_78
      hfix147_78 hinj147_78 hcardT147_78
      (fun i => conj_mem_of_fixedPoints _ _ (T147_78 i) (hfix147_78 i) _)
      ⟨147, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 18 hp) Q2.T147_78_2 Q2.hfix147_78_2 Q2.hinj147_78_2
      Q2.hcardT147_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_78_2 i) (Q2.hfix147_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 18 (transLenTr ⟨78, by decide⟩ 18 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T147_78 = colFn colCertDiv_147_78_18.D1 (m := 1) from colCertDiv_147_78_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 18 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T147_78_2 = colFn colCertDiv_147_78_18.D2 (m := 1) from colCertDiv_147_78_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_78_18_match


theorem leaf_147_78_19 (hp : 19 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 19 (transLenTr ⟨78, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 19 (transLenTr ⟨78, by decide⟩ 19 hp)) T147_78
      hfix147_78 hinj147_78 hcardT147_78
      (fun i => conj_mem_of_fixedPoints _ _ (T147_78 i) (hfix147_78 i) _)
      ⟨147, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 19 hp) Q2.T147_78_2 Q2.hfix147_78_2 Q2.hinj147_78_2
      Q2.hcardT147_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_78_2 i) (Q2.hfix147_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 19 (transLenTr ⟨78, by decide⟩ 19 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T147_78 = colFn colCertDiv_147_78_19.D1 (m := 1) from colCertDiv_147_78_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 19 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T147_78_2 = colFn colCertDiv_147_78_19.D2 (m := 1) from colCertDiv_147_78_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_78_19_match


theorem leaf_147_78_20 (hp : 20 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 20 (transLenTr ⟨78, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 20 (transLenTr ⟨78, by decide⟩ 20 hp)) T147_78
      hfix147_78 hinj147_78 hcardT147_78
      (fun i => conj_mem_of_fixedPoints _ _ (T147_78 i) (hfix147_78 i) _)
      ⟨147, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 20 hp) Q2.T147_78_2 Q2.hfix147_78_2 Q2.hinj147_78_2
      Q2.hcardT147_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_78_2 i) (Q2.hfix147_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 20 (transLenTr ⟨78, by decide⟩ 20 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T147_78 = colFn colCertDiv_147_78_20.D1 (m := 1) from colCertDiv_147_78_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 20 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T147_78_2 = colFn colCertDiv_147_78_20.D2 (m := 1) from colCertDiv_147_78_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_78_20_match


theorem leaf_147_78_21 (hp : 21 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 21 (transLenTr ⟨78, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 21 (transLenTr ⟨78, by decide⟩ 21 hp)) T147_78
      hfix147_78 hinj147_78 hcardT147_78
      (fun i => conj_mem_of_fixedPoints _ _ (T147_78 i) (hfix147_78 i) _)
      ⟨147, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 21 hp) Q2.T147_78_2 Q2.hfix147_78_2 Q2.hinj147_78_2
      Q2.hcardT147_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_78_2 i) (Q2.hfix147_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 21 (transLenTr ⟨78, by decide⟩ 21 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T147_78 = colFn colCertDiv_147_78_21.D1 (m := 1) from colCertDiv_147_78_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 21 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T147_78_2 = colFn colCertDiv_147_78_21.D2 (m := 1) from colCertDiv_147_78_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_78_21_match


theorem leaf_147_78_22 (hp : 22 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 22 (transLenTr ⟨78, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 22 (transLenTr ⟨78, by decide⟩ 22 hp)) T147_78
      hfix147_78 hinj147_78 hcardT147_78
      (fun i => conj_mem_of_fixedPoints _ _ (T147_78 i) (hfix147_78 i) _)
      ⟨147, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 22 hp) Q2.T147_78_2 Q2.hfix147_78_2 Q2.hinj147_78_2
      Q2.hcardT147_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_78_2 i) (Q2.hfix147_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 22 (transLenTr ⟨78, by decide⟩ 22 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T147_78 = colFn colCertDiv_147_78_22.D1 (m := 1) from colCertDiv_147_78_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 22 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T147_78_2 = colFn colCertDiv_147_78_22.D2 (m := 1) from colCertDiv_147_78_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_78_22_match


theorem leaf_147_78_23 (hp : 23 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 23 (transLenTr ⟨78, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 23 (transLenTr ⟨78, by decide⟩ 23 hp)) T147_78
      hfix147_78 hinj147_78 hcardT147_78
      (fun i => conj_mem_of_fixedPoints _ _ (T147_78 i) (hfix147_78 i) _)
      ⟨147, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 23 hp) Q2.T147_78_2 Q2.hfix147_78_2 Q2.hinj147_78_2
      Q2.hcardT147_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_78_2 i) (Q2.hfix147_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 23 (transLenTr ⟨78, by decide⟩ 23 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T147_78 = colFn colCertDiv_147_78_23.D1 (m := 1) from colCertDiv_147_78_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 23 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T147_78_2 = colFn colCertDiv_147_78_23.D2 (m := 1) from colCertDiv_147_78_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_78_23_match


theorem leaf_147_78_24 (hp : 24 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 24 (transLenTr ⟨78, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 24 (transLenTr ⟨78, by decide⟩ 24 hp)) T147_78
      hfix147_78 hinj147_78 hcardT147_78
      (fun i => conj_mem_of_fixedPoints _ _ (T147_78 i) (hfix147_78 i) _)
      ⟨147, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 24 hp) Q2.T147_78_2 Q2.hfix147_78_2 Q2.hinj147_78_2
      Q2.hcardT147_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_78_2 i) (Q2.hfix147_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 24 (transLenTr ⟨78, by decide⟩ 24 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T147_78 = colFn colCertDiv_147_78_24.D1 (m := 1) from colCertDiv_147_78_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 24 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T147_78_2 = colFn colCertDiv_147_78_24.D2 (m := 1) from colCertDiv_147_78_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_78_24_match


theorem leaf_147_79_0 (hp : 0 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 0 (transLenTr ⟨79, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 0 (transLenTr ⟨79, by decide⟩ 0 hp)) T147_79
      hfix147_79 hinj147_79 hcardT147_79
      (fun i => conj_mem_of_fixedPoints _ _ (T147_79 i) (hfix147_79 i) _)
      ⟨147, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 0 hp) Q2.T147_79_2 Q2.hfix147_79_2 Q2.hinj147_79_2
      Q2.hcardT147_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_79_2 i) (Q2.hfix147_79_2 i) _)
      colCert_147_79_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_79_1 (hp : 1 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 1 (transLenTr ⟨79, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 1 (transLenTr ⟨79, by decide⟩ 1 hp)) T147_79
      hfix147_79 hinj147_79 hcardT147_79
      (fun i => conj_mem_of_fixedPoints _ _ (T147_79 i) (hfix147_79 i) _)
      ⟨147, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 1 hp) Q2.T147_79_2 Q2.hfix147_79_2 Q2.hinj147_79_2
      Q2.hcardT147_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_79_2 i) (Q2.hfix147_79_2 i) _)
      colCert_147_79_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_79_2 (hp : 2 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 2 (transLenTr ⟨79, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 2 (transLenTr ⟨79, by decide⟩ 2 hp)) T147_79
      hfix147_79 hinj147_79 hcardT147_79
      (fun i => conj_mem_of_fixedPoints _ _ (T147_79 i) (hfix147_79 i) _)
      ⟨147, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 2 hp) Q2.T147_79_2 Q2.hfix147_79_2 Q2.hinj147_79_2
      Q2.hcardT147_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_79_2 i) (Q2.hfix147_79_2 i) _)
      colCert_147_79_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_79_3 (hp : 3 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 3 (transLenTr ⟨79, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 3 (transLenTr ⟨79, by decide⟩ 3 hp)) T147_79
      hfix147_79 hinj147_79 hcardT147_79
      (fun i => conj_mem_of_fixedPoints _ _ (T147_79 i) (hfix147_79 i) _)
      ⟨147, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 3 hp) Q2.T147_79_2 Q2.hfix147_79_2 Q2.hinj147_79_2
      Q2.hcardT147_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_79_2 i) (Q2.hfix147_79_2 i) _)
      colCert_147_79_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_79_4 (hp : 4 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 4 (transLenTr ⟨79, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 4 (transLenTr ⟨79, by decide⟩ 4 hp)) T147_79
      hfix147_79 hinj147_79 hcardT147_79
      (fun i => conj_mem_of_fixedPoints _ _ (T147_79 i) (hfix147_79 i) _)
      ⟨147, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 4 hp) Q2.T147_79_2 Q2.hfix147_79_2 Q2.hinj147_79_2
      Q2.hcardT147_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_79_2 i) (Q2.hfix147_79_2 i) _)
      colCert_147_79_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_79_5 (hp : 5 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 5 (transLenTr ⟨79, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 5 (transLenTr ⟨79, by decide⟩ 5 hp)) T147_79
      hfix147_79 hinj147_79 hcardT147_79
      (fun i => conj_mem_of_fixedPoints _ _ (T147_79 i) (hfix147_79 i) _)
      ⟨147, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 5 hp) Q2.T147_79_2 Q2.hfix147_79_2 Q2.hinj147_79_2
      Q2.hcardT147_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_79_2 i) (Q2.hfix147_79_2 i) _)
      colCert_147_79_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_79_6 (hp : 6 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 6 (transLenTr ⟨79, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 6 (transLenTr ⟨79, by decide⟩ 6 hp)) T147_79
      hfix147_79 hinj147_79 hcardT147_79
      (fun i => conj_mem_of_fixedPoints _ _ (T147_79 i) (hfix147_79 i) _)
      ⟨147, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 6 hp) Q2.T147_79_2 Q2.hfix147_79_2 Q2.hinj147_79_2
      Q2.hcardT147_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_79_2 i) (Q2.hfix147_79_2 i) _)
      colCert_147_79_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_79_7 (hp : 7 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 7 (transLenTr ⟨79, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 7 (transLenTr ⟨79, by decide⟩ 7 hp)) T147_79
      hfix147_79 hinj147_79 hcardT147_79
      (fun i => conj_mem_of_fixedPoints _ _ (T147_79 i) (hfix147_79 i) _)
      ⟨147, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 7 hp) Q2.T147_79_2 Q2.hfix147_79_2 Q2.hinj147_79_2
      Q2.hcardT147_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_79_2 i) (Q2.hfix147_79_2 i) _)
      colCert_147_79_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_79_8 (hp : 8 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 8 (transLenTr ⟨79, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 8 (transLenTr ⟨79, by decide⟩ 8 hp)) T147_79
      hfix147_79 hinj147_79 hcardT147_79
      (fun i => conj_mem_of_fixedPoints _ _ (T147_79 i) (hfix147_79 i) _)
      ⟨147, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 8 hp) Q2.T147_79_2 Q2.hfix147_79_2 Q2.hinj147_79_2
      Q2.hcardT147_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_79_2 i) (Q2.hfix147_79_2 i) _)
      colCert_147_79_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_79_9 (hp : 9 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 9 (transLenTr ⟨79, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 9 (transLenTr ⟨79, by decide⟩ 9 hp)) T147_79
      hfix147_79 hinj147_79 hcardT147_79
      (fun i => conj_mem_of_fixedPoints _ _ (T147_79 i) (hfix147_79 i) _)
      ⟨147, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 9 hp) Q2.T147_79_2 Q2.hfix147_79_2 Q2.hinj147_79_2
      Q2.hcardT147_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_79_2 i) (Q2.hfix147_79_2 i) _)
      colCert_147_79_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_79_10 (hp : 10 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 10 (transLenTr ⟨79, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 10 (transLenTr ⟨79, by decide⟩ 10 hp)) T147_79
      hfix147_79 hinj147_79 hcardT147_79
      (fun i => conj_mem_of_fixedPoints _ _ (T147_79 i) (hfix147_79 i) _)
      ⟨147, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 10 hp) Q2.T147_79_2 Q2.hfix147_79_2 Q2.hinj147_79_2
      Q2.hcardT147_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_79_2 i) (Q2.hfix147_79_2 i) _)
      colCert_147_79_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_79_11 (hp : 11 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 11 (transLenTr ⟨79, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 11 (transLenTr ⟨79, by decide⟩ 11 hp)) T147_79
      hfix147_79 hinj147_79 hcardT147_79
      (fun i => conj_mem_of_fixedPoints _ _ (T147_79 i) (hfix147_79 i) _)
      ⟨147, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 11 hp) Q2.T147_79_2 Q2.hfix147_79_2 Q2.hinj147_79_2
      Q2.hcardT147_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_79_2 i) (Q2.hfix147_79_2 i) _)
      colCert_147_79_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_79_12 (hp : 12 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 12 (transLenTr ⟨79, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 12 (transLenTr ⟨79, by decide⟩ 12 hp)) T147_79
      hfix147_79 hinj147_79 hcardT147_79
      (fun i => conj_mem_of_fixedPoints _ _ (T147_79 i) (hfix147_79 i) _)
      ⟨147, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 12 hp) Q2.T147_79_2 Q2.hfix147_79_2 Q2.hinj147_79_2
      Q2.hcardT147_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_79_2 i) (Q2.hfix147_79_2 i) _)
      colCert_147_79_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_79_13 (hp : 13 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 13 (transLenTr ⟨79, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 13 (transLenTr ⟨79, by decide⟩ 13 hp)) T147_79
      hfix147_79 hinj147_79 hcardT147_79
      (fun i => conj_mem_of_fixedPoints _ _ (T147_79 i) (hfix147_79 i) _)
      ⟨147, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 13 hp) Q2.T147_79_2 Q2.hfix147_79_2 Q2.hinj147_79_2
      Q2.hcardT147_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_79_2 i) (Q2.hfix147_79_2 i) _)
      colCert_147_79_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_79_14 (hp : 14 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 14 (transLenTr ⟨79, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 14 (transLenTr ⟨79, by decide⟩ 14 hp)) T147_79
      hfix147_79 hinj147_79 hcardT147_79
      (fun i => conj_mem_of_fixedPoints _ _ (T147_79 i) (hfix147_79 i) _)
      ⟨147, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 14 hp) Q2.T147_79_2 Q2.hfix147_79_2 Q2.hinj147_79_2
      Q2.hcardT147_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_79_2 i) (Q2.hfix147_79_2 i) _)
      colCert_147_79_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_79_15 (hp : 15 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 15 (transLenTr ⟨79, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 15 (transLenTr ⟨79, by decide⟩ 15 hp)) T147_79
      hfix147_79 hinj147_79 hcardT147_79
      (fun i => conj_mem_of_fixedPoints _ _ (T147_79 i) (hfix147_79 i) _)
      ⟨147, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 15 hp) Q2.T147_79_2 Q2.hfix147_79_2 Q2.hinj147_79_2
      Q2.hcardT147_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_79_2 i) (Q2.hfix147_79_2 i) _)
      colCert_147_79_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_79_16 (hp : 16 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 16 (transLenTr ⟨79, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 16 (transLenTr ⟨79, by decide⟩ 16 hp)) T147_79
      hfix147_79 hinj147_79 hcardT147_79
      (fun i => conj_mem_of_fixedPoints _ _ (T147_79 i) (hfix147_79 i) _)
      ⟨147, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 16 hp) Q2.T147_79_2 Q2.hfix147_79_2 Q2.hinj147_79_2
      Q2.hcardT147_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_79_2 i) (Q2.hfix147_79_2 i) _)
      colCert_147_79_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_79_17 (hp : 17 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 17 (transLenTr ⟨79, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 17 (transLenTr ⟨79, by decide⟩ 17 hp)) T147_79
      hfix147_79 hinj147_79 hcardT147_79
      (fun i => conj_mem_of_fixedPoints _ _ (T147_79 i) (hfix147_79 i) _)
      ⟨147, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 17 hp) Q2.T147_79_2 Q2.hfix147_79_2 Q2.hinj147_79_2
      Q2.hcardT147_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_79_2 i) (Q2.hfix147_79_2 i) _)
      colCert_147_79_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_79_18 (hp : 18 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 18 (transLenTr ⟨79, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 18 (transLenTr ⟨79, by decide⟩ 18 hp)) T147_79
      hfix147_79 hinj147_79 hcardT147_79
      (fun i => conj_mem_of_fixedPoints _ _ (T147_79 i) (hfix147_79 i) _)
      ⟨147, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 18 hp) Q2.T147_79_2 Q2.hfix147_79_2 Q2.hinj147_79_2
      Q2.hcardT147_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_79_2 i) (Q2.hfix147_79_2 i) _)
      colCert_147_79_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_79_19 (hp : 19 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 19 (transLenTr ⟨79, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 19 (transLenTr ⟨79, by decide⟩ 19 hp)) T147_79
      hfix147_79 hinj147_79 hcardT147_79
      (fun i => conj_mem_of_fixedPoints _ _ (T147_79 i) (hfix147_79 i) _)
      ⟨147, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 19 hp) Q2.T147_79_2 Q2.hfix147_79_2 Q2.hinj147_79_2
      Q2.hcardT147_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_79_2 i) (Q2.hfix147_79_2 i) _)
      colCert_147_79_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_79_20 (hp : 20 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 20 (transLenTr ⟨79, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 20 (transLenTr ⟨79, by decide⟩ 20 hp)) T147_79
      hfix147_79 hinj147_79 hcardT147_79
      (fun i => conj_mem_of_fixedPoints _ _ (T147_79 i) (hfix147_79 i) _)
      ⟨147, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 20 hp) Q2.T147_79_2 Q2.hfix147_79_2 Q2.hinj147_79_2
      Q2.hcardT147_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_79_2 i) (Q2.hfix147_79_2 i) _)
      colCert_147_79_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_79_21 (hp : 21 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 21 (transLenTr ⟨79, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 21 (transLenTr ⟨79, by decide⟩ 21 hp)) T147_79
      hfix147_79 hinj147_79 hcardT147_79
      (fun i => conj_mem_of_fixedPoints _ _ (T147_79 i) (hfix147_79 i) _)
      ⟨147, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 21 hp) Q2.T147_79_2 Q2.hfix147_79_2 Q2.hinj147_79_2
      Q2.hcardT147_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_79_2 i) (Q2.hfix147_79_2 i) _)
      colCert_147_79_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_79_22 (hp : 22 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 22 (transLenTr ⟨79, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 22 (transLenTr ⟨79, by decide⟩ 22 hp)) T147_79
      hfix147_79 hinj147_79 hcardT147_79
      (fun i => conj_mem_of_fixedPoints _ _ (T147_79 i) (hfix147_79 i) _)
      ⟨147, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 22 hp) Q2.T147_79_2 Q2.hfix147_79_2 Q2.hinj147_79_2
      Q2.hcardT147_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_79_2 i) (Q2.hfix147_79_2 i) _)
      colCert_147_79_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_79_23 (hp : 23 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 23 (transLenTr ⟨79, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 23 (transLenTr ⟨79, by decide⟩ 23 hp)) T147_79
      hfix147_79 hinj147_79 hcardT147_79
      (fun i => conj_mem_of_fixedPoints _ _ (T147_79 i) (hfix147_79 i) _)
      ⟨147, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 23 hp) Q2.T147_79_2 Q2.hfix147_79_2 Q2.hinj147_79_2
      Q2.hcardT147_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_79_2 i) (Q2.hfix147_79_2 i) _)
      colCert_147_79_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_79_24 (hp : 24 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 24 (transLenTr ⟨79, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 24 (transLenTr ⟨79, by decide⟩ 24 hp)) T147_79
      hfix147_79 hinj147_79 hcardT147_79
      (fun i => conj_mem_of_fixedPoints _ _ (T147_79 i) (hfix147_79 i) _)
      ⟨147, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 24 hp) Q2.T147_79_2 Q2.hfix147_79_2 Q2.hinj147_79_2
      Q2.hcardT147_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_79_2 i) (Q2.hfix147_79_2 i) _)
      colCert_147_79_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_0 (hp : 0 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 0 (transLenTr ⟨80, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 0 (transLenTr ⟨80, by decide⟩ 0 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 0 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_1 (hp : 1 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 1 (transLenTr ⟨80, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 1 (transLenTr ⟨80, by decide⟩ 1 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 1 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_2 (hp : 2 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 2 (transLenTr ⟨80, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 2 (transLenTr ⟨80, by decide⟩ 2 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 2 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_3 (hp : 3 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 3 (transLenTr ⟨80, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 3 (transLenTr ⟨80, by decide⟩ 3 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 3 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_4 (hp : 4 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 4 (transLenTr ⟨80, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 4 (transLenTr ⟨80, by decide⟩ 4 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 4 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_5 (hp : 5 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 5 (transLenTr ⟨80, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 5 (transLenTr ⟨80, by decide⟩ 5 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 5 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_10 (hp : 10 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 10 (transLenTr ⟨80, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 10 (transLenTr ⟨80, by decide⟩ 10 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 10 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_15 (hp : 15 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 15 (transLenTr ⟨80, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 15 (transLenTr ⟨80, by decide⟩ 15 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 15 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_20 (hp : 20 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 20 (transLenTr ⟨80, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 20 (transLenTr ⟨80, by decide⟩ 20 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 20 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_25 (hp : 25 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 25 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 25 (transLenTr ⟨80, by decide⟩ 25 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 25 (transLenTr ⟨80, by decide⟩ 25 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 25 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_25.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_30 (hp : 30 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 30 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 30 (transLenTr ⟨80, by decide⟩ 30 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 30 (transLenTr ⟨80, by decide⟩ 30 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 30 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_30.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_35 (hp : 35 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 35 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 35 (transLenTr ⟨80, by decide⟩ 35 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 35 (transLenTr ⟨80, by decide⟩ 35 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 35 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_35.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_40 (hp : 40 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 40 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 40 (transLenTr ⟨80, by decide⟩ 40 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 40 (transLenTr ⟨80, by decide⟩ 40 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 40 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_40.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_45 (hp : 45 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 45 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 45 (transLenTr ⟨80, by decide⟩ 45 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 45 (transLenTr ⟨80, by decide⟩ 45 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 45 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_45.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_50 (hp : 50 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 50 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 50 (transLenTr ⟨80, by decide⟩ 50 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 50 (transLenTr ⟨80, by decide⟩ 50 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 50 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_50.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_55 (hp : 55 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 55 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 55 (transLenTr ⟨80, by decide⟩ 55 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 55 (transLenTr ⟨80, by decide⟩ 55 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 55 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_55.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_60 (hp : 60 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 60 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 60 (transLenTr ⟨80, by decide⟩ 60 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 60 (transLenTr ⟨80, by decide⟩ 60 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 60 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_60.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_65 (hp : 65 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 65 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 65 (transLenTr ⟨80, by decide⟩ 65 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 65 (transLenTr ⟨80, by decide⟩ 65 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 65 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_65.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_70 (hp : 70 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 70 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 70 (transLenTr ⟨80, by decide⟩ 70 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 70 (transLenTr ⟨80, by decide⟩ 70 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 70 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_70.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_75 (hp : 75 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 75 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 75 (transLenTr ⟨80, by decide⟩ 75 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 75 (transLenTr ⟨80, by decide⟩ 75 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 75 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_75.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_80 (hp : 80 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 80 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 80 (transLenTr ⟨80, by decide⟩ 80 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 80 (transLenTr ⟨80, by decide⟩ 80 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 80 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_80.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_85 (hp : 85 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 85 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 85 (transLenTr ⟨80, by decide⟩ 85 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 85 (transLenTr ⟨80, by decide⟩ 85 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 85 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_85.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_90 (hp : 90 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 90 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 90 (transLenTr ⟨80, by decide⟩ 90 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 90 (transLenTr ⟨80, by decide⟩ 90 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 90 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_90.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_95 (hp : 95 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 95 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 95 (transLenTr ⟨80, by decide⟩ 95 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 95 (transLenTr ⟨80, by decide⟩ 95 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 95 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_95.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_100 (hp : 100 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 100 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 100 (transLenTr ⟨80, by decide⟩ 100 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 100 (transLenTr ⟨80, by decide⟩ 100 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 100 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_100.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_105 (hp : 105 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 105 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 105 (transLenTr ⟨80, by decide⟩ 105 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 105 (transLenTr ⟨80, by decide⟩ 105 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 105 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_105.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_110 (hp : 110 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 110 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 110 (transLenTr ⟨80, by decide⟩ 110 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 110 (transLenTr ⟨80, by decide⟩ 110 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 110 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_110.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_115 (hp : 115 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 115 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 115 (transLenTr ⟨80, by decide⟩ 115 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 115 (transLenTr ⟨80, by decide⟩ 115 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 115 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_115.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_80_120 (hp : 120 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 120 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 120 (transLenTr ⟨80, by decide⟩ 120 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 120 (transLenTr ⟨80, by decide⟩ 120 hp)) T147_80
      hfix147_80 hinj147_80 hcardT147_80
      (fun i => conj_mem_of_fixedPoints _ _ (T147_80 i) (hfix147_80 i) _)
      ⟨147, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 120 hp) Q2.T147_80_2 Q2.hfix147_80_2 Q2.hinj147_80_2
      Q2.hcardT147_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_80_2 i) (Q2.hfix147_80_2 i) _)
      colCert_147_80_120.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_81_0 (hp : 0 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 0 (transLenTr ⟨81, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 0 (transLenTr ⟨81, by decide⟩ 0 hp)) T147_81
      hfix147_81 hinj147_81 hcardT147_81
      (fun i => conj_mem_of_fixedPoints _ _ (T147_81 i) (hfix147_81 i) _)
      ⟨147, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 0 hp) Q2.T147_81_2 Q2.hfix147_81_2 Q2.hinj147_81_2
      Q2.hcardT147_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_81_2 i) (Q2.hfix147_81_2 i) _)
      colCert_147_81_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_81_1 (hp : 1 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 1 (transLenTr ⟨81, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 1 (transLenTr ⟨81, by decide⟩ 1 hp)) T147_81
      hfix147_81 hinj147_81 hcardT147_81
      (fun i => conj_mem_of_fixedPoints _ _ (T147_81 i) (hfix147_81 i) _)
      ⟨147, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 1 hp) Q2.T147_81_2 Q2.hfix147_81_2 Q2.hinj147_81_2
      Q2.hcardT147_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_81_2 i) (Q2.hfix147_81_2 i) _)
      colCert_147_81_1.hD ?_).symm
  rw [alnId_147 j hj]


end LeanDring.P5Presentation
