/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C022
import LeanDring.P5.Data.ColRestCheap.C105
import LeanDring.P5.Data.ColRestCheap.C106
import LeanDring.P5.Data.ColRestCheap.C107
import LeanDring.P5.Data.ColRestCheap.C108
import LeanDring.P5.Data.EntryK.C042
import LeanDring.P5.Data.EntryK.C043
import LeanDring.P5.Data.EntryK.C044
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C036
import LeanDring.P5.Data.SpeciesDiv.C037

/-! # Stage-5 leaves, chunk 47 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_145_106_1 (hp : 1 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 1 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 1 (transLenTr ⟨106, by decide⟩ 1 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 1 (transLenTr ⟨106, by decide⟩ 1 hp)) T145_106
      hfix145_106 hinj145_106 hcardT145_106
      (fun i => conj_mem_of_fixedPoints _ _ (T145_106 i) (hfix145_106 i) _)
      ⟨145, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 1 hp) Q2.T145_106_2 Q2.hfix145_106_2 Q2.hinj145_106_2
      Q2.hcardT145_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_106_2 i) (Q2.hfix145_106_2 i) _)
      colCert_145_106_1.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_106_2 (hp : 2 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 2 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 2 (transLenTr ⟨106, by decide⟩ 2 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 2 (transLenTr ⟨106, by decide⟩ 2 hp)) T145_106
      hfix145_106 hinj145_106 hcardT145_106
      (fun i => conj_mem_of_fixedPoints _ _ (T145_106 i) (hfix145_106 i) _)
      ⟨145, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 2 hp) Q2.T145_106_2 Q2.hfix145_106_2 Q2.hinj145_106_2
      Q2.hcardT145_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_106_2 i) (Q2.hfix145_106_2 i) _)
      colCert_145_106_2.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_106_3 (hp : 3 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 3 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 3 (transLenTr ⟨106, by decide⟩ 3 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 3 (transLenTr ⟨106, by decide⟩ 3 hp)) T145_106
      hfix145_106 hinj145_106 hcardT145_106
      (fun i => conj_mem_of_fixedPoints _ _ (T145_106 i) (hfix145_106 i) _)
      ⟨145, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 3 hp) Q2.T145_106_2 Q2.hfix145_106_2 Q2.hinj145_106_2
      Q2.hcardT145_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_106_2 i) (Q2.hfix145_106_2 i) _)
      colCert_145_106_3.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_106_4 (hp : 4 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 4 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 4 (transLenTr ⟨106, by decide⟩ 4 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 4 (transLenTr ⟨106, by decide⟩ 4 hp)) T145_106
      hfix145_106 hinj145_106 hcardT145_106
      (fun i => conj_mem_of_fixedPoints _ _ (T145_106 i) (hfix145_106 i) _)
      ⟨145, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 4 hp) Q2.T145_106_2 Q2.hfix145_106_2 Q2.hinj145_106_2
      Q2.hcardT145_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_106_2 i) (Q2.hfix145_106_2 i) _)
      colCert_145_106_4.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_106_5 (hp : 5 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 5 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 5 (transLenTr ⟨106, by decide⟩ 5 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 5 (transLenTr ⟨106, by decide⟩ 5 hp)) T145_106
      hfix145_106 hinj145_106 hcardT145_106
      (fun i => conj_mem_of_fixedPoints _ _ (T145_106 i) (hfix145_106 i) _)
      ⟨145, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 5 hp) Q2.T145_106_2 Q2.hfix145_106_2 Q2.hinj145_106_2
      Q2.hcardT145_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_106_2 i) (Q2.hfix145_106_2 i) _)
      colCert_145_106_5.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_106_10 (hp : 10 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 10 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 10 (transLenTr ⟨106, by decide⟩ 10 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨145, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 10 (transLenTr ⟨106, by decide⟩ 10 hp)) T145_106
      hfix145_106 hinj145_106 hcardT145_106
      (fun i => conj_mem_of_fixedPoints _ _ (T145_106 i) (hfix145_106 i) _)
      ⟨145, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 10 hp) Q2.T145_106_2 Q2.hfix145_106_2 Q2.hinj145_106_2
      Q2.hcardT145_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_106_2 i) (Q2.hfix145_106_2 i) _)
      ?_).symm
  rw [show colData1 (⟨145, by decide⟩ : Fin 148)
        ((colE1 ⟨106, by decide⟩ 10 (transLenTr ⟨106, by decide⟩ 10 hp) : ↥(reps ⟨106, by decide⟩)) : Coordinate 1)
        T145_106 = colFn colCertDiv_145_106_10.D1 (m := 5) from colCertDiv_145_106_10.bind1,
    show colData2 (⟨145, by decide⟩ : Fin 148)
        ((colE2 ⟨106, by decide⟩ 10 hp : ↥(Q2.reps ⟨106, by decide⟩)) : Coordinate 2)
        Q2.T145_106_2 = colFn colCertDiv_145_106_10.D2 (m := 5) from colCertDiv_145_106_10.bind2]
  rw [alnId_145 j hj]
  exact fastcode_of_div ⟨145, by decide⟩ _ _ _
    ((alnId_145 j hj) ▸ Q2.listedAt (⟨145, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨145, by decide⟩ : Fin 148) hj hq).1) colCertDiv_145_106_10_match


theorem leaf_145_106_15 (hp : 15 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 15 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 15 (transLenTr ⟨106, by decide⟩ 15 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨145, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 15 (transLenTr ⟨106, by decide⟩ 15 hp)) T145_106
      hfix145_106 hinj145_106 hcardT145_106
      (fun i => conj_mem_of_fixedPoints _ _ (T145_106 i) (hfix145_106 i) _)
      ⟨145, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 15 hp) Q2.T145_106_2 Q2.hfix145_106_2 Q2.hinj145_106_2
      Q2.hcardT145_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_106_2 i) (Q2.hfix145_106_2 i) _)
      ?_).symm
  rw [show colData1 (⟨145, by decide⟩ : Fin 148)
        ((colE1 ⟨106, by decide⟩ 15 (transLenTr ⟨106, by decide⟩ 15 hp) : ↥(reps ⟨106, by decide⟩)) : Coordinate 1)
        T145_106 = colFn colCertDiv_145_106_15.D1 (m := 5) from colCertDiv_145_106_15.bind1,
    show colData2 (⟨145, by decide⟩ : Fin 148)
        ((colE2 ⟨106, by decide⟩ 15 hp : ↥(Q2.reps ⟨106, by decide⟩)) : Coordinate 2)
        Q2.T145_106_2 = colFn colCertDiv_145_106_15.D2 (m := 5) from colCertDiv_145_106_15.bind2]
  rw [alnId_145 j hj]
  exact fastcode_of_div ⟨145, by decide⟩ _ _ _
    ((alnId_145 j hj) ▸ Q2.listedAt (⟨145, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨145, by decide⟩ : Fin 148) hj hq).1) colCertDiv_145_106_15_match


theorem leaf_145_106_20 (hp : 20 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 20 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 20 (transLenTr ⟨106, by decide⟩ 20 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨145, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 20 (transLenTr ⟨106, by decide⟩ 20 hp)) T145_106
      hfix145_106 hinj145_106 hcardT145_106
      (fun i => conj_mem_of_fixedPoints _ _ (T145_106 i) (hfix145_106 i) _)
      ⟨145, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 20 hp) Q2.T145_106_2 Q2.hfix145_106_2 Q2.hinj145_106_2
      Q2.hcardT145_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_106_2 i) (Q2.hfix145_106_2 i) _)
      ?_).symm
  rw [show colData1 (⟨145, by decide⟩ : Fin 148)
        ((colE1 ⟨106, by decide⟩ 20 (transLenTr ⟨106, by decide⟩ 20 hp) : ↥(reps ⟨106, by decide⟩)) : Coordinate 1)
        T145_106 = colFn colCertDiv_145_106_20.D1 (m := 5) from colCertDiv_145_106_20.bind1,
    show colData2 (⟨145, by decide⟩ : Fin 148)
        ((colE2 ⟨106, by decide⟩ 20 hp : ↥(Q2.reps ⟨106, by decide⟩)) : Coordinate 2)
        Q2.T145_106_2 = colFn colCertDiv_145_106_20.D2 (m := 5) from colCertDiv_145_106_20.bind2]
  rw [alnId_145 j hj]
  exact fastcode_of_div ⟨145, by decide⟩ _ _ _
    ((alnId_145 j hj) ▸ Q2.listedAt (⟨145, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨145, by decide⟩ : Fin 148) hj hq).1) colCertDiv_145_106_20_match


theorem leaf_145_107_0 (hp : 0 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 0 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 0 (transLenTr ⟨107, by decide⟩ 0 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 0 (transLenTr ⟨107, by decide⟩ 0 hp)) T145_107
      hfix145_107 hinj145_107 hcardT145_107
      (fun i => conj_mem_of_fixedPoints _ _ (T145_107 i) (hfix145_107 i) _)
      ⟨145, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 0 hp) Q2.T145_107_2 Q2.hfix145_107_2 Q2.hinj145_107_2
      Q2.hcardT145_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_107_2 i) (Q2.hfix145_107_2 i) _)
      colCert_145_107_0.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_107_1 (hp : 1 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 1 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 1 (transLenTr ⟨107, by decide⟩ 1 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 1 (transLenTr ⟨107, by decide⟩ 1 hp)) T145_107
      hfix145_107 hinj145_107 hcardT145_107
      (fun i => conj_mem_of_fixedPoints _ _ (T145_107 i) (hfix145_107 i) _)
      ⟨145, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 1 hp) Q2.T145_107_2 Q2.hfix145_107_2 Q2.hinj145_107_2
      Q2.hcardT145_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_107_2 i) (Q2.hfix145_107_2 i) _)
      colCert_145_107_1.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_107_2 (hp : 2 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 2 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 2 (transLenTr ⟨107, by decide⟩ 2 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 2 (transLenTr ⟨107, by decide⟩ 2 hp)) T145_107
      hfix145_107 hinj145_107 hcardT145_107
      (fun i => conj_mem_of_fixedPoints _ _ (T145_107 i) (hfix145_107 i) _)
      ⟨145, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 2 hp) Q2.T145_107_2 Q2.hfix145_107_2 Q2.hinj145_107_2
      Q2.hcardT145_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_107_2 i) (Q2.hfix145_107_2 i) _)
      colCert_145_107_2.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_107_3 (hp : 3 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 3 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 3 (transLenTr ⟨107, by decide⟩ 3 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 3 (transLenTr ⟨107, by decide⟩ 3 hp)) T145_107
      hfix145_107 hinj145_107 hcardT145_107
      (fun i => conj_mem_of_fixedPoints _ _ (T145_107 i) (hfix145_107 i) _)
      ⟨145, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 3 hp) Q2.T145_107_2 Q2.hfix145_107_2 Q2.hinj145_107_2
      Q2.hcardT145_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_107_2 i) (Q2.hfix145_107_2 i) _)
      colCert_145_107_3.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_107_4 (hp : 4 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 4 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 4 (transLenTr ⟨107, by decide⟩ 4 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 4 (transLenTr ⟨107, by decide⟩ 4 hp)) T145_107
      hfix145_107 hinj145_107 hcardT145_107
      (fun i => conj_mem_of_fixedPoints _ _ (T145_107 i) (hfix145_107 i) _)
      ⟨145, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 4 hp) Q2.T145_107_2 Q2.hfix145_107_2 Q2.hinj145_107_2
      Q2.hcardT145_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_107_2 i) (Q2.hfix145_107_2 i) _)
      colCert_145_107_4.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_107_5 (hp : 5 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 5 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 5 (transLenTr ⟨107, by decide⟩ 5 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 5 (transLenTr ⟨107, by decide⟩ 5 hp)) T145_107
      hfix145_107 hinj145_107 hcardT145_107
      (fun i => conj_mem_of_fixedPoints _ _ (T145_107 i) (hfix145_107 i) _)
      ⟨145, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 5 hp) Q2.T145_107_2 Q2.hfix145_107_2 Q2.hinj145_107_2
      Q2.hcardT145_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_107_2 i) (Q2.hfix145_107_2 i) _)
      colCert_145_107_5.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_107_10 (hp : 10 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 10 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 10 (transLenTr ⟨107, by decide⟩ 10 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 10 (transLenTr ⟨107, by decide⟩ 10 hp)) T145_107
      hfix145_107 hinj145_107 hcardT145_107
      (fun i => conj_mem_of_fixedPoints _ _ (T145_107 i) (hfix145_107 i) _)
      ⟨145, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 10 hp) Q2.T145_107_2 Q2.hfix145_107_2 Q2.hinj145_107_2
      Q2.hcardT145_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_107_2 i) (Q2.hfix145_107_2 i) _)
      colCert_145_107_10.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_107_15 (hp : 15 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 15 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 15 (transLenTr ⟨107, by decide⟩ 15 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨145, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 15 (transLenTr ⟨107, by decide⟩ 15 hp)) T145_107
      hfix145_107 hinj145_107 hcardT145_107
      (fun i => conj_mem_of_fixedPoints _ _ (T145_107 i) (hfix145_107 i) _)
      ⟨145, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 15 hp) Q2.T145_107_2 Q2.hfix145_107_2 Q2.hinj145_107_2
      Q2.hcardT145_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_107_2 i) (Q2.hfix145_107_2 i) _)
      ?_).symm
  rw [show colData1 (⟨145, by decide⟩ : Fin 148)
        ((colE1 ⟨107, by decide⟩ 15 (transLenTr ⟨107, by decide⟩ 15 hp) : ↥(reps ⟨107, by decide⟩)) : Coordinate 1)
        T145_107 = colFn colCertDiv_145_107_15.D1 (m := 5) from colCertDiv_145_107_15.bind1,
    show colData2 (⟨145, by decide⟩ : Fin 148)
        ((colE2 ⟨107, by decide⟩ 15 hp : ↥(Q2.reps ⟨107, by decide⟩)) : Coordinate 2)
        Q2.T145_107_2 = colFn colCertDiv_145_107_15.D2 (m := 5) from colCertDiv_145_107_15.bind2]
  rw [alnId_145 j hj]
  exact fastcode_of_div ⟨145, by decide⟩ _ _ _
    ((alnId_145 j hj) ▸ Q2.listedAt (⟨145, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨145, by decide⟩ : Fin 148) hj hq).1) colCertDiv_145_107_15_match


theorem leaf_145_107_20 (hp : 20 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 20 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 20 (transLenTr ⟨107, by decide⟩ 20 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨145, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 20 (transLenTr ⟨107, by decide⟩ 20 hp)) T145_107
      hfix145_107 hinj145_107 hcardT145_107
      (fun i => conj_mem_of_fixedPoints _ _ (T145_107 i) (hfix145_107 i) _)
      ⟨145, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 20 hp) Q2.T145_107_2 Q2.hfix145_107_2 Q2.hinj145_107_2
      Q2.hcardT145_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_107_2 i) (Q2.hfix145_107_2 i) _)
      ?_).symm
  rw [show colData1 (⟨145, by decide⟩ : Fin 148)
        ((colE1 ⟨107, by decide⟩ 20 (transLenTr ⟨107, by decide⟩ 20 hp) : ↥(reps ⟨107, by decide⟩)) : Coordinate 1)
        T145_107 = colFn colCertDiv_145_107_20.D1 (m := 5) from colCertDiv_145_107_20.bind1,
    show colData2 (⟨145, by decide⟩ : Fin 148)
        ((colE2 ⟨107, by decide⟩ 20 hp : ↥(Q2.reps ⟨107, by decide⟩)) : Coordinate 2)
        Q2.T145_107_2 = colFn colCertDiv_145_107_20.D2 (m := 5) from colCertDiv_145_107_20.bind2]
  rw [alnId_145 j hj]
  exact fastcode_of_div ⟨145, by decide⟩ _ _ _
    ((alnId_145 j hj) ▸ Q2.listedAt (⟨145, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨145, by decide⟩ : Fin 148) hj hq).1) colCertDiv_145_107_20_match


theorem leaf_145_108_0 (hp : 0 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 0 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 0 (transLenTr ⟨108, by decide⟩ 0 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 0 (transLenTr ⟨108, by decide⟩ 0 hp)) T145_108
      hfix145_108 hinj145_108 hcardT145_108
      (fun i => conj_mem_of_fixedPoints _ _ (T145_108 i) (hfix145_108 i) _)
      ⟨145, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 0 hp) Q2.T145_108_2 Q2.hfix145_108_2 Q2.hinj145_108_2
      Q2.hcardT145_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_108_2 i) (Q2.hfix145_108_2 i) _)
      colCert_145_108_0.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_108_1 (hp : 1 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 1 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 1 (transLenTr ⟨108, by decide⟩ 1 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 1 (transLenTr ⟨108, by decide⟩ 1 hp)) T145_108
      hfix145_108 hinj145_108 hcardT145_108
      (fun i => conj_mem_of_fixedPoints _ _ (T145_108 i) (hfix145_108 i) _)
      ⟨145, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 1 hp) Q2.T145_108_2 Q2.hfix145_108_2 Q2.hinj145_108_2
      Q2.hcardT145_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_108_2 i) (Q2.hfix145_108_2 i) _)
      colCert_145_108_1.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_108_2 (hp : 2 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 2 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 2 (transLenTr ⟨108, by decide⟩ 2 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 2 (transLenTr ⟨108, by decide⟩ 2 hp)) T145_108
      hfix145_108 hinj145_108 hcardT145_108
      (fun i => conj_mem_of_fixedPoints _ _ (T145_108 i) (hfix145_108 i) _)
      ⟨145, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 2 hp) Q2.T145_108_2 Q2.hfix145_108_2 Q2.hinj145_108_2
      Q2.hcardT145_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_108_2 i) (Q2.hfix145_108_2 i) _)
      colCert_145_108_2.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_108_3 (hp : 3 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 3 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 3 (transLenTr ⟨108, by decide⟩ 3 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 3 (transLenTr ⟨108, by decide⟩ 3 hp)) T145_108
      hfix145_108 hinj145_108 hcardT145_108
      (fun i => conj_mem_of_fixedPoints _ _ (T145_108 i) (hfix145_108 i) _)
      ⟨145, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 3 hp) Q2.T145_108_2 Q2.hfix145_108_2 Q2.hinj145_108_2
      Q2.hcardT145_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_108_2 i) (Q2.hfix145_108_2 i) _)
      colCert_145_108_3.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_108_4 (hp : 4 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 4 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 4 (transLenTr ⟨108, by decide⟩ 4 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 4 (transLenTr ⟨108, by decide⟩ 4 hp)) T145_108
      hfix145_108 hinj145_108 hcardT145_108
      (fun i => conj_mem_of_fixedPoints _ _ (T145_108 i) (hfix145_108 i) _)
      ⟨145, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 4 hp) Q2.T145_108_2 Q2.hfix145_108_2 Q2.hinj145_108_2
      Q2.hcardT145_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_108_2 i) (Q2.hfix145_108_2 i) _)
      colCert_145_108_4.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_108_5 (hp : 5 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 5 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 5 (transLenTr ⟨108, by decide⟩ 5 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 5 (transLenTr ⟨108, by decide⟩ 5 hp)) T145_108
      hfix145_108 hinj145_108 hcardT145_108
      (fun i => conj_mem_of_fixedPoints _ _ (T145_108 i) (hfix145_108 i) _)
      ⟨145, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 5 hp) Q2.T145_108_2 Q2.hfix145_108_2 Q2.hinj145_108_2
      Q2.hcardT145_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_108_2 i) (Q2.hfix145_108_2 i) _)
      colCert_145_108_5.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_108_10 (hp : 10 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 10 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 10 (transLenTr ⟨108, by decide⟩ 10 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨145, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 10 (transLenTr ⟨108, by decide⟩ 10 hp)) T145_108
      hfix145_108 hinj145_108 hcardT145_108
      (fun i => conj_mem_of_fixedPoints _ _ (T145_108 i) (hfix145_108 i) _)
      ⟨145, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 10 hp) Q2.T145_108_2 Q2.hfix145_108_2 Q2.hinj145_108_2
      Q2.hcardT145_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_108_2 i) (Q2.hfix145_108_2 i) _)
      ?_).symm
  rw [show colData1 (⟨145, by decide⟩ : Fin 148)
        ((colE1 ⟨108, by decide⟩ 10 (transLenTr ⟨108, by decide⟩ 10 hp) : ↥(reps ⟨108, by decide⟩)) : Coordinate 1)
        T145_108 = colFn colCertDiv_145_108_10.D1 (m := 5) from colCertDiv_145_108_10.bind1,
    show colData2 (⟨145, by decide⟩ : Fin 148)
        ((colE2 ⟨108, by decide⟩ 10 hp : ↥(Q2.reps ⟨108, by decide⟩)) : Coordinate 2)
        Q2.T145_108_2 = colFn colCertDiv_145_108_10.D2 (m := 5) from colCertDiv_145_108_10.bind2]
  rw [alnId_145 j hj]
  exact fastcode_of_div ⟨145, by decide⟩ _ _ _
    ((alnId_145 j hj) ▸ Q2.listedAt (⟨145, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨145, by decide⟩ : Fin 148) hj hq).1) colCertDiv_145_108_10_match


theorem leaf_145_108_15 (hp : 15 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 15 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 15 (transLenTr ⟨108, by decide⟩ 15 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨145, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 15 (transLenTr ⟨108, by decide⟩ 15 hp)) T145_108
      hfix145_108 hinj145_108 hcardT145_108
      (fun i => conj_mem_of_fixedPoints _ _ (T145_108 i) (hfix145_108 i) _)
      ⟨145, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 15 hp) Q2.T145_108_2 Q2.hfix145_108_2 Q2.hinj145_108_2
      Q2.hcardT145_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_108_2 i) (Q2.hfix145_108_2 i) _)
      ?_).symm
  rw [show colData1 (⟨145, by decide⟩ : Fin 148)
        ((colE1 ⟨108, by decide⟩ 15 (transLenTr ⟨108, by decide⟩ 15 hp) : ↥(reps ⟨108, by decide⟩)) : Coordinate 1)
        T145_108 = colFn colCertDiv_145_108_15.D1 (m := 5) from colCertDiv_145_108_15.bind1,
    show colData2 (⟨145, by decide⟩ : Fin 148)
        ((colE2 ⟨108, by decide⟩ 15 hp : ↥(Q2.reps ⟨108, by decide⟩)) : Coordinate 2)
        Q2.T145_108_2 = colFn colCertDiv_145_108_15.D2 (m := 5) from colCertDiv_145_108_15.bind2]
  rw [alnId_145 j hj]
  exact fastcode_of_div ⟨145, by decide⟩ _ _ _
    ((alnId_145 j hj) ▸ Q2.listedAt (⟨145, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨145, by decide⟩ : Fin 148) hj hq).1) colCertDiv_145_108_15_match


theorem leaf_145_108_20 (hp : 20 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 20 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 20 (transLenTr ⟨108, by decide⟩ 20 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨145, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 20 (transLenTr ⟨108, by decide⟩ 20 hp)) T145_108
      hfix145_108 hinj145_108 hcardT145_108
      (fun i => conj_mem_of_fixedPoints _ _ (T145_108 i) (hfix145_108 i) _)
      ⟨145, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 20 hp) Q2.T145_108_2 Q2.hfix145_108_2 Q2.hinj145_108_2
      Q2.hcardT145_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_108_2 i) (Q2.hfix145_108_2 i) _)
      ?_).symm
  rw [show colData1 (⟨145, by decide⟩ : Fin 148)
        ((colE1 ⟨108, by decide⟩ 20 (transLenTr ⟨108, by decide⟩ 20 hp) : ↥(reps ⟨108, by decide⟩)) : Coordinate 1)
        T145_108 = colFn colCertDiv_145_108_20.D1 (m := 5) from colCertDiv_145_108_20.bind1,
    show colData2 (⟨145, by decide⟩ : Fin 148)
        ((colE2 ⟨108, by decide⟩ 20 hp : ↥(Q2.reps ⟨108, by decide⟩)) : Coordinate 2)
        Q2.T145_108_2 = colFn colCertDiv_145_108_20.D2 (m := 5) from colCertDiv_145_108_20.bind2]
  rw [alnId_145 j hj]
  exact fastcode_of_div ⟨145, by decide⟩ _ _ _
    ((alnId_145 j hj) ▸ Q2.listedAt (⟨145, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨145, by decide⟩ : Fin 148) hj hq).1) colCertDiv_145_108_20_match


theorem leaf_145_109_0 (hp : 0 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 0 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 0 (transLenTr ⟨109, by decide⟩ 0 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 0 (transLenTr ⟨109, by decide⟩ 0 hp)) T145_109
      hfix145_109 hinj145_109 hcardT145_109
      (fun i => conj_mem_of_fixedPoints _ _ (T145_109 i) (hfix145_109 i) _)
      ⟨145, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 0 hp) Q2.T145_109_2 Q2.hfix145_109_2 Q2.hinj145_109_2
      Q2.hcardT145_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_109_2 i) (Q2.hfix145_109_2 i) _)
      colCert_145_109_0.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_109_1 (hp : 1 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 1 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 1 (transLenTr ⟨109, by decide⟩ 1 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 1 (transLenTr ⟨109, by decide⟩ 1 hp)) T145_109
      hfix145_109 hinj145_109 hcardT145_109
      (fun i => conj_mem_of_fixedPoints _ _ (T145_109 i) (hfix145_109 i) _)
      ⟨145, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 1 hp) Q2.T145_109_2 Q2.hfix145_109_2 Q2.hinj145_109_2
      Q2.hcardT145_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_109_2 i) (Q2.hfix145_109_2 i) _)
      colCert_145_109_1.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_109_2 (hp : 2 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 2 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 2 (transLenTr ⟨109, by decide⟩ 2 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 2 (transLenTr ⟨109, by decide⟩ 2 hp)) T145_109
      hfix145_109 hinj145_109 hcardT145_109
      (fun i => conj_mem_of_fixedPoints _ _ (T145_109 i) (hfix145_109 i) _)
      ⟨145, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 2 hp) Q2.T145_109_2 Q2.hfix145_109_2 Q2.hinj145_109_2
      Q2.hcardT145_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_109_2 i) (Q2.hfix145_109_2 i) _)
      colCert_145_109_2.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_109_3 (hp : 3 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 3 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 3 (transLenTr ⟨109, by decide⟩ 3 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 3 (transLenTr ⟨109, by decide⟩ 3 hp)) T145_109
      hfix145_109 hinj145_109 hcardT145_109
      (fun i => conj_mem_of_fixedPoints _ _ (T145_109 i) (hfix145_109 i) _)
      ⟨145, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 3 hp) Q2.T145_109_2 Q2.hfix145_109_2 Q2.hinj145_109_2
      Q2.hcardT145_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_109_2 i) (Q2.hfix145_109_2 i) _)
      colCert_145_109_3.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_109_4 (hp : 4 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 4 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 4 (transLenTr ⟨109, by decide⟩ 4 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 4 (transLenTr ⟨109, by decide⟩ 4 hp)) T145_109
      hfix145_109 hinj145_109 hcardT145_109
      (fun i => conj_mem_of_fixedPoints _ _ (T145_109 i) (hfix145_109 i) _)
      ⟨145, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 4 hp) Q2.T145_109_2 Q2.hfix145_109_2 Q2.hinj145_109_2
      Q2.hcardT145_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_109_2 i) (Q2.hfix145_109_2 i) _)
      colCert_145_109_4.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_109_5 (hp : 5 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 5 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 5 (transLenTr ⟨109, by decide⟩ 5 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 5 (transLenTr ⟨109, by decide⟩ 5 hp)) T145_109
      hfix145_109 hinj145_109 hcardT145_109
      (fun i => conj_mem_of_fixedPoints _ _ (T145_109 i) (hfix145_109 i) _)
      ⟨145, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 5 hp) Q2.T145_109_2 Q2.hfix145_109_2 Q2.hinj145_109_2
      Q2.hcardT145_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_109_2 i) (Q2.hfix145_109_2 i) _)
      colCert_145_109_5.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_109_10 (hp : 10 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 10 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 10 (transLenTr ⟨109, by decide⟩ 10 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 10 (transLenTr ⟨109, by decide⟩ 10 hp)) T145_109
      hfix145_109 hinj145_109 hcardT145_109
      (fun i => conj_mem_of_fixedPoints _ _ (T145_109 i) (hfix145_109 i) _)
      ⟨145, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 10 hp) Q2.T145_109_2 Q2.hfix145_109_2 Q2.hinj145_109_2
      Q2.hcardT145_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_109_2 i) (Q2.hfix145_109_2 i) _)
      colCert_145_109_10.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_109_15 (hp : 15 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 15 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 15 (transLenTr ⟨109, by decide⟩ 15 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 15 (transLenTr ⟨109, by decide⟩ 15 hp)) T145_109
      hfix145_109 hinj145_109 hcardT145_109
      (fun i => conj_mem_of_fixedPoints _ _ (T145_109 i) (hfix145_109 i) _)
      ⟨145, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 15 hp) Q2.T145_109_2 Q2.hfix145_109_2 Q2.hinj145_109_2
      Q2.hcardT145_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_109_2 i) (Q2.hfix145_109_2 i) _)
      colCert_145_109_15.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_109_20 (hp : 20 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 20 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 20 (transLenTr ⟨109, by decide⟩ 20 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 20 (transLenTr ⟨109, by decide⟩ 20 hp)) T145_109
      hfix145_109 hinj145_109 hcardT145_109
      (fun i => conj_mem_of_fixedPoints _ _ (T145_109 i) (hfix145_109 i) _)
      ⟨145, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 20 hp) Q2.T145_109_2 Q2.hfix145_109_2 Q2.hinj145_109_2
      Q2.hcardT145_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_109_2 i) (Q2.hfix145_109_2 i) _)
      colCert_145_109_20.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_115_0 (hp : 0 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 0 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 0 (transLenTr ⟨115, by decide⟩ 0 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 0 (transLenTr ⟨115, by decide⟩ 0 hp)) T145_115
      hfix145_115 hinj145_115 hcardT145_115
      (fun i => conj_mem_of_fixedPoints _ _ (T145_115 i) (hfix145_115 i) _)
      ⟨145, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 0 hp) Q2.T145_115_2 Q2.hfix145_115_2 Q2.hinj145_115_2
      Q2.hcardT145_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_115_2 i) (Q2.hfix145_115_2 i) _)
      colCert_145_115_0.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_115_1 (hp : 1 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 1 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 1 (transLenTr ⟨115, by decide⟩ 1 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 1 (transLenTr ⟨115, by decide⟩ 1 hp)) T145_115
      hfix145_115 hinj145_115 hcardT145_115
      (fun i => conj_mem_of_fixedPoints _ _ (T145_115 i) (hfix145_115 i) _)
      ⟨145, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 1 hp) Q2.T145_115_2 Q2.hfix145_115_2 Q2.hinj145_115_2
      Q2.hcardT145_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_115_2 i) (Q2.hfix145_115_2 i) _)
      colCert_145_115_1.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_115_2 (hp : 2 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 2 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 2 (transLenTr ⟨115, by decide⟩ 2 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 2 (transLenTr ⟨115, by decide⟩ 2 hp)) T145_115
      hfix145_115 hinj145_115 hcardT145_115
      (fun i => conj_mem_of_fixedPoints _ _ (T145_115 i) (hfix145_115 i) _)
      ⟨145, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 2 hp) Q2.T145_115_2 Q2.hfix145_115_2 Q2.hinj145_115_2
      Q2.hcardT145_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_115_2 i) (Q2.hfix145_115_2 i) _)
      colCert_145_115_2.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_115_3 (hp : 3 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 3 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 3 (transLenTr ⟨115, by decide⟩ 3 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 3 (transLenTr ⟨115, by decide⟩ 3 hp)) T145_115
      hfix145_115 hinj145_115 hcardT145_115
      (fun i => conj_mem_of_fixedPoints _ _ (T145_115 i) (hfix145_115 i) _)
      ⟨145, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 3 hp) Q2.T145_115_2 Q2.hfix145_115_2 Q2.hinj145_115_2
      Q2.hcardT145_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_115_2 i) (Q2.hfix145_115_2 i) _)
      colCert_145_115_3.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_115_4 (hp : 4 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 4 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 4 (transLenTr ⟨115, by decide⟩ 4 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 4 (transLenTr ⟨115, by decide⟩ 4 hp)) T145_115
      hfix145_115 hinj145_115 hcardT145_115
      (fun i => conj_mem_of_fixedPoints _ _ (T145_115 i) (hfix145_115 i) _)
      ⟨145, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 4 hp) Q2.T145_115_2 Q2.hfix145_115_2 Q2.hinj145_115_2
      Q2.hcardT145_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_115_2 i) (Q2.hfix145_115_2 i) _)
      colCert_145_115_4.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_115_5 (hp : 5 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 5 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 5 (transLenTr ⟨115, by decide⟩ 5 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 5 (transLenTr ⟨115, by decide⟩ 5 hp)) T145_115
      hfix145_115 hinj145_115 hcardT145_115
      (fun i => conj_mem_of_fixedPoints _ _ (T145_115 i) (hfix145_115 i) _)
      ⟨145, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 5 hp) Q2.T145_115_2 Q2.hfix145_115_2 Q2.hinj145_115_2
      Q2.hcardT145_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_115_2 i) (Q2.hfix145_115_2 i) _)
      colCert_145_115_5.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_115_10 (hp : 10 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 10 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 10 (transLenTr ⟨115, by decide⟩ 10 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 10 (transLenTr ⟨115, by decide⟩ 10 hp)) T145_115
      hfix145_115 hinj145_115 hcardT145_115
      (fun i => conj_mem_of_fixedPoints _ _ (T145_115 i) (hfix145_115 i) _)
      ⟨145, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 10 hp) Q2.T145_115_2 Q2.hfix145_115_2 Q2.hinj145_115_2
      Q2.hcardT145_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_115_2 i) (Q2.hfix145_115_2 i) _)
      colCert_145_115_10.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_115_15 (hp : 15 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 15 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 15 (transLenTr ⟨115, by decide⟩ 15 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 15 (transLenTr ⟨115, by decide⟩ 15 hp)) T145_115
      hfix145_115 hinj145_115 hcardT145_115
      (fun i => conj_mem_of_fixedPoints _ _ (T145_115 i) (hfix145_115 i) _)
      ⟨145, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 15 hp) Q2.T145_115_2 Q2.hfix145_115_2 Q2.hinj145_115_2
      Q2.hcardT145_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_115_2 i) (Q2.hfix145_115_2 i) _)
      colCert_145_115_15.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_115_20 (hp : 20 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 20 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 20 (transLenTr ⟨115, by decide⟩ 20 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 20 (transLenTr ⟨115, by decide⟩ 20 hp)) T145_115
      hfix145_115 hinj145_115 hcardT145_115
      (fun i => conj_mem_of_fixedPoints _ _ (T145_115 i) (hfix145_115 i) _)
      ⟨145, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 20 hp) Q2.T145_115_2 Q2.hfix145_115_2 Q2.hinj145_115_2
      Q2.hcardT145_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_115_2 i) (Q2.hfix145_115_2 i) _)
      colCert_145_115_20.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_145_0 (hp : 0 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 0 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 0 (transLenTr ⟨145, by decide⟩ 0 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 0 (transLenTr ⟨145, by decide⟩ 0 hp)) T145_145
      hfix145_145 hinj145_145 hcardT145_145
      (fun i => conj_mem_of_fixedPoints _ _ (T145_145 i) (hfix145_145 i) _)
      ⟨145, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 0 hp) Q2.T145_145_2 Q2.hfix145_145_2 Q2.hinj145_145_2
      Q2.hcardT145_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_145_2 i) (Q2.hfix145_145_2 i) _)
      colCert_145_145_0.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_145_1 (hp : 1 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 1 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 1 (transLenTr ⟨145, by decide⟩ 1 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 1 (transLenTr ⟨145, by decide⟩ 1 hp)) T145_145
      hfix145_145 hinj145_145 hcardT145_145
      (fun i => conj_mem_of_fixedPoints _ _ (T145_145 i) (hfix145_145 i) _)
      ⟨145, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 1 hp) Q2.T145_145_2 Q2.hfix145_145_2 Q2.hinj145_145_2
      Q2.hcardT145_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_145_2 i) (Q2.hfix145_145_2 i) _)
      colCert_145_145_1.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_145_2 (hp : 2 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 2 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 2 (transLenTr ⟨145, by decide⟩ 2 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 2 (transLenTr ⟨145, by decide⟩ 2 hp)) T145_145
      hfix145_145 hinj145_145 hcardT145_145
      (fun i => conj_mem_of_fixedPoints _ _ (T145_145 i) (hfix145_145 i) _)
      ⟨145, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 2 hp) Q2.T145_145_2 Q2.hfix145_145_2 Q2.hinj145_145_2
      Q2.hcardT145_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_145_2 i) (Q2.hfix145_145_2 i) _)
      colCert_145_145_2.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_145_3 (hp : 3 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 3 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 3 (transLenTr ⟨145, by decide⟩ 3 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 3 (transLenTr ⟨145, by decide⟩ 3 hp)) T145_145
      hfix145_145 hinj145_145 hcardT145_145
      (fun i => conj_mem_of_fixedPoints _ _ (T145_145 i) (hfix145_145 i) _)
      ⟨145, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 3 hp) Q2.T145_145_2 Q2.hfix145_145_2 Q2.hinj145_145_2
      Q2.hcardT145_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_145_2 i) (Q2.hfix145_145_2 i) _)
      colCert_145_145_3.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_145_4 (hp : 4 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 4 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 4 (transLenTr ⟨145, by decide⟩ 4 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 4 (transLenTr ⟨145, by decide⟩ 4 hp)) T145_145
      hfix145_145 hinj145_145 hcardT145_145
      (fun i => conj_mem_of_fixedPoints _ _ (T145_145 i) (hfix145_145 i) _)
      ⟨145, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 4 hp) Q2.T145_145_2 Q2.hfix145_145_2 Q2.hinj145_145_2
      Q2.hcardT145_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_145_2 i) (Q2.hfix145_145_2 i) _)
      colCert_145_145_4.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_145_5 (hp : 5 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 5 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 5 (transLenTr ⟨145, by decide⟩ 5 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 5 (transLenTr ⟨145, by decide⟩ 5 hp)) T145_145
      hfix145_145 hinj145_145 hcardT145_145
      (fun i => conj_mem_of_fixedPoints _ _ (T145_145 i) (hfix145_145 i) _)
      ⟨145, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 5 hp) Q2.T145_145_2 Q2.hfix145_145_2 Q2.hinj145_145_2
      Q2.hcardT145_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_145_2 i) (Q2.hfix145_145_2 i) _)
      colCert_145_145_5.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_145_6 (hp : 6 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 6 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 6 (transLenTr ⟨145, by decide⟩ 6 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 6 (transLenTr ⟨145, by decide⟩ 6 hp)) T145_145
      hfix145_145 hinj145_145 hcardT145_145
      (fun i => conj_mem_of_fixedPoints _ _ (T145_145 i) (hfix145_145 i) _)
      ⟨145, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 6 hp) Q2.T145_145_2 Q2.hfix145_145_2 Q2.hinj145_145_2
      Q2.hcardT145_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_145_2 i) (Q2.hfix145_145_2 i) _)
      colCert_145_145_6.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_145_7 (hp : 7 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 7 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 7 (transLenTr ⟨145, by decide⟩ 7 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 7 (transLenTr ⟨145, by decide⟩ 7 hp)) T145_145
      hfix145_145 hinj145_145 hcardT145_145
      (fun i => conj_mem_of_fixedPoints _ _ (T145_145 i) (hfix145_145 i) _)
      ⟨145, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 7 hp) Q2.T145_145_2 Q2.hfix145_145_2 Q2.hinj145_145_2
      Q2.hcardT145_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_145_2 i) (Q2.hfix145_145_2 i) _)
      colCert_145_145_7.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_145_8 (hp : 8 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 8 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 8 (transLenTr ⟨145, by decide⟩ 8 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 8 (transLenTr ⟨145, by decide⟩ 8 hp)) T145_145
      hfix145_145 hinj145_145 hcardT145_145
      (fun i => conj_mem_of_fixedPoints _ _ (T145_145 i) (hfix145_145 i) _)
      ⟨145, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 8 hp) Q2.T145_145_2 Q2.hfix145_145_2 Q2.hinj145_145_2
      Q2.hcardT145_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_145_2 i) (Q2.hfix145_145_2 i) _)
      colCert_145_145_8.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_145_9 (hp : 9 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 9 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 9 (transLenTr ⟨145, by decide⟩ 9 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 9 (transLenTr ⟨145, by decide⟩ 9 hp)) T145_145
      hfix145_145 hinj145_145 hcardT145_145
      (fun i => conj_mem_of_fixedPoints _ _ (T145_145 i) (hfix145_145 i) _)
      ⟨145, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 9 hp) Q2.T145_145_2 Q2.hfix145_145_2 Q2.hinj145_145_2
      Q2.hcardT145_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_145_2 i) (Q2.hfix145_145_2 i) _)
      colCert_145_145_9.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_145_10 (hp : 10 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 10 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 10 (transLenTr ⟨145, by decide⟩ 10 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 10 (transLenTr ⟨145, by decide⟩ 10 hp)) T145_145
      hfix145_145 hinj145_145 hcardT145_145
      (fun i => conj_mem_of_fixedPoints _ _ (T145_145 i) (hfix145_145 i) _)
      ⟨145, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 10 hp) Q2.T145_145_2 Q2.hfix145_145_2 Q2.hinj145_145_2
      Q2.hcardT145_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_145_2 i) (Q2.hfix145_145_2 i) _)
      colCert_145_145_10.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_145_11 (hp : 11 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 11 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 11 (transLenTr ⟨145, by decide⟩ 11 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 11 (transLenTr ⟨145, by decide⟩ 11 hp)) T145_145
      hfix145_145 hinj145_145 hcardT145_145
      (fun i => conj_mem_of_fixedPoints _ _ (T145_145 i) (hfix145_145 i) _)
      ⟨145, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 11 hp) Q2.T145_145_2 Q2.hfix145_145_2 Q2.hinj145_145_2
      Q2.hcardT145_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_145_2 i) (Q2.hfix145_145_2 i) _)
      colCert_145_145_11.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_145_12 (hp : 12 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 12 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 12 (transLenTr ⟨145, by decide⟩ 12 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 12 (transLenTr ⟨145, by decide⟩ 12 hp)) T145_145
      hfix145_145 hinj145_145 hcardT145_145
      (fun i => conj_mem_of_fixedPoints _ _ (T145_145 i) (hfix145_145 i) _)
      ⟨145, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 12 hp) Q2.T145_145_2 Q2.hfix145_145_2 Q2.hinj145_145_2
      Q2.hcardT145_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_145_2 i) (Q2.hfix145_145_2 i) _)
      colCert_145_145_12.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_145_13 (hp : 13 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 13 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 13 (transLenTr ⟨145, by decide⟩ 13 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 13 (transLenTr ⟨145, by decide⟩ 13 hp)) T145_145
      hfix145_145 hinj145_145 hcardT145_145
      (fun i => conj_mem_of_fixedPoints _ _ (T145_145 i) (hfix145_145 i) _)
      ⟨145, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 13 hp) Q2.T145_145_2 Q2.hfix145_145_2 Q2.hinj145_145_2
      Q2.hcardT145_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_145_2 i) (Q2.hfix145_145_2 i) _)
      colCert_145_145_13.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_145_14 (hp : 14 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 14 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 14 (transLenTr ⟨145, by decide⟩ 14 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 14 (transLenTr ⟨145, by decide⟩ 14 hp)) T145_145
      hfix145_145 hinj145_145 hcardT145_145
      (fun i => conj_mem_of_fixedPoints _ _ (T145_145 i) (hfix145_145 i) _)
      ⟨145, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 14 hp) Q2.T145_145_2 Q2.hfix145_145_2 Q2.hinj145_145_2
      Q2.hcardT145_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_145_2 i) (Q2.hfix145_145_2 i) _)
      colCert_145_145_14.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_145_15 (hp : 15 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 15 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 15 (transLenTr ⟨145, by decide⟩ 15 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 15 (transLenTr ⟨145, by decide⟩ 15 hp)) T145_145
      hfix145_145 hinj145_145 hcardT145_145
      (fun i => conj_mem_of_fixedPoints _ _ (T145_145 i) (hfix145_145 i) _)
      ⟨145, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 15 hp) Q2.T145_145_2 Q2.hfix145_145_2 Q2.hinj145_145_2
      Q2.hcardT145_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_145_2 i) (Q2.hfix145_145_2 i) _)
      colCert_145_145_15.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_145_16 (hp : 16 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 16 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 16 (transLenTr ⟨145, by decide⟩ 16 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 16 (transLenTr ⟨145, by decide⟩ 16 hp)) T145_145
      hfix145_145 hinj145_145 hcardT145_145
      (fun i => conj_mem_of_fixedPoints _ _ (T145_145 i) (hfix145_145 i) _)
      ⟨145, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 16 hp) Q2.T145_145_2 Q2.hfix145_145_2 Q2.hinj145_145_2
      Q2.hcardT145_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_145_2 i) (Q2.hfix145_145_2 i) _)
      colCert_145_145_16.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_145_17 (hp : 17 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 17 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 17 (transLenTr ⟨145, by decide⟩ 17 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 17 (transLenTr ⟨145, by decide⟩ 17 hp)) T145_145
      hfix145_145 hinj145_145 hcardT145_145
      (fun i => conj_mem_of_fixedPoints _ _ (T145_145 i) (hfix145_145 i) _)
      ⟨145, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 17 hp) Q2.T145_145_2 Q2.hfix145_145_2 Q2.hinj145_145_2
      Q2.hcardT145_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_145_2 i) (Q2.hfix145_145_2 i) _)
      colCert_145_145_17.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_145_18 (hp : 18 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 18 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 18 (transLenTr ⟨145, by decide⟩ 18 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 18 (transLenTr ⟨145, by decide⟩ 18 hp)) T145_145
      hfix145_145 hinj145_145 hcardT145_145
      (fun i => conj_mem_of_fixedPoints _ _ (T145_145 i) (hfix145_145 i) _)
      ⟨145, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 18 hp) Q2.T145_145_2 Q2.hfix145_145_2 Q2.hinj145_145_2
      Q2.hcardT145_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_145_2 i) (Q2.hfix145_145_2 i) _)
      colCert_145_145_18.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_145_19 (hp : 19 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 19 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 19 (transLenTr ⟨145, by decide⟩ 19 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 19 (transLenTr ⟨145, by decide⟩ 19 hp)) T145_145
      hfix145_145 hinj145_145 hcardT145_145
      (fun i => conj_mem_of_fixedPoints _ _ (T145_145 i) (hfix145_145 i) _)
      ⟨145, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 19 hp) Q2.T145_145_2 Q2.hfix145_145_2 Q2.hinj145_145_2
      Q2.hcardT145_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_145_2 i) (Q2.hfix145_145_2 i) _)
      colCert_145_145_19.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_145_20 (hp : 20 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 20 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 20 (transLenTr ⟨145, by decide⟩ 20 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 20 (transLenTr ⟨145, by decide⟩ 20 hp)) T145_145
      hfix145_145 hinj145_145 hcardT145_145
      (fun i => conj_mem_of_fixedPoints _ _ (T145_145 i) (hfix145_145 i) _)
      ⟨145, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 20 hp) Q2.T145_145_2 Q2.hfix145_145_2 Q2.hinj145_145_2
      Q2.hcardT145_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_145_2 i) (Q2.hfix145_145_2 i) _)
      colCert_145_145_20.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_145_21 (hp : 21 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 21 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 21 (transLenTr ⟨145, by decide⟩ 21 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 21 (transLenTr ⟨145, by decide⟩ 21 hp)) T145_145
      hfix145_145 hinj145_145 hcardT145_145
      (fun i => conj_mem_of_fixedPoints _ _ (T145_145 i) (hfix145_145 i) _)
      ⟨145, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 21 hp) Q2.T145_145_2 Q2.hfix145_145_2 Q2.hinj145_145_2
      Q2.hcardT145_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_145_2 i) (Q2.hfix145_145_2 i) _)
      colCert_145_145_21.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_145_22 (hp : 22 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 22 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 22 (transLenTr ⟨145, by decide⟩ 22 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 22 (transLenTr ⟨145, by decide⟩ 22 hp)) T145_145
      hfix145_145 hinj145_145 hcardT145_145
      (fun i => conj_mem_of_fixedPoints _ _ (T145_145 i) (hfix145_145 i) _)
      ⟨145, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 22 hp) Q2.T145_145_2 Q2.hfix145_145_2 Q2.hinj145_145_2
      Q2.hcardT145_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_145_2 i) (Q2.hfix145_145_2 i) _)
      colCert_145_145_22.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_145_23 (hp : 23 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 23 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 23 (transLenTr ⟨145, by decide⟩ 23 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 23 (transLenTr ⟨145, by decide⟩ 23 hp)) T145_145
      hfix145_145 hinj145_145 hcardT145_145
      (fun i => conj_mem_of_fixedPoints _ _ (T145_145 i) (hfix145_145 i) _)
      ⟨145, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 23 hp) Q2.T145_145_2 Q2.hfix145_145_2 Q2.hinj145_145_2
      Q2.hcardT145_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_145_2 i) (Q2.hfix145_145_2 i) _)
      colCert_145_145_23.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_145_24 (hp : 24 < (Q2.transData.getD 145 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ 24 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ 24 (transLenTr ⟨145, by decide⟩ 24 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨145, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨145, by decide⟩ 24 (transLenTr ⟨145, by decide⟩ 24 hp)) T145_145
      hfix145_145 hinj145_145 hcardT145_145
      (fun i => conj_mem_of_fixedPoints _ _ (T145_145 i) (hfix145_145 i) _)
      ⟨145, by decide⟩ ⟨145, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨145, by decide⟩ 24 hp) Q2.T145_145_2 Q2.hfix145_145_2 Q2.hinj145_145_2
      Q2.hcardT145_145_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_145_2 i) (Q2.hfix145_145_2 i) _)
      colCert_145_145_24.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_146_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T146_10
      hfix146_10 hinj146_10 hcardT146_10
      (fun i => conj_mem_of_fixedPoints _ _ (T146_10 i) (hfix146_10 i) _)
      ⟨146, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T146_10_2 Q2.hfix146_10_2 Q2.hinj146_10_2
      Q2.hcardT146_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_10_2 i) (Q2.hfix146_10_2 i) _)
      colCert_146_10_0.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T146_10
      hfix146_10 hinj146_10 hcardT146_10
      (fun i => conj_mem_of_fixedPoints _ _ (T146_10 i) (hfix146_10 i) _)
      ⟨146, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T146_10_2 Q2.hfix146_10_2 Q2.hinj146_10_2
      Q2.hcardT146_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_10_2 i) (Q2.hfix146_10_2 i) _)
      colCert_146_10_1.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T146_10
      hfix146_10 hinj146_10 hcardT146_10
      (fun i => conj_mem_of_fixedPoints _ _ (T146_10 i) (hfix146_10 i) _)
      ⟨146, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T146_10_2 Q2.hfix146_10_2 Q2.hinj146_10_2
      Q2.hcardT146_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_10_2 i) (Q2.hfix146_10_2 i) _)
      colCert_146_10_2.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T146_10
      hfix146_10 hinj146_10 hcardT146_10
      (fun i => conj_mem_of_fixedPoints _ _ (T146_10 i) (hfix146_10 i) _)
      ⟨146, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T146_10_2 Q2.hfix146_10_2 Q2.hinj146_10_2
      Q2.hcardT146_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_10_2 i) (Q2.hfix146_10_2 i) _)
      colCert_146_10_3.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T146_10
      hfix146_10 hinj146_10 hcardT146_10
      (fun i => conj_mem_of_fixedPoints _ _ (T146_10 i) (hfix146_10 i) _)
      ⟨146, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T146_10_2 Q2.hfix146_10_2 Q2.hinj146_10_2
      Q2.hcardT146_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_10_2 i) (Q2.hfix146_10_2 i) _)
      colCert_146_10_4.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_11_0 (hp : 0 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 0 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp)) T146_11
      hfix146_11 hinj146_11 hcardT146_11
      (fun i => conj_mem_of_fixedPoints _ _ (T146_11 i) (hfix146_11 i) _)
      ⟨146, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 0 hp) Q2.T146_11_2 Q2.hfix146_11_2 Q2.hinj146_11_2
      Q2.hcardT146_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_11_2 i) (Q2.hfix146_11_2 i) _)
      colCert_146_11_0.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_11_1 (hp : 1 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 1 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp)) T146_11
      hfix146_11 hinj146_11 hcardT146_11
      (fun i => conj_mem_of_fixedPoints _ _ (T146_11 i) (hfix146_11 i) _)
      ⟨146, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 1 hp) Q2.T146_11_2 Q2.hfix146_11_2 Q2.hinj146_11_2
      Q2.hcardT146_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_11_2 i) (Q2.hfix146_11_2 i) _)
      colCert_146_11_1.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_11_2 (hp : 2 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 2 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp)) T146_11
      hfix146_11 hinj146_11 hcardT146_11
      (fun i => conj_mem_of_fixedPoints _ _ (T146_11 i) (hfix146_11 i) _)
      ⟨146, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 2 hp) Q2.T146_11_2 Q2.hfix146_11_2 Q2.hinj146_11_2
      Q2.hcardT146_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_11_2 i) (Q2.hfix146_11_2 i) _)
      colCert_146_11_2.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_11_3 (hp : 3 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 3 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp)) T146_11
      hfix146_11 hinj146_11 hcardT146_11
      (fun i => conj_mem_of_fixedPoints _ _ (T146_11 i) (hfix146_11 i) _)
      ⟨146, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 3 hp) Q2.T146_11_2 Q2.hfix146_11_2 Q2.hinj146_11_2
      Q2.hcardT146_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_11_2 i) (Q2.hfix146_11_2 i) _)
      colCert_146_11_3.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_11_4 (hp : 4 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 4 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp)) T146_11
      hfix146_11 hinj146_11 hcardT146_11
      (fun i => conj_mem_of_fixedPoints _ _ (T146_11 i) (hfix146_11 i) _)
      ⟨146, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 4 hp) Q2.T146_11_2 Q2.hfix146_11_2 Q2.hinj146_11_2
      Q2.hcardT146_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_11_2 i) (Q2.hfix146_11_2 i) _)
      colCert_146_11_4.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T146_12
      hfix146_12 hinj146_12 hcardT146_12
      (fun i => conj_mem_of_fixedPoints _ _ (T146_12 i) (hfix146_12 i) _)
      ⟨146, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T146_12_2 Q2.hfix146_12_2 Q2.hinj146_12_2
      Q2.hcardT146_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_12_2 i) (Q2.hfix146_12_2 i) _)
      colCert_146_12_0.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T146_12
      hfix146_12 hinj146_12 hcardT146_12
      (fun i => conj_mem_of_fixedPoints _ _ (T146_12 i) (hfix146_12 i) _)
      ⟨146, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T146_12_2 Q2.hfix146_12_2 Q2.hinj146_12_2
      Q2.hcardT146_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_12_2 i) (Q2.hfix146_12_2 i) _)
      colCert_146_12_1.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T146_12
      hfix146_12 hinj146_12 hcardT146_12
      (fun i => conj_mem_of_fixedPoints _ _ (T146_12 i) (hfix146_12 i) _)
      ⟨146, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T146_12_2 Q2.hfix146_12_2 Q2.hinj146_12_2
      Q2.hcardT146_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_12_2 i) (Q2.hfix146_12_2 i) _)
      colCert_146_12_2.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T146_12
      hfix146_12 hinj146_12 hcardT146_12
      (fun i => conj_mem_of_fixedPoints _ _ (T146_12 i) (hfix146_12 i) _)
      ⟨146, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T146_12_2 Q2.hfix146_12_2 Q2.hinj146_12_2
      Q2.hcardT146_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_12_2 i) (Q2.hfix146_12_2 i) _)
      colCert_146_12_3.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T146_12
      hfix146_12 hinj146_12 hcardT146_12
      (fun i => conj_mem_of_fixedPoints _ _ (T146_12 i) (hfix146_12 i) _)
      ⟨146, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T146_12_2 Q2.hfix146_12_2 Q2.hinj146_12_2
      Q2.hcardT146_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_12_2 i) (Q2.hfix146_12_2 i) _)
      colCert_146_12_4.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_48_0 (hp : 0 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 0 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp)) T146_48
      hfix146_48 hinj146_48 hcardT146_48
      (fun i => conj_mem_of_fixedPoints _ _ (T146_48 i) (hfix146_48 i) _)
      ⟨146, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 0 hp) Q2.T146_48_2 Q2.hfix146_48_2 Q2.hinj146_48_2
      Q2.hcardT146_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_48_2 i) (Q2.hfix146_48_2 i) _)
      colCert_146_48_0.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_48_1 (hp : 1 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 1 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp)) T146_48
      hfix146_48 hinj146_48 hcardT146_48
      (fun i => conj_mem_of_fixedPoints _ _ (T146_48 i) (hfix146_48 i) _)
      ⟨146, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 1 hp) Q2.T146_48_2 Q2.hfix146_48_2 Q2.hinj146_48_2
      Q2.hcardT146_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_48_2 i) (Q2.hfix146_48_2 i) _)
      colCert_146_48_1.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_48_2 (hp : 2 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 2 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp)) T146_48
      hfix146_48 hinj146_48 hcardT146_48
      (fun i => conj_mem_of_fixedPoints _ _ (T146_48 i) (hfix146_48 i) _)
      ⟨146, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 2 hp) Q2.T146_48_2 Q2.hfix146_48_2 Q2.hinj146_48_2
      Q2.hcardT146_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_48_2 i) (Q2.hfix146_48_2 i) _)
      colCert_146_48_2.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_48_3 (hp : 3 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 3 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp)) T146_48
      hfix146_48 hinj146_48 hcardT146_48
      (fun i => conj_mem_of_fixedPoints _ _ (T146_48 i) (hfix146_48 i) _)
      ⟨146, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 3 hp) Q2.T146_48_2 Q2.hfix146_48_2 Q2.hinj146_48_2
      Q2.hcardT146_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_48_2 i) (Q2.hfix146_48_2 i) _)
      colCert_146_48_3.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_48_4 (hp : 4 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 4 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp)) T146_48
      hfix146_48 hinj146_48 hcardT146_48
      (fun i => conj_mem_of_fixedPoints _ _ (T146_48 i) (hfix146_48 i) _)
      ⟨146, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 4 hp) Q2.T146_48_2 Q2.hfix146_48_2 Q2.hinj146_48_2
      Q2.hcardT146_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_48_2 i) (Q2.hfix146_48_2 i) _)
      colCert_146_48_4.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_48_5 (hp : 5 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 5 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨146, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp)) T146_48
      hfix146_48 hinj146_48 hcardT146_48
      (fun i => conj_mem_of_fixedPoints _ _ (T146_48 i) (hfix146_48 i) _)
      ⟨146, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 5 hp) Q2.T146_48_2 Q2.hfix146_48_2 Q2.hinj146_48_2
      Q2.hcardT146_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_48_2 i) (Q2.hfix146_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨146, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T146_48 = colFn colCertDiv_146_48_5.D1 (m := 5) from colCertDiv_146_48_5.bind1,
    show colData2 (⟨146, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 5 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T146_48_2 = colFn colCertDiv_146_48_5.D2 (m := 5) from colCertDiv_146_48_5.bind2]
  rw [alnId_146 j hj]
  exact fastcode_of_div ⟨146, by decide⟩ _ _ _
    ((alnId_146 j hj) ▸ Q2.listedAt (⟨146, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨146, by decide⟩ : Fin 148) hj hq).1) colCertDiv_146_48_5_match


theorem leaf_146_48_10 (hp : 10 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 10 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨146, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp)) T146_48
      hfix146_48 hinj146_48 hcardT146_48
      (fun i => conj_mem_of_fixedPoints _ _ (T146_48 i) (hfix146_48 i) _)
      ⟨146, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 10 hp) Q2.T146_48_2 Q2.hfix146_48_2 Q2.hinj146_48_2
      Q2.hcardT146_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_48_2 i) (Q2.hfix146_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨146, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T146_48 = colFn colCertDiv_146_48_10.D1 (m := 5) from colCertDiv_146_48_10.bind1,
    show colData2 (⟨146, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 10 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T146_48_2 = colFn colCertDiv_146_48_10.D2 (m := 5) from colCertDiv_146_48_10.bind2]
  rw [alnId_146 j hj]
  exact fastcode_of_div ⟨146, by decide⟩ _ _ _
    ((alnId_146 j hj) ▸ Q2.listedAt (⟨146, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨146, by decide⟩ : Fin 148) hj hq).1) colCertDiv_146_48_10_match


theorem leaf_146_48_15 (hp : 15 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 15 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨146, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp)) T146_48
      hfix146_48 hinj146_48 hcardT146_48
      (fun i => conj_mem_of_fixedPoints _ _ (T146_48 i) (hfix146_48 i) _)
      ⟨146, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 15 hp) Q2.T146_48_2 Q2.hfix146_48_2 Q2.hinj146_48_2
      Q2.hcardT146_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_48_2 i) (Q2.hfix146_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨146, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T146_48 = colFn colCertDiv_146_48_15.D1 (m := 5) from colCertDiv_146_48_15.bind1,
    show colData2 (⟨146, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 15 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T146_48_2 = colFn colCertDiv_146_48_15.D2 (m := 5) from colCertDiv_146_48_15.bind2]
  rw [alnId_146 j hj]
  exact fastcode_of_div ⟨146, by decide⟩ _ _ _
    ((alnId_146 j hj) ▸ Q2.listedAt (⟨146, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨146, by decide⟩ : Fin 148) hj hq).1) colCertDiv_146_48_15_match


theorem leaf_146_48_20 (hp : 20 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 20 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨146, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp)) T146_48
      hfix146_48 hinj146_48 hcardT146_48
      (fun i => conj_mem_of_fixedPoints _ _ (T146_48 i) (hfix146_48 i) _)
      ⟨146, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 20 hp) Q2.T146_48_2 Q2.hfix146_48_2 Q2.hinj146_48_2
      Q2.hcardT146_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_48_2 i) (Q2.hfix146_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨146, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T146_48 = colFn colCertDiv_146_48_20.D1 (m := 5) from colCertDiv_146_48_20.bind1,
    show colData2 (⟨146, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 20 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T146_48_2 = colFn colCertDiv_146_48_20.D2 (m := 5) from colCertDiv_146_48_20.bind2]
  rw [alnId_146 j hj]
  exact fastcode_of_div ⟨146, by decide⟩ _ _ _
    ((alnId_146 j hj) ▸ Q2.listedAt (⟨146, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨146, by decide⟩ : Fin 148) hj hq).1) colCertDiv_146_48_20_match


theorem leaf_146_49_0 (hp : 0 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 0 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp)) T146_49
      hfix146_49 hinj146_49 hcardT146_49
      (fun i => conj_mem_of_fixedPoints _ _ (T146_49 i) (hfix146_49 i) _)
      ⟨146, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 0 hp) Q2.T146_49_2 Q2.hfix146_49_2 Q2.hinj146_49_2
      Q2.hcardT146_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_49_2 i) (Q2.hfix146_49_2 i) _)
      colCert_146_49_0.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_49_1 (hp : 1 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 1 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp)) T146_49
      hfix146_49 hinj146_49 hcardT146_49
      (fun i => conj_mem_of_fixedPoints _ _ (T146_49 i) (hfix146_49 i) _)
      ⟨146, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 1 hp) Q2.T146_49_2 Q2.hfix146_49_2 Q2.hinj146_49_2
      Q2.hcardT146_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_49_2 i) (Q2.hfix146_49_2 i) _)
      colCert_146_49_1.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_49_2 (hp : 2 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 2 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp)) T146_49
      hfix146_49 hinj146_49 hcardT146_49
      (fun i => conj_mem_of_fixedPoints _ _ (T146_49 i) (hfix146_49 i) _)
      ⟨146, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 2 hp) Q2.T146_49_2 Q2.hfix146_49_2 Q2.hinj146_49_2
      Q2.hcardT146_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_49_2 i) (Q2.hfix146_49_2 i) _)
      colCert_146_49_2.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_49_3 (hp : 3 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 3 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp)) T146_49
      hfix146_49 hinj146_49 hcardT146_49
      (fun i => conj_mem_of_fixedPoints _ _ (T146_49 i) (hfix146_49 i) _)
      ⟨146, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 3 hp) Q2.T146_49_2 Q2.hfix146_49_2 Q2.hinj146_49_2
      Q2.hcardT146_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_49_2 i) (Q2.hfix146_49_2 i) _)
      colCert_146_49_3.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_49_4 (hp : 4 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 4 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp)) T146_49
      hfix146_49 hinj146_49 hcardT146_49
      (fun i => conj_mem_of_fixedPoints _ _ (T146_49 i) (hfix146_49 i) _)
      ⟨146, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 4 hp) Q2.T146_49_2 Q2.hfix146_49_2 Q2.hinj146_49_2
      Q2.hcardT146_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_49_2 i) (Q2.hfix146_49_2 i) _)
      colCert_146_49_4.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_49_5 (hp : 5 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 5 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp)) T146_49
      hfix146_49 hinj146_49 hcardT146_49
      (fun i => conj_mem_of_fixedPoints _ _ (T146_49 i) (hfix146_49 i) _)
      ⟨146, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 5 hp) Q2.T146_49_2 Q2.hfix146_49_2 Q2.hinj146_49_2
      Q2.hcardT146_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_49_2 i) (Q2.hfix146_49_2 i) _)
      colCert_146_49_5.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_49_10 (hp : 10 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 10 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨146, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp)) T146_49
      hfix146_49 hinj146_49 hcardT146_49
      (fun i => conj_mem_of_fixedPoints _ _ (T146_49 i) (hfix146_49 i) _)
      ⟨146, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 10 hp) Q2.T146_49_2 Q2.hfix146_49_2 Q2.hinj146_49_2
      Q2.hcardT146_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_49_2 i) (Q2.hfix146_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨146, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T146_49 = colFn colCertDiv_146_49_10.D1 (m := 5) from colCertDiv_146_49_10.bind1,
    show colData2 (⟨146, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 10 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T146_49_2 = colFn colCertDiv_146_49_10.D2 (m := 5) from colCertDiv_146_49_10.bind2]
  rw [alnId_146 j hj]
  exact fastcode_of_div ⟨146, by decide⟩ _ _ _
    ((alnId_146 j hj) ▸ Q2.listedAt (⟨146, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨146, by decide⟩ : Fin 148) hj hq).1) colCertDiv_146_49_10_match


theorem leaf_146_49_15 (hp : 15 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 15 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨146, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp)) T146_49
      hfix146_49 hinj146_49 hcardT146_49
      (fun i => conj_mem_of_fixedPoints _ _ (T146_49 i) (hfix146_49 i) _)
      ⟨146, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 15 hp) Q2.T146_49_2 Q2.hfix146_49_2 Q2.hinj146_49_2
      Q2.hcardT146_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_49_2 i) (Q2.hfix146_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨146, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T146_49 = colFn colCertDiv_146_49_15.D1 (m := 5) from colCertDiv_146_49_15.bind1,
    show colData2 (⟨146, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 15 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T146_49_2 = colFn colCertDiv_146_49_15.D2 (m := 5) from colCertDiv_146_49_15.bind2]
  rw [alnId_146 j hj]
  exact fastcode_of_div ⟨146, by decide⟩ _ _ _
    ((alnId_146 j hj) ▸ Q2.listedAt (⟨146, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨146, by decide⟩ : Fin 148) hj hq).1) colCertDiv_146_49_15_match


theorem leaf_146_49_20 (hp : 20 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 20 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨146, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp)) T146_49
      hfix146_49 hinj146_49 hcardT146_49
      (fun i => conj_mem_of_fixedPoints _ _ (T146_49 i) (hfix146_49 i) _)
      ⟨146, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 20 hp) Q2.T146_49_2 Q2.hfix146_49_2 Q2.hinj146_49_2
      Q2.hcardT146_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_49_2 i) (Q2.hfix146_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨146, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T146_49 = colFn colCertDiv_146_49_20.D1 (m := 5) from colCertDiv_146_49_20.bind1,
    show colData2 (⟨146, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 20 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T146_49_2 = colFn colCertDiv_146_49_20.D2 (m := 5) from colCertDiv_146_49_20.bind2]
  rw [alnId_146 j hj]
  exact fastcode_of_div ⟨146, by decide⟩ _ _ _
    ((alnId_146 j hj) ▸ Q2.listedAt (⟨146, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨146, by decide⟩ : Fin 148) hj hq).1) colCertDiv_146_49_20_match


theorem leaf_146_50_0 (hp : 0 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 0 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp)) T146_50
      hfix146_50 hinj146_50 hcardT146_50
      (fun i => conj_mem_of_fixedPoints _ _ (T146_50 i) (hfix146_50 i) _)
      ⟨146, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 0 hp) Q2.T146_50_2 Q2.hfix146_50_2 Q2.hinj146_50_2
      Q2.hcardT146_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_50_2 i) (Q2.hfix146_50_2 i) _)
      colCert_146_50_0.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_50_1 (hp : 1 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 1 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp)) T146_50
      hfix146_50 hinj146_50 hcardT146_50
      (fun i => conj_mem_of_fixedPoints _ _ (T146_50 i) (hfix146_50 i) _)
      ⟨146, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 1 hp) Q2.T146_50_2 Q2.hfix146_50_2 Q2.hinj146_50_2
      Q2.hcardT146_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_50_2 i) (Q2.hfix146_50_2 i) _)
      colCert_146_50_1.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_50_2 (hp : 2 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 2 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp)) T146_50
      hfix146_50 hinj146_50 hcardT146_50
      (fun i => conj_mem_of_fixedPoints _ _ (T146_50 i) (hfix146_50 i) _)
      ⟨146, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 2 hp) Q2.T146_50_2 Q2.hfix146_50_2 Q2.hinj146_50_2
      Q2.hcardT146_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_50_2 i) (Q2.hfix146_50_2 i) _)
      colCert_146_50_2.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_50_3 (hp : 3 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 3 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp)) T146_50
      hfix146_50 hinj146_50 hcardT146_50
      (fun i => conj_mem_of_fixedPoints _ _ (T146_50 i) (hfix146_50 i) _)
      ⟨146, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 3 hp) Q2.T146_50_2 Q2.hfix146_50_2 Q2.hinj146_50_2
      Q2.hcardT146_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_50_2 i) (Q2.hfix146_50_2 i) _)
      colCert_146_50_3.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_50_4 (hp : 4 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 4 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp)) T146_50
      hfix146_50 hinj146_50 hcardT146_50
      (fun i => conj_mem_of_fixedPoints _ _ (T146_50 i) (hfix146_50 i) _)
      ⟨146, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 4 hp) Q2.T146_50_2 Q2.hfix146_50_2 Q2.hinj146_50_2
      Q2.hcardT146_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_50_2 i) (Q2.hfix146_50_2 i) _)
      colCert_146_50_4.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_50_5 (hp : 5 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 5 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨146, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp)) T146_50
      hfix146_50 hinj146_50 hcardT146_50
      (fun i => conj_mem_of_fixedPoints _ _ (T146_50 i) (hfix146_50 i) _)
      ⟨146, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 5 hp) Q2.T146_50_2 Q2.hfix146_50_2 Q2.hinj146_50_2
      Q2.hcardT146_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_50_2 i) (Q2.hfix146_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨146, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T146_50 = colFn colCertDiv_146_50_5.D1 (m := 5) from colCertDiv_146_50_5.bind1,
    show colData2 (⟨146, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 5 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T146_50_2 = colFn colCertDiv_146_50_5.D2 (m := 5) from colCertDiv_146_50_5.bind2]
  rw [alnId_146 j hj]
  exact fastcode_of_div ⟨146, by decide⟩ _ _ _
    ((alnId_146 j hj) ▸ Q2.listedAt (⟨146, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨146, by decide⟩ : Fin 148) hj hq).1) colCertDiv_146_50_5_match


theorem leaf_146_50_10 (hp : 10 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 10 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨146, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp)) T146_50
      hfix146_50 hinj146_50 hcardT146_50
      (fun i => conj_mem_of_fixedPoints _ _ (T146_50 i) (hfix146_50 i) _)
      ⟨146, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 10 hp) Q2.T146_50_2 Q2.hfix146_50_2 Q2.hinj146_50_2
      Q2.hcardT146_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_50_2 i) (Q2.hfix146_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨146, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T146_50 = colFn colCertDiv_146_50_10.D1 (m := 5) from colCertDiv_146_50_10.bind1,
    show colData2 (⟨146, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 10 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T146_50_2 = colFn colCertDiv_146_50_10.D2 (m := 5) from colCertDiv_146_50_10.bind2]
  rw [alnId_146 j hj]
  exact fastcode_of_div ⟨146, by decide⟩ _ _ _
    ((alnId_146 j hj) ▸ Q2.listedAt (⟨146, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨146, by decide⟩ : Fin 148) hj hq).1) colCertDiv_146_50_10_match


theorem leaf_146_50_15 (hp : 15 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 15 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨146, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp)) T146_50
      hfix146_50 hinj146_50 hcardT146_50
      (fun i => conj_mem_of_fixedPoints _ _ (T146_50 i) (hfix146_50 i) _)
      ⟨146, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 15 hp) Q2.T146_50_2 Q2.hfix146_50_2 Q2.hinj146_50_2
      Q2.hcardT146_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_50_2 i) (Q2.hfix146_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨146, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T146_50 = colFn colCertDiv_146_50_15.D1 (m := 5) from colCertDiv_146_50_15.bind1,
    show colData2 (⟨146, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 15 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T146_50_2 = colFn colCertDiv_146_50_15.D2 (m := 5) from colCertDiv_146_50_15.bind2]
  rw [alnId_146 j hj]
  exact fastcode_of_div ⟨146, by decide⟩ _ _ _
    ((alnId_146 j hj) ▸ Q2.listedAt (⟨146, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨146, by decide⟩ : Fin 148) hj hq).1) colCertDiv_146_50_15_match


theorem leaf_146_50_20 (hp : 20 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 20 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨146, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp)) T146_50
      hfix146_50 hinj146_50 hcardT146_50
      (fun i => conj_mem_of_fixedPoints _ _ (T146_50 i) (hfix146_50 i) _)
      ⟨146, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 20 hp) Q2.T146_50_2 Q2.hfix146_50_2 Q2.hinj146_50_2
      Q2.hcardT146_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_50_2 i) (Q2.hfix146_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨146, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T146_50 = colFn colCertDiv_146_50_20.D1 (m := 5) from colCertDiv_146_50_20.bind1,
    show colData2 (⟨146, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 20 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T146_50_2 = colFn colCertDiv_146_50_20.D2 (m := 5) from colCertDiv_146_50_20.bind2]
  rw [alnId_146 j hj]
  exact fastcode_of_div ⟨146, by decide⟩ _ _ _
    ((alnId_146 j hj) ▸ Q2.listedAt (⟨146, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨146, by decide⟩ : Fin 148) hj hq).1) colCertDiv_146_50_20_match


theorem leaf_146_51_0 (hp : 0 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 0 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp)) T146_51
      hfix146_51 hinj146_51 hcardT146_51
      (fun i => conj_mem_of_fixedPoints _ _ (T146_51 i) (hfix146_51 i) _)
      ⟨146, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 0 hp) Q2.T146_51_2 Q2.hfix146_51_2 Q2.hinj146_51_2
      Q2.hcardT146_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_51_2 i) (Q2.hfix146_51_2 i) _)
      colCert_146_51_0.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_51_1 (hp : 1 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 1 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp)) T146_51
      hfix146_51 hinj146_51 hcardT146_51
      (fun i => conj_mem_of_fixedPoints _ _ (T146_51 i) (hfix146_51 i) _)
      ⟨146, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 1 hp) Q2.T146_51_2 Q2.hfix146_51_2 Q2.hinj146_51_2
      Q2.hcardT146_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_51_2 i) (Q2.hfix146_51_2 i) _)
      colCert_146_51_1.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_51_2 (hp : 2 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 2 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp)) T146_51
      hfix146_51 hinj146_51 hcardT146_51
      (fun i => conj_mem_of_fixedPoints _ _ (T146_51 i) (hfix146_51 i) _)
      ⟨146, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 2 hp) Q2.T146_51_2 Q2.hfix146_51_2 Q2.hinj146_51_2
      Q2.hcardT146_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_51_2 i) (Q2.hfix146_51_2 i) _)
      colCert_146_51_2.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_51_3 (hp : 3 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 3 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp)) T146_51
      hfix146_51 hinj146_51 hcardT146_51
      (fun i => conj_mem_of_fixedPoints _ _ (T146_51 i) (hfix146_51 i) _)
      ⟨146, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 3 hp) Q2.T146_51_2 Q2.hfix146_51_2 Q2.hinj146_51_2
      Q2.hcardT146_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_51_2 i) (Q2.hfix146_51_2 i) _)
      colCert_146_51_3.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_51_4 (hp : 4 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 4 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp)) T146_51
      hfix146_51 hinj146_51 hcardT146_51
      (fun i => conj_mem_of_fixedPoints _ _ (T146_51 i) (hfix146_51 i) _)
      ⟨146, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 4 hp) Q2.T146_51_2 Q2.hfix146_51_2 Q2.hinj146_51_2
      Q2.hcardT146_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_51_2 i) (Q2.hfix146_51_2 i) _)
      colCert_146_51_4.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_51_5 (hp : 5 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 5 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨146, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp)) T146_51
      hfix146_51 hinj146_51 hcardT146_51
      (fun i => conj_mem_of_fixedPoints _ _ (T146_51 i) (hfix146_51 i) _)
      ⟨146, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 5 hp) Q2.T146_51_2 Q2.hfix146_51_2 Q2.hinj146_51_2
      Q2.hcardT146_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_51_2 i) (Q2.hfix146_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨146, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T146_51 = colFn colCertDiv_146_51_5.D1 (m := 5) from colCertDiv_146_51_5.bind1,
    show colData2 (⟨146, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 5 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T146_51_2 = colFn colCertDiv_146_51_5.D2 (m := 5) from colCertDiv_146_51_5.bind2]
  rw [alnId_146 j hj]
  exact fastcode_of_div ⟨146, by decide⟩ _ _ _
    ((alnId_146 j hj) ▸ Q2.listedAt (⟨146, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨146, by decide⟩ : Fin 148) hj hq).1) colCertDiv_146_51_5_match


theorem leaf_146_51_10 (hp : 10 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 10 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨146, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp)) T146_51
      hfix146_51 hinj146_51 hcardT146_51
      (fun i => conj_mem_of_fixedPoints _ _ (T146_51 i) (hfix146_51 i) _)
      ⟨146, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 10 hp) Q2.T146_51_2 Q2.hfix146_51_2 Q2.hinj146_51_2
      Q2.hcardT146_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_51_2 i) (Q2.hfix146_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨146, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T146_51 = colFn colCertDiv_146_51_10.D1 (m := 5) from colCertDiv_146_51_10.bind1,
    show colData2 (⟨146, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 10 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T146_51_2 = colFn colCertDiv_146_51_10.D2 (m := 5) from colCertDiv_146_51_10.bind2]
  rw [alnId_146 j hj]
  exact fastcode_of_div ⟨146, by decide⟩ _ _ _
    ((alnId_146 j hj) ▸ Q2.listedAt (⟨146, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨146, by decide⟩ : Fin 148) hj hq).1) colCertDiv_146_51_10_match


theorem leaf_146_51_15 (hp : 15 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 15 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨146, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp)) T146_51
      hfix146_51 hinj146_51 hcardT146_51
      (fun i => conj_mem_of_fixedPoints _ _ (T146_51 i) (hfix146_51 i) _)
      ⟨146, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 15 hp) Q2.T146_51_2 Q2.hfix146_51_2 Q2.hinj146_51_2
      Q2.hcardT146_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_51_2 i) (Q2.hfix146_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨146, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T146_51 = colFn colCertDiv_146_51_15.D1 (m := 5) from colCertDiv_146_51_15.bind1,
    show colData2 (⟨146, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 15 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T146_51_2 = colFn colCertDiv_146_51_15.D2 (m := 5) from colCertDiv_146_51_15.bind2]
  rw [alnId_146 j hj]
  exact fastcode_of_div ⟨146, by decide⟩ _ _ _
    ((alnId_146 j hj) ▸ Q2.listedAt (⟨146, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨146, by decide⟩ : Fin 148) hj hq).1) colCertDiv_146_51_15_match


theorem leaf_146_51_20 (hp : 20 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 20 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨146, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp)) T146_51
      hfix146_51 hinj146_51 hcardT146_51
      (fun i => conj_mem_of_fixedPoints _ _ (T146_51 i) (hfix146_51 i) _)
      ⟨146, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 20 hp) Q2.T146_51_2 Q2.hfix146_51_2 Q2.hinj146_51_2
      Q2.hcardT146_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_51_2 i) (Q2.hfix146_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨146, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T146_51 = colFn colCertDiv_146_51_20.D1 (m := 5) from colCertDiv_146_51_20.bind1,
    show colData2 (⟨146, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 20 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T146_51_2 = colFn colCertDiv_146_51_20.D2 (m := 5) from colCertDiv_146_51_20.bind2]
  rw [alnId_146 j hj]
  exact fastcode_of_div ⟨146, by decide⟩ _ _ _
    ((alnId_146 j hj) ▸ Q2.listedAt (⟨146, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨146, by decide⟩ : Fin 148) hj hq).1) colCertDiv_146_51_20_match


theorem leaf_146_52_0 (hp : 0 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 0 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp)) T146_52
      hfix146_52 hinj146_52 hcardT146_52
      (fun i => conj_mem_of_fixedPoints _ _ (T146_52 i) (hfix146_52 i) _)
      ⟨146, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 0 hp) Q2.T146_52_2 Q2.hfix146_52_2 Q2.hinj146_52_2
      Q2.hcardT146_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_52_2 i) (Q2.hfix146_52_2 i) _)
      colCert_146_52_0.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_52_1 (hp : 1 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 1 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp)) T146_52
      hfix146_52 hinj146_52 hcardT146_52
      (fun i => conj_mem_of_fixedPoints _ _ (T146_52 i) (hfix146_52 i) _)
      ⟨146, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 1 hp) Q2.T146_52_2 Q2.hfix146_52_2 Q2.hinj146_52_2
      Q2.hcardT146_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_52_2 i) (Q2.hfix146_52_2 i) _)
      colCert_146_52_1.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_52_2 (hp : 2 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 2 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp)) T146_52
      hfix146_52 hinj146_52 hcardT146_52
      (fun i => conj_mem_of_fixedPoints _ _ (T146_52 i) (hfix146_52 i) _)
      ⟨146, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 2 hp) Q2.T146_52_2 Q2.hfix146_52_2 Q2.hinj146_52_2
      Q2.hcardT146_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_52_2 i) (Q2.hfix146_52_2 i) _)
      colCert_146_52_2.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_52_3 (hp : 3 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 3 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp)) T146_52
      hfix146_52 hinj146_52 hcardT146_52
      (fun i => conj_mem_of_fixedPoints _ _ (T146_52 i) (hfix146_52 i) _)
      ⟨146, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 3 hp) Q2.T146_52_2 Q2.hfix146_52_2 Q2.hinj146_52_2
      Q2.hcardT146_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_52_2 i) (Q2.hfix146_52_2 i) _)
      colCert_146_52_3.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_52_4 (hp : 4 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 4 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp)) T146_52
      hfix146_52 hinj146_52 hcardT146_52
      (fun i => conj_mem_of_fixedPoints _ _ (T146_52 i) (hfix146_52 i) _)
      ⟨146, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 4 hp) Q2.T146_52_2 Q2.hfix146_52_2 Q2.hinj146_52_2
      Q2.hcardT146_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_52_2 i) (Q2.hfix146_52_2 i) _)
      colCert_146_52_4.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_52_5 (hp : 5 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 5 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨146, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp)) T146_52
      hfix146_52 hinj146_52 hcardT146_52
      (fun i => conj_mem_of_fixedPoints _ _ (T146_52 i) (hfix146_52 i) _)
      ⟨146, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 5 hp) Q2.T146_52_2 Q2.hfix146_52_2 Q2.hinj146_52_2
      Q2.hcardT146_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_52_2 i) (Q2.hfix146_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨146, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T146_52 = colFn colCertDiv_146_52_5.D1 (m := 5) from colCertDiv_146_52_5.bind1,
    show colData2 (⟨146, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 5 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T146_52_2 = colFn colCertDiv_146_52_5.D2 (m := 5) from colCertDiv_146_52_5.bind2]
  rw [alnId_146 j hj]
  exact fastcode_of_div ⟨146, by decide⟩ _ _ _
    ((alnId_146 j hj) ▸ Q2.listedAt (⟨146, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨146, by decide⟩ : Fin 148) hj hq).1) colCertDiv_146_52_5_match


theorem leaf_146_52_10 (hp : 10 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 10 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨146, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp)) T146_52
      hfix146_52 hinj146_52 hcardT146_52
      (fun i => conj_mem_of_fixedPoints _ _ (T146_52 i) (hfix146_52 i) _)
      ⟨146, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 10 hp) Q2.T146_52_2 Q2.hfix146_52_2 Q2.hinj146_52_2
      Q2.hcardT146_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_52_2 i) (Q2.hfix146_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨146, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T146_52 = colFn colCertDiv_146_52_10.D1 (m := 5) from colCertDiv_146_52_10.bind1,
    show colData2 (⟨146, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 10 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T146_52_2 = colFn colCertDiv_146_52_10.D2 (m := 5) from colCertDiv_146_52_10.bind2]
  rw [alnId_146 j hj]
  exact fastcode_of_div ⟨146, by decide⟩ _ _ _
    ((alnId_146 j hj) ▸ Q2.listedAt (⟨146, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨146, by decide⟩ : Fin 148) hj hq).1) colCertDiv_146_52_10_match


theorem leaf_146_52_15 (hp : 15 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 15 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨146, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp)) T146_52
      hfix146_52 hinj146_52 hcardT146_52
      (fun i => conj_mem_of_fixedPoints _ _ (T146_52 i) (hfix146_52 i) _)
      ⟨146, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 15 hp) Q2.T146_52_2 Q2.hfix146_52_2 Q2.hinj146_52_2
      Q2.hcardT146_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_52_2 i) (Q2.hfix146_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨146, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T146_52 = colFn colCertDiv_146_52_15.D1 (m := 5) from colCertDiv_146_52_15.bind1,
    show colData2 (⟨146, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 15 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T146_52_2 = colFn colCertDiv_146_52_15.D2 (m := 5) from colCertDiv_146_52_15.bind2]
  rw [alnId_146 j hj]
  exact fastcode_of_div ⟨146, by decide⟩ _ _ _
    ((alnId_146 j hj) ▸ Q2.listedAt (⟨146, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨146, by decide⟩ : Fin 148) hj hq).1) colCertDiv_146_52_15_match


theorem leaf_146_52_20 (hp : 20 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 20 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨146, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp)) T146_52
      hfix146_52 hinj146_52 hcardT146_52
      (fun i => conj_mem_of_fixedPoints _ _ (T146_52 i) (hfix146_52 i) _)
      ⟨146, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 20 hp) Q2.T146_52_2 Q2.hfix146_52_2 Q2.hinj146_52_2
      Q2.hcardT146_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_52_2 i) (Q2.hfix146_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨146, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T146_52 = colFn colCertDiv_146_52_20.D1 (m := 5) from colCertDiv_146_52_20.bind1,
    show colData2 (⟨146, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 20 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T146_52_2 = colFn colCertDiv_146_52_20.D2 (m := 5) from colCertDiv_146_52_20.bind2]
  rw [alnId_146 j hj]
  exact fastcode_of_div ⟨146, by decide⟩ _ _ _
    ((alnId_146 j hj) ▸ Q2.listedAt (⟨146, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨146, by decide⟩ : Fin 148) hj hq).1) colCertDiv_146_52_20_match


theorem leaf_146_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T146_53
      hfix146_53 hinj146_53 hcardT146_53
      (fun i => conj_mem_of_fixedPoints _ _ (T146_53 i) (hfix146_53 i) _)
      ⟨146, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T146_53_2 Q2.hfix146_53_2 Q2.hinj146_53_2
      Q2.hcardT146_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_53_2 i) (Q2.hfix146_53_2 i) _)
      colCert_146_53_0.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T146_53
      hfix146_53 hinj146_53 hcardT146_53
      (fun i => conj_mem_of_fixedPoints _ _ (T146_53 i) (hfix146_53 i) _)
      ⟨146, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T146_53_2 Q2.hfix146_53_2 Q2.hinj146_53_2
      Q2.hcardT146_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_53_2 i) (Q2.hfix146_53_2 i) _)
      colCert_146_53_1.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T146_53
      hfix146_53 hinj146_53 hcardT146_53
      (fun i => conj_mem_of_fixedPoints _ _ (T146_53 i) (hfix146_53 i) _)
      ⟨146, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T146_53_2 Q2.hfix146_53_2 Q2.hinj146_53_2
      Q2.hcardT146_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_53_2 i) (Q2.hfix146_53_2 i) _)
      colCert_146_53_2.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T146_53
      hfix146_53 hinj146_53 hcardT146_53
      (fun i => conj_mem_of_fixedPoints _ _ (T146_53 i) (hfix146_53 i) _)
      ⟨146, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T146_53_2 Q2.hfix146_53_2 Q2.hinj146_53_2
      Q2.hcardT146_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_53_2 i) (Q2.hfix146_53_2 i) _)
      colCert_146_53_3.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T146_53
      hfix146_53 hinj146_53 hcardT146_53
      (fun i => conj_mem_of_fixedPoints _ _ (T146_53 i) (hfix146_53 i) _)
      ⟨146, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T146_53_2 Q2.hfix146_53_2 Q2.hinj146_53_2
      Q2.hcardT146_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_53_2 i) (Q2.hfix146_53_2 i) _)
      colCert_146_53_4.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T146_53
      hfix146_53 hinj146_53 hcardT146_53
      (fun i => conj_mem_of_fixedPoints _ _ (T146_53 i) (hfix146_53 i) _)
      ⟨146, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T146_53_2 Q2.hfix146_53_2 Q2.hinj146_53_2
      Q2.hcardT146_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_53_2 i) (Q2.hfix146_53_2 i) _)
      colCert_146_53_5.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T146_53
      hfix146_53 hinj146_53 hcardT146_53
      (fun i => conj_mem_of_fixedPoints _ _ (T146_53 i) (hfix146_53 i) _)
      ⟨146, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T146_53_2 Q2.hfix146_53_2 Q2.hinj146_53_2
      Q2.hcardT146_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_53_2 i) (Q2.hfix146_53_2 i) _)
      colCert_146_53_10.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T146_53
      hfix146_53 hinj146_53 hcardT146_53
      (fun i => conj_mem_of_fixedPoints _ _ (T146_53 i) (hfix146_53 i) _)
      ⟨146, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T146_53_2 Q2.hfix146_53_2 Q2.hinj146_53_2
      Q2.hcardT146_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_53_2 i) (Q2.hfix146_53_2 i) _)
      colCert_146_53_15.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T146_53
      hfix146_53 hinj146_53 hcardT146_53
      (fun i => conj_mem_of_fixedPoints _ _ (T146_53 i) (hfix146_53 i) _)
      ⟨146, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T146_53_2 Q2.hfix146_53_2 Q2.hinj146_53_2
      Q2.hcardT146_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_53_2 i) (Q2.hfix146_53_2 i) _)
      colCert_146_53_20.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_54_0 (hp : 0 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 0 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 0 (transLenTr ⟨54, by decide⟩ 0 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 0 (transLenTr ⟨54, by decide⟩ 0 hp)) T146_54
      hfix146_54 hinj146_54 hcardT146_54
      (fun i => conj_mem_of_fixedPoints _ _ (T146_54 i) (hfix146_54 i) _)
      ⟨146, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 0 hp) Q2.T146_54_2 Q2.hfix146_54_2 Q2.hinj146_54_2
      Q2.hcardT146_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_54_2 i) (Q2.hfix146_54_2 i) _)
      colCert_146_54_0.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_54_1 (hp : 1 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 1 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 1 (transLenTr ⟨54, by decide⟩ 1 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 1 (transLenTr ⟨54, by decide⟩ 1 hp)) T146_54
      hfix146_54 hinj146_54 hcardT146_54
      (fun i => conj_mem_of_fixedPoints _ _ (T146_54 i) (hfix146_54 i) _)
      ⟨146, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 1 hp) Q2.T146_54_2 Q2.hfix146_54_2 Q2.hinj146_54_2
      Q2.hcardT146_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_54_2 i) (Q2.hfix146_54_2 i) _)
      colCert_146_54_1.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_54_2 (hp : 2 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 2 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 2 (transLenTr ⟨54, by decide⟩ 2 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 2 (transLenTr ⟨54, by decide⟩ 2 hp)) T146_54
      hfix146_54 hinj146_54 hcardT146_54
      (fun i => conj_mem_of_fixedPoints _ _ (T146_54 i) (hfix146_54 i) _)
      ⟨146, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 2 hp) Q2.T146_54_2 Q2.hfix146_54_2 Q2.hinj146_54_2
      Q2.hcardT146_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_54_2 i) (Q2.hfix146_54_2 i) _)
      colCert_146_54_2.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_54_3 (hp : 3 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 3 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 3 (transLenTr ⟨54, by decide⟩ 3 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 3 (transLenTr ⟨54, by decide⟩ 3 hp)) T146_54
      hfix146_54 hinj146_54 hcardT146_54
      (fun i => conj_mem_of_fixedPoints _ _ (T146_54 i) (hfix146_54 i) _)
      ⟨146, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 3 hp) Q2.T146_54_2 Q2.hfix146_54_2 Q2.hinj146_54_2
      Q2.hcardT146_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_54_2 i) (Q2.hfix146_54_2 i) _)
      colCert_146_54_3.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_54_4 (hp : 4 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 4 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 4 (transLenTr ⟨54, by decide⟩ 4 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 4 (transLenTr ⟨54, by decide⟩ 4 hp)) T146_54
      hfix146_54 hinj146_54 hcardT146_54
      (fun i => conj_mem_of_fixedPoints _ _ (T146_54 i) (hfix146_54 i) _)
      ⟨146, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 4 hp) Q2.T146_54_2 Q2.hfix146_54_2 Q2.hinj146_54_2
      Q2.hcardT146_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_54_2 i) (Q2.hfix146_54_2 i) _)
      colCert_146_54_4.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_54_5 (hp : 5 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 5 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 5 (transLenTr ⟨54, by decide⟩ 5 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 5 (transLenTr ⟨54, by decide⟩ 5 hp)) T146_54
      hfix146_54 hinj146_54 hcardT146_54
      (fun i => conj_mem_of_fixedPoints _ _ (T146_54 i) (hfix146_54 i) _)
      ⟨146, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 5 hp) Q2.T146_54_2 Q2.hfix146_54_2 Q2.hinj146_54_2
      Q2.hcardT146_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_54_2 i) (Q2.hfix146_54_2 i) _)
      colCert_146_54_5.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_54_10 (hp : 10 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 10 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 10 (transLenTr ⟨54, by decide⟩ 10 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 10 (transLenTr ⟨54, by decide⟩ 10 hp)) T146_54
      hfix146_54 hinj146_54 hcardT146_54
      (fun i => conj_mem_of_fixedPoints _ _ (T146_54 i) (hfix146_54 i) _)
      ⟨146, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 10 hp) Q2.T146_54_2 Q2.hfix146_54_2 Q2.hinj146_54_2
      Q2.hcardT146_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_54_2 i) (Q2.hfix146_54_2 i) _)
      colCert_146_54_10.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_54_15 (hp : 15 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 15 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 15 (transLenTr ⟨54, by decide⟩ 15 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 15 (transLenTr ⟨54, by decide⟩ 15 hp)) T146_54
      hfix146_54 hinj146_54 hcardT146_54
      (fun i => conj_mem_of_fixedPoints _ _ (T146_54 i) (hfix146_54 i) _)
      ⟨146, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 15 hp) Q2.T146_54_2 Q2.hfix146_54_2 Q2.hinj146_54_2
      Q2.hcardT146_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_54_2 i) (Q2.hfix146_54_2 i) _)
      colCert_146_54_15.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_54_20 (hp : 20 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 20 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 20 (transLenTr ⟨54, by decide⟩ 20 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 20 (transLenTr ⟨54, by decide⟩ 20 hp)) T146_54
      hfix146_54 hinj146_54 hcardT146_54
      (fun i => conj_mem_of_fixedPoints _ _ (T146_54 i) (hfix146_54 i) _)
      ⟨146, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 20 hp) Q2.T146_54_2 Q2.hfix146_54_2 Q2.hinj146_54_2
      Q2.hcardT146_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_54_2 i) (Q2.hfix146_54_2 i) _)
      colCert_146_54_20.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_110_0 (hp : 0 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 0 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 0 (transLenTr ⟨110, by decide⟩ 0 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 0 (transLenTr ⟨110, by decide⟩ 0 hp)) T146_110
      hfix146_110 hinj146_110 hcardT146_110
      (fun i => conj_mem_of_fixedPoints _ _ (T146_110 i) (hfix146_110 i) _)
      ⟨146, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 0 hp) Q2.T146_110_2 Q2.hfix146_110_2 Q2.hinj146_110_2
      Q2.hcardT146_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_110_2 i) (Q2.hfix146_110_2 i) _)
      colCert_146_110_0.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_110_1 (hp : 1 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 1 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 1 (transLenTr ⟨110, by decide⟩ 1 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 1 (transLenTr ⟨110, by decide⟩ 1 hp)) T146_110
      hfix146_110 hinj146_110 hcardT146_110
      (fun i => conj_mem_of_fixedPoints _ _ (T146_110 i) (hfix146_110 i) _)
      ⟨146, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 1 hp) Q2.T146_110_2 Q2.hfix146_110_2 Q2.hinj146_110_2
      Q2.hcardT146_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_110_2 i) (Q2.hfix146_110_2 i) _)
      colCert_146_110_1.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_110_2 (hp : 2 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 2 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 2 (transLenTr ⟨110, by decide⟩ 2 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 2 (transLenTr ⟨110, by decide⟩ 2 hp)) T146_110
      hfix146_110 hinj146_110 hcardT146_110
      (fun i => conj_mem_of_fixedPoints _ _ (T146_110 i) (hfix146_110 i) _)
      ⟨146, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 2 hp) Q2.T146_110_2 Q2.hfix146_110_2 Q2.hinj146_110_2
      Q2.hcardT146_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_110_2 i) (Q2.hfix146_110_2 i) _)
      colCert_146_110_2.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_110_3 (hp : 3 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 3 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 3 (transLenTr ⟨110, by decide⟩ 3 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 3 (transLenTr ⟨110, by decide⟩ 3 hp)) T146_110
      hfix146_110 hinj146_110 hcardT146_110
      (fun i => conj_mem_of_fixedPoints _ _ (T146_110 i) (hfix146_110 i) _)
      ⟨146, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 3 hp) Q2.T146_110_2 Q2.hfix146_110_2 Q2.hinj146_110_2
      Q2.hcardT146_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_110_2 i) (Q2.hfix146_110_2 i) _)
      colCert_146_110_3.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_110_4 (hp : 4 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 4 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 4 (transLenTr ⟨110, by decide⟩ 4 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 4 (transLenTr ⟨110, by decide⟩ 4 hp)) T146_110
      hfix146_110 hinj146_110 hcardT146_110
      (fun i => conj_mem_of_fixedPoints _ _ (T146_110 i) (hfix146_110 i) _)
      ⟨146, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 4 hp) Q2.T146_110_2 Q2.hfix146_110_2 Q2.hinj146_110_2
      Q2.hcardT146_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_110_2 i) (Q2.hfix146_110_2 i) _)
      colCert_146_110_4.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_110_5 (hp : 5 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 5 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 5 (transLenTr ⟨110, by decide⟩ 5 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 5 (transLenTr ⟨110, by decide⟩ 5 hp)) T146_110
      hfix146_110 hinj146_110 hcardT146_110
      (fun i => conj_mem_of_fixedPoints _ _ (T146_110 i) (hfix146_110 i) _)
      ⟨146, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 5 hp) Q2.T146_110_2 Q2.hfix146_110_2 Q2.hinj146_110_2
      Q2.hcardT146_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_110_2 i) (Q2.hfix146_110_2 i) _)
      colCert_146_110_5.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_110_10 (hp : 10 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 10 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 10 (transLenTr ⟨110, by decide⟩ 10 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 10 (transLenTr ⟨110, by decide⟩ 10 hp)) T146_110
      hfix146_110 hinj146_110 hcardT146_110
      (fun i => conj_mem_of_fixedPoints _ _ (T146_110 i) (hfix146_110 i) _)
      ⟨146, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 10 hp) Q2.T146_110_2 Q2.hfix146_110_2 Q2.hinj146_110_2
      Q2.hcardT146_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_110_2 i) (Q2.hfix146_110_2 i) _)
      colCert_146_110_10.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_110_15 (hp : 15 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 15 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 15 (transLenTr ⟨110, by decide⟩ 15 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 15 (transLenTr ⟨110, by decide⟩ 15 hp)) T146_110
      hfix146_110 hinj146_110 hcardT146_110
      (fun i => conj_mem_of_fixedPoints _ _ (T146_110 i) (hfix146_110 i) _)
      ⟨146, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 15 hp) Q2.T146_110_2 Q2.hfix146_110_2 Q2.hinj146_110_2
      Q2.hcardT146_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_110_2 i) (Q2.hfix146_110_2 i) _)
      colCert_146_110_15.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_110_20 (hp : 20 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 20 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 20 (transLenTr ⟨110, by decide⟩ 20 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 20 (transLenTr ⟨110, by decide⟩ 20 hp)) T146_110
      hfix146_110 hinj146_110 hcardT146_110
      (fun i => conj_mem_of_fixedPoints _ _ (T146_110 i) (hfix146_110 i) _)
      ⟨146, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 20 hp) Q2.T146_110_2 Q2.hfix146_110_2 Q2.hinj146_110_2
      Q2.hcardT146_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_110_2 i) (Q2.hfix146_110_2 i) _)
      colCert_146_110_20.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_110_25 (hp : 25 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 25 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 25 (transLenTr ⟨110, by decide⟩ 25 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 25 (transLenTr ⟨110, by decide⟩ 25 hp)) T146_110
      hfix146_110 hinj146_110 hcardT146_110
      (fun i => conj_mem_of_fixedPoints _ _ (T146_110 i) (hfix146_110 i) _)
      ⟨146, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 25 hp) Q2.T146_110_2 Q2.hfix146_110_2 Q2.hinj146_110_2
      Q2.hcardT146_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_110_2 i) (Q2.hfix146_110_2 i) _)
      colCert_146_110_25.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_110_50 (hp : 50 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 50 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 50 (transLenTr ⟨110, by decide⟩ 50 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 50 (transLenTr ⟨110, by decide⟩ 50 hp)) T146_110
      hfix146_110 hinj146_110 hcardT146_110
      (fun i => conj_mem_of_fixedPoints _ _ (T146_110 i) (hfix146_110 i) _)
      ⟨146, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 50 hp) Q2.T146_110_2 Q2.hfix146_110_2 Q2.hinj146_110_2
      Q2.hcardT146_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_110_2 i) (Q2.hfix146_110_2 i) _)
      colCert_146_110_50.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_110_75 (hp : 75 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 75 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 75 (transLenTr ⟨110, by decide⟩ 75 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 75 (transLenTr ⟨110, by decide⟩ 75 hp)) T146_110
      hfix146_110 hinj146_110 hcardT146_110
      (fun i => conj_mem_of_fixedPoints _ _ (T146_110 i) (hfix146_110 i) _)
      ⟨146, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 75 hp) Q2.T146_110_2 Q2.hfix146_110_2 Q2.hinj146_110_2
      Q2.hcardT146_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_110_2 i) (Q2.hfix146_110_2 i) _)
      colCert_146_110_75.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_110_100 (hp : 100 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 100 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 100 (transLenTr ⟨110, by decide⟩ 100 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 100 (transLenTr ⟨110, by decide⟩ 100 hp)) T146_110
      hfix146_110 hinj146_110 hcardT146_110
      (fun i => conj_mem_of_fixedPoints _ _ (T146_110 i) (hfix146_110 i) _)
      ⟨146, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 100 hp) Q2.T146_110_2 Q2.hfix146_110_2 Q2.hinj146_110_2
      Q2.hcardT146_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_110_2 i) (Q2.hfix146_110_2 i) _)
      colCert_146_110_100.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_111_0 (hp : 0 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 0 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 0 (transLenTr ⟨111, by decide⟩ 0 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 0 (transLenTr ⟨111, by decide⟩ 0 hp)) T146_111
      hfix146_111 hinj146_111 hcardT146_111
      (fun i => conj_mem_of_fixedPoints _ _ (T146_111 i) (hfix146_111 i) _)
      ⟨146, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 0 hp) Q2.T146_111_2 Q2.hfix146_111_2 Q2.hinj146_111_2
      Q2.hcardT146_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_111_2 i) (Q2.hfix146_111_2 i) _)
      colCert_146_111_0.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_111_1 (hp : 1 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 1 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 1 (transLenTr ⟨111, by decide⟩ 1 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 1 (transLenTr ⟨111, by decide⟩ 1 hp)) T146_111
      hfix146_111 hinj146_111 hcardT146_111
      (fun i => conj_mem_of_fixedPoints _ _ (T146_111 i) (hfix146_111 i) _)
      ⟨146, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 1 hp) Q2.T146_111_2 Q2.hfix146_111_2 Q2.hinj146_111_2
      Q2.hcardT146_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_111_2 i) (Q2.hfix146_111_2 i) _)
      colCert_146_111_1.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_111_2 (hp : 2 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 2 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 2 (transLenTr ⟨111, by decide⟩ 2 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 2 (transLenTr ⟨111, by decide⟩ 2 hp)) T146_111
      hfix146_111 hinj146_111 hcardT146_111
      (fun i => conj_mem_of_fixedPoints _ _ (T146_111 i) (hfix146_111 i) _)
      ⟨146, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 2 hp) Q2.T146_111_2 Q2.hfix146_111_2 Q2.hinj146_111_2
      Q2.hcardT146_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_111_2 i) (Q2.hfix146_111_2 i) _)
      colCert_146_111_2.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_111_3 (hp : 3 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 3 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 3 (transLenTr ⟨111, by decide⟩ 3 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 3 (transLenTr ⟨111, by decide⟩ 3 hp)) T146_111
      hfix146_111 hinj146_111 hcardT146_111
      (fun i => conj_mem_of_fixedPoints _ _ (T146_111 i) (hfix146_111 i) _)
      ⟨146, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 3 hp) Q2.T146_111_2 Q2.hfix146_111_2 Q2.hinj146_111_2
      Q2.hcardT146_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_111_2 i) (Q2.hfix146_111_2 i) _)
      colCert_146_111_3.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_111_4 (hp : 4 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 4 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 4 (transLenTr ⟨111, by decide⟩ 4 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 4 (transLenTr ⟨111, by decide⟩ 4 hp)) T146_111
      hfix146_111 hinj146_111 hcardT146_111
      (fun i => conj_mem_of_fixedPoints _ _ (T146_111 i) (hfix146_111 i) _)
      ⟨146, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 4 hp) Q2.T146_111_2 Q2.hfix146_111_2 Q2.hinj146_111_2
      Q2.hcardT146_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_111_2 i) (Q2.hfix146_111_2 i) _)
      colCert_146_111_4.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_111_5 (hp : 5 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 5 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 5 (transLenTr ⟨111, by decide⟩ 5 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 5 (transLenTr ⟨111, by decide⟩ 5 hp)) T146_111
      hfix146_111 hinj146_111 hcardT146_111
      (fun i => conj_mem_of_fixedPoints _ _ (T146_111 i) (hfix146_111 i) _)
      ⟨146, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 5 hp) Q2.T146_111_2 Q2.hfix146_111_2 Q2.hinj146_111_2
      Q2.hcardT146_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_111_2 i) (Q2.hfix146_111_2 i) _)
      colCert_146_111_5.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_111_10 (hp : 10 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 10 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 10 (transLenTr ⟨111, by decide⟩ 10 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨146, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 10 (transLenTr ⟨111, by decide⟩ 10 hp)) T146_111
      hfix146_111 hinj146_111 hcardT146_111
      (fun i => conj_mem_of_fixedPoints _ _ (T146_111 i) (hfix146_111 i) _)
      ⟨146, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 10 hp) Q2.T146_111_2 Q2.hfix146_111_2 Q2.hinj146_111_2
      Q2.hcardT146_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_111_2 i) (Q2.hfix146_111_2 i) _)
      ?_).symm
  rw [show colData1 (⟨146, by decide⟩ : Fin 148)
        ((colE1 ⟨111, by decide⟩ 10 (transLenTr ⟨111, by decide⟩ 10 hp) : ↥(reps ⟨111, by decide⟩)) : Coordinate 1)
        T146_111 = colFn colCertDiv_146_111_10.D1 (m := 5) from colCertDiv_146_111_10.bind1,
    show colData2 (⟨146, by decide⟩ : Fin 148)
        ((colE2 ⟨111, by decide⟩ 10 hp : ↥(Q2.reps ⟨111, by decide⟩)) : Coordinate 2)
        Q2.T146_111_2 = colFn colCertDiv_146_111_10.D2 (m := 5) from colCertDiv_146_111_10.bind2]
  rw [alnId_146 j hj]
  exact fastcode_of_div ⟨146, by decide⟩ _ _ _
    ((alnId_146 j hj) ▸ Q2.listedAt (⟨146, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨146, by decide⟩ : Fin 148) hj hq).1) colCertDiv_146_111_10_match


theorem leaf_146_111_15 (hp : 15 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 15 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 15 (transLenTr ⟨111, by decide⟩ 15 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨146, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 15 (transLenTr ⟨111, by decide⟩ 15 hp)) T146_111
      hfix146_111 hinj146_111 hcardT146_111
      (fun i => conj_mem_of_fixedPoints _ _ (T146_111 i) (hfix146_111 i) _)
      ⟨146, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 15 hp) Q2.T146_111_2 Q2.hfix146_111_2 Q2.hinj146_111_2
      Q2.hcardT146_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_111_2 i) (Q2.hfix146_111_2 i) _)
      ?_).symm
  rw [show colData1 (⟨146, by decide⟩ : Fin 148)
        ((colE1 ⟨111, by decide⟩ 15 (transLenTr ⟨111, by decide⟩ 15 hp) : ↥(reps ⟨111, by decide⟩)) : Coordinate 1)
        T146_111 = colFn colCertDiv_146_111_15.D1 (m := 5) from colCertDiv_146_111_15.bind1,
    show colData2 (⟨146, by decide⟩ : Fin 148)
        ((colE2 ⟨111, by decide⟩ 15 hp : ↥(Q2.reps ⟨111, by decide⟩)) : Coordinate 2)
        Q2.T146_111_2 = colFn colCertDiv_146_111_15.D2 (m := 5) from colCertDiv_146_111_15.bind2]
  rw [alnId_146 j hj]
  exact fastcode_of_div ⟨146, by decide⟩ _ _ _
    ((alnId_146 j hj) ▸ Q2.listedAt (⟨146, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨146, by decide⟩ : Fin 148) hj hq).1) colCertDiv_146_111_15_match


theorem leaf_146_111_20 (hp : 20 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 20 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 20 (transLenTr ⟨111, by decide⟩ 20 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨146, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 20 (transLenTr ⟨111, by decide⟩ 20 hp)) T146_111
      hfix146_111 hinj146_111 hcardT146_111
      (fun i => conj_mem_of_fixedPoints _ _ (T146_111 i) (hfix146_111 i) _)
      ⟨146, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 20 hp) Q2.T146_111_2 Q2.hfix146_111_2 Q2.hinj146_111_2
      Q2.hcardT146_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_111_2 i) (Q2.hfix146_111_2 i) _)
      ?_).symm
  rw [show colData1 (⟨146, by decide⟩ : Fin 148)
        ((colE1 ⟨111, by decide⟩ 20 (transLenTr ⟨111, by decide⟩ 20 hp) : ↥(reps ⟨111, by decide⟩)) : Coordinate 1)
        T146_111 = colFn colCertDiv_146_111_20.D1 (m := 5) from colCertDiv_146_111_20.bind1,
    show colData2 (⟨146, by decide⟩ : Fin 148)
        ((colE2 ⟨111, by decide⟩ 20 hp : ↥(Q2.reps ⟨111, by decide⟩)) : Coordinate 2)
        Q2.T146_111_2 = colFn colCertDiv_146_111_20.D2 (m := 5) from colCertDiv_146_111_20.bind2]
  rw [alnId_146 j hj]
  exact fastcode_of_div ⟨146, by decide⟩ _ _ _
    ((alnId_146 j hj) ▸ Q2.listedAt (⟨146, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨146, by decide⟩ : Fin 148) hj hq).1) colCertDiv_146_111_20_match


theorem leaf_146_112_0 (hp : 0 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 0 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 0 (transLenTr ⟨112, by decide⟩ 0 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 0 (transLenTr ⟨112, by decide⟩ 0 hp)) T146_112
      hfix146_112 hinj146_112 hcardT146_112
      (fun i => conj_mem_of_fixedPoints _ _ (T146_112 i) (hfix146_112 i) _)
      ⟨146, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 0 hp) Q2.T146_112_2 Q2.hfix146_112_2 Q2.hinj146_112_2
      Q2.hcardT146_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_112_2 i) (Q2.hfix146_112_2 i) _)
      colCert_146_112_0.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_112_1 (hp : 1 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 1 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 1 (transLenTr ⟨112, by decide⟩ 1 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 1 (transLenTr ⟨112, by decide⟩ 1 hp)) T146_112
      hfix146_112 hinj146_112 hcardT146_112
      (fun i => conj_mem_of_fixedPoints _ _ (T146_112 i) (hfix146_112 i) _)
      ⟨146, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 1 hp) Q2.T146_112_2 Q2.hfix146_112_2 Q2.hinj146_112_2
      Q2.hcardT146_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_112_2 i) (Q2.hfix146_112_2 i) _)
      colCert_146_112_1.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_112_2 (hp : 2 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 2 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 2 (transLenTr ⟨112, by decide⟩ 2 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 2 (transLenTr ⟨112, by decide⟩ 2 hp)) T146_112
      hfix146_112 hinj146_112 hcardT146_112
      (fun i => conj_mem_of_fixedPoints _ _ (T146_112 i) (hfix146_112 i) _)
      ⟨146, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 2 hp) Q2.T146_112_2 Q2.hfix146_112_2 Q2.hinj146_112_2
      Q2.hcardT146_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_112_2 i) (Q2.hfix146_112_2 i) _)
      colCert_146_112_2.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_112_3 (hp : 3 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 3 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 3 (transLenTr ⟨112, by decide⟩ 3 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 3 (transLenTr ⟨112, by decide⟩ 3 hp)) T146_112
      hfix146_112 hinj146_112 hcardT146_112
      (fun i => conj_mem_of_fixedPoints _ _ (T146_112 i) (hfix146_112 i) _)
      ⟨146, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 3 hp) Q2.T146_112_2 Q2.hfix146_112_2 Q2.hinj146_112_2
      Q2.hcardT146_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_112_2 i) (Q2.hfix146_112_2 i) _)
      colCert_146_112_3.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_112_4 (hp : 4 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 4 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 4 (transLenTr ⟨112, by decide⟩ 4 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 4 (transLenTr ⟨112, by decide⟩ 4 hp)) T146_112
      hfix146_112 hinj146_112 hcardT146_112
      (fun i => conj_mem_of_fixedPoints _ _ (T146_112 i) (hfix146_112 i) _)
      ⟨146, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 4 hp) Q2.T146_112_2 Q2.hfix146_112_2 Q2.hinj146_112_2
      Q2.hcardT146_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_112_2 i) (Q2.hfix146_112_2 i) _)
      colCert_146_112_4.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_112_5 (hp : 5 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 5 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 5 (transLenTr ⟨112, by decide⟩ 5 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 5 (transLenTr ⟨112, by decide⟩ 5 hp)) T146_112
      hfix146_112 hinj146_112 hcardT146_112
      (fun i => conj_mem_of_fixedPoints _ _ (T146_112 i) (hfix146_112 i) _)
      ⟨146, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 5 hp) Q2.T146_112_2 Q2.hfix146_112_2 Q2.hinj146_112_2
      Q2.hcardT146_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_112_2 i) (Q2.hfix146_112_2 i) _)
      colCert_146_112_5.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_112_10 (hp : 10 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 10 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 10 (transLenTr ⟨112, by decide⟩ 10 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 10 (transLenTr ⟨112, by decide⟩ 10 hp)) T146_112
      hfix146_112 hinj146_112 hcardT146_112
      (fun i => conj_mem_of_fixedPoints _ _ (T146_112 i) (hfix146_112 i) _)
      ⟨146, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 10 hp) Q2.T146_112_2 Q2.hfix146_112_2 Q2.hinj146_112_2
      Q2.hcardT146_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_112_2 i) (Q2.hfix146_112_2 i) _)
      colCert_146_112_10.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_112_15 (hp : 15 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 15 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 15 (transLenTr ⟨112, by decide⟩ 15 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨146, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 15 (transLenTr ⟨112, by decide⟩ 15 hp)) T146_112
      hfix146_112 hinj146_112 hcardT146_112
      (fun i => conj_mem_of_fixedPoints _ _ (T146_112 i) (hfix146_112 i) _)
      ⟨146, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 15 hp) Q2.T146_112_2 Q2.hfix146_112_2 Q2.hinj146_112_2
      Q2.hcardT146_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_112_2 i) (Q2.hfix146_112_2 i) _)
      ?_).symm
  rw [show colData1 (⟨146, by decide⟩ : Fin 148)
        ((colE1 ⟨112, by decide⟩ 15 (transLenTr ⟨112, by decide⟩ 15 hp) : ↥(reps ⟨112, by decide⟩)) : Coordinate 1)
        T146_112 = colFn colCertDiv_146_112_15.D1 (m := 5) from colCertDiv_146_112_15.bind1,
    show colData2 (⟨146, by decide⟩ : Fin 148)
        ((colE2 ⟨112, by decide⟩ 15 hp : ↥(Q2.reps ⟨112, by decide⟩)) : Coordinate 2)
        Q2.T146_112_2 = colFn colCertDiv_146_112_15.D2 (m := 5) from colCertDiv_146_112_15.bind2]
  rw [alnId_146 j hj]
  exact fastcode_of_div ⟨146, by decide⟩ _ _ _
    ((alnId_146 j hj) ▸ Q2.listedAt (⟨146, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨146, by decide⟩ : Fin 148) hj hq).1) colCertDiv_146_112_15_match


theorem leaf_146_112_20 (hp : 20 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 20 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 20 (transLenTr ⟨112, by decide⟩ 20 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨146, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 20 (transLenTr ⟨112, by decide⟩ 20 hp)) T146_112
      hfix146_112 hinj146_112 hcardT146_112
      (fun i => conj_mem_of_fixedPoints _ _ (T146_112 i) (hfix146_112 i) _)
      ⟨146, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 20 hp) Q2.T146_112_2 Q2.hfix146_112_2 Q2.hinj146_112_2
      Q2.hcardT146_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_112_2 i) (Q2.hfix146_112_2 i) _)
      ?_).symm
  rw [show colData1 (⟨146, by decide⟩ : Fin 148)
        ((colE1 ⟨112, by decide⟩ 20 (transLenTr ⟨112, by decide⟩ 20 hp) : ↥(reps ⟨112, by decide⟩)) : Coordinate 1)
        T146_112 = colFn colCertDiv_146_112_20.D1 (m := 5) from colCertDiv_146_112_20.bind1,
    show colData2 (⟨146, by decide⟩ : Fin 148)
        ((colE2 ⟨112, by decide⟩ 20 hp : ↥(Q2.reps ⟨112, by decide⟩)) : Coordinate 2)
        Q2.T146_112_2 = colFn colCertDiv_146_112_20.D2 (m := 5) from colCertDiv_146_112_20.bind2]
  rw [alnId_146 j hj]
  exact fastcode_of_div ⟨146, by decide⟩ _ _ _
    ((alnId_146 j hj) ▸ Q2.listedAt (⟨146, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨146, by decide⟩ : Fin 148) hj hq).1) colCertDiv_146_112_20_match


theorem leaf_146_113_0 (hp : 0 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 0 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 0 (transLenTr ⟨113, by decide⟩ 0 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 0 (transLenTr ⟨113, by decide⟩ 0 hp)) T146_113
      hfix146_113 hinj146_113 hcardT146_113
      (fun i => conj_mem_of_fixedPoints _ _ (T146_113 i) (hfix146_113 i) _)
      ⟨146, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 0 hp) Q2.T146_113_2 Q2.hfix146_113_2 Q2.hinj146_113_2
      Q2.hcardT146_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_113_2 i) (Q2.hfix146_113_2 i) _)
      colCert_146_113_0.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_113_1 (hp : 1 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 1 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 1 (transLenTr ⟨113, by decide⟩ 1 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 1 (transLenTr ⟨113, by decide⟩ 1 hp)) T146_113
      hfix146_113 hinj146_113 hcardT146_113
      (fun i => conj_mem_of_fixedPoints _ _ (T146_113 i) (hfix146_113 i) _)
      ⟨146, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 1 hp) Q2.T146_113_2 Q2.hfix146_113_2 Q2.hinj146_113_2
      Q2.hcardT146_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_113_2 i) (Q2.hfix146_113_2 i) _)
      colCert_146_113_1.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_113_2 (hp : 2 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 2 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 2 (transLenTr ⟨113, by decide⟩ 2 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 2 (transLenTr ⟨113, by decide⟩ 2 hp)) T146_113
      hfix146_113 hinj146_113 hcardT146_113
      (fun i => conj_mem_of_fixedPoints _ _ (T146_113 i) (hfix146_113 i) _)
      ⟨146, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 2 hp) Q2.T146_113_2 Q2.hfix146_113_2 Q2.hinj146_113_2
      Q2.hcardT146_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_113_2 i) (Q2.hfix146_113_2 i) _)
      colCert_146_113_2.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_113_3 (hp : 3 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 3 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 3 (transLenTr ⟨113, by decide⟩ 3 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 3 (transLenTr ⟨113, by decide⟩ 3 hp)) T146_113
      hfix146_113 hinj146_113 hcardT146_113
      (fun i => conj_mem_of_fixedPoints _ _ (T146_113 i) (hfix146_113 i) _)
      ⟨146, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 3 hp) Q2.T146_113_2 Q2.hfix146_113_2 Q2.hinj146_113_2
      Q2.hcardT146_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_113_2 i) (Q2.hfix146_113_2 i) _)
      colCert_146_113_3.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_113_4 (hp : 4 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 4 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 4 (transLenTr ⟨113, by decide⟩ 4 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 4 (transLenTr ⟨113, by decide⟩ 4 hp)) T146_113
      hfix146_113 hinj146_113 hcardT146_113
      (fun i => conj_mem_of_fixedPoints _ _ (T146_113 i) (hfix146_113 i) _)
      ⟨146, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 4 hp) Q2.T146_113_2 Q2.hfix146_113_2 Q2.hinj146_113_2
      Q2.hcardT146_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_113_2 i) (Q2.hfix146_113_2 i) _)
      colCert_146_113_4.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_113_5 (hp : 5 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 5 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 5 (transLenTr ⟨113, by decide⟩ 5 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 5 (transLenTr ⟨113, by decide⟩ 5 hp)) T146_113
      hfix146_113 hinj146_113 hcardT146_113
      (fun i => conj_mem_of_fixedPoints _ _ (T146_113 i) (hfix146_113 i) _)
      ⟨146, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 5 hp) Q2.T146_113_2 Q2.hfix146_113_2 Q2.hinj146_113_2
      Q2.hcardT146_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_113_2 i) (Q2.hfix146_113_2 i) _)
      colCert_146_113_5.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_113_10 (hp : 10 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 10 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 10 (transLenTr ⟨113, by decide⟩ 10 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨146, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 10 (transLenTr ⟨113, by decide⟩ 10 hp)) T146_113
      hfix146_113 hinj146_113 hcardT146_113
      (fun i => conj_mem_of_fixedPoints _ _ (T146_113 i) (hfix146_113 i) _)
      ⟨146, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 10 hp) Q2.T146_113_2 Q2.hfix146_113_2 Q2.hinj146_113_2
      Q2.hcardT146_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_113_2 i) (Q2.hfix146_113_2 i) _)
      ?_).symm
  rw [show colData1 (⟨146, by decide⟩ : Fin 148)
        ((colE1 ⟨113, by decide⟩ 10 (transLenTr ⟨113, by decide⟩ 10 hp) : ↥(reps ⟨113, by decide⟩)) : Coordinate 1)
        T146_113 = colFn colCertDiv_146_113_10.D1 (m := 5) from colCertDiv_146_113_10.bind1,
    show colData2 (⟨146, by decide⟩ : Fin 148)
        ((colE2 ⟨113, by decide⟩ 10 hp : ↥(Q2.reps ⟨113, by decide⟩)) : Coordinate 2)
        Q2.T146_113_2 = colFn colCertDiv_146_113_10.D2 (m := 5) from colCertDiv_146_113_10.bind2]
  rw [alnId_146 j hj]
  exact fastcode_of_div ⟨146, by decide⟩ _ _ _
    ((alnId_146 j hj) ▸ Q2.listedAt (⟨146, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨146, by decide⟩ : Fin 148) hj hq).1) colCertDiv_146_113_10_match


theorem leaf_146_113_15 (hp : 15 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 15 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 15 (transLenTr ⟨113, by decide⟩ 15 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨146, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 15 (transLenTr ⟨113, by decide⟩ 15 hp)) T146_113
      hfix146_113 hinj146_113 hcardT146_113
      (fun i => conj_mem_of_fixedPoints _ _ (T146_113 i) (hfix146_113 i) _)
      ⟨146, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 15 hp) Q2.T146_113_2 Q2.hfix146_113_2 Q2.hinj146_113_2
      Q2.hcardT146_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_113_2 i) (Q2.hfix146_113_2 i) _)
      ?_).symm
  rw [show colData1 (⟨146, by decide⟩ : Fin 148)
        ((colE1 ⟨113, by decide⟩ 15 (transLenTr ⟨113, by decide⟩ 15 hp) : ↥(reps ⟨113, by decide⟩)) : Coordinate 1)
        T146_113 = colFn colCertDiv_146_113_15.D1 (m := 5) from colCertDiv_146_113_15.bind1,
    show colData2 (⟨146, by decide⟩ : Fin 148)
        ((colE2 ⟨113, by decide⟩ 15 hp : ↥(Q2.reps ⟨113, by decide⟩)) : Coordinate 2)
        Q2.T146_113_2 = colFn colCertDiv_146_113_15.D2 (m := 5) from colCertDiv_146_113_15.bind2]
  rw [alnId_146 j hj]
  exact fastcode_of_div ⟨146, by decide⟩ _ _ _
    ((alnId_146 j hj) ▸ Q2.listedAt (⟨146, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨146, by decide⟩ : Fin 148) hj hq).1) colCertDiv_146_113_15_match


theorem leaf_146_113_20 (hp : 20 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 20 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 20 (transLenTr ⟨113, by decide⟩ 20 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨146, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 20 (transLenTr ⟨113, by decide⟩ 20 hp)) T146_113
      hfix146_113 hinj146_113 hcardT146_113
      (fun i => conj_mem_of_fixedPoints _ _ (T146_113 i) (hfix146_113 i) _)
      ⟨146, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 20 hp) Q2.T146_113_2 Q2.hfix146_113_2 Q2.hinj146_113_2
      Q2.hcardT146_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_113_2 i) (Q2.hfix146_113_2 i) _)
      ?_).symm
  rw [show colData1 (⟨146, by decide⟩ : Fin 148)
        ((colE1 ⟨113, by decide⟩ 20 (transLenTr ⟨113, by decide⟩ 20 hp) : ↥(reps ⟨113, by decide⟩)) : Coordinate 1)
        T146_113 = colFn colCertDiv_146_113_20.D1 (m := 5) from colCertDiv_146_113_20.bind1,
    show colData2 (⟨146, by decide⟩ : Fin 148)
        ((colE2 ⟨113, by decide⟩ 20 hp : ↥(Q2.reps ⟨113, by decide⟩)) : Coordinate 2)
        Q2.T146_113_2 = colFn colCertDiv_146_113_20.D2 (m := 5) from colCertDiv_146_113_20.bind2]
  rw [alnId_146 j hj]
  exact fastcode_of_div ⟨146, by decide⟩ _ _ _
    ((alnId_146 j hj) ▸ Q2.listedAt (⟨146, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨146, by decide⟩ : Fin 148) hj hq).1) colCertDiv_146_113_20_match


theorem leaf_146_114_0 (hp : 0 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 0 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 0 (transLenTr ⟨114, by decide⟩ 0 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 0 (transLenTr ⟨114, by decide⟩ 0 hp)) T146_114
      hfix146_114 hinj146_114 hcardT146_114
      (fun i => conj_mem_of_fixedPoints _ _ (T146_114 i) (hfix146_114 i) _)
      ⟨146, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 0 hp) Q2.T146_114_2 Q2.hfix146_114_2 Q2.hinj146_114_2
      Q2.hcardT146_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_114_2 i) (Q2.hfix146_114_2 i) _)
      colCert_146_114_0.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_114_1 (hp : 1 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 1 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 1 (transLenTr ⟨114, by decide⟩ 1 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 1 (transLenTr ⟨114, by decide⟩ 1 hp)) T146_114
      hfix146_114 hinj146_114 hcardT146_114
      (fun i => conj_mem_of_fixedPoints _ _ (T146_114 i) (hfix146_114 i) _)
      ⟨146, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 1 hp) Q2.T146_114_2 Q2.hfix146_114_2 Q2.hinj146_114_2
      Q2.hcardT146_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_114_2 i) (Q2.hfix146_114_2 i) _)
      colCert_146_114_1.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_114_2 (hp : 2 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 2 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 2 (transLenTr ⟨114, by decide⟩ 2 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 2 (transLenTr ⟨114, by decide⟩ 2 hp)) T146_114
      hfix146_114 hinj146_114 hcardT146_114
      (fun i => conj_mem_of_fixedPoints _ _ (T146_114 i) (hfix146_114 i) _)
      ⟨146, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 2 hp) Q2.T146_114_2 Q2.hfix146_114_2 Q2.hinj146_114_2
      Q2.hcardT146_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_114_2 i) (Q2.hfix146_114_2 i) _)
      colCert_146_114_2.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_114_3 (hp : 3 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 3 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 3 (transLenTr ⟨114, by decide⟩ 3 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 3 (transLenTr ⟨114, by decide⟩ 3 hp)) T146_114
      hfix146_114 hinj146_114 hcardT146_114
      (fun i => conj_mem_of_fixedPoints _ _ (T146_114 i) (hfix146_114 i) _)
      ⟨146, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 3 hp) Q2.T146_114_2 Q2.hfix146_114_2 Q2.hinj146_114_2
      Q2.hcardT146_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_114_2 i) (Q2.hfix146_114_2 i) _)
      colCert_146_114_3.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_114_4 (hp : 4 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 4 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 4 (transLenTr ⟨114, by decide⟩ 4 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 4 (transLenTr ⟨114, by decide⟩ 4 hp)) T146_114
      hfix146_114 hinj146_114 hcardT146_114
      (fun i => conj_mem_of_fixedPoints _ _ (T146_114 i) (hfix146_114 i) _)
      ⟨146, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 4 hp) Q2.T146_114_2 Q2.hfix146_114_2 Q2.hinj146_114_2
      Q2.hcardT146_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_114_2 i) (Q2.hfix146_114_2 i) _)
      colCert_146_114_4.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_114_5 (hp : 5 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 5 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 5 (transLenTr ⟨114, by decide⟩ 5 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 5 (transLenTr ⟨114, by decide⟩ 5 hp)) T146_114
      hfix146_114 hinj146_114 hcardT146_114
      (fun i => conj_mem_of_fixedPoints _ _ (T146_114 i) (hfix146_114 i) _)
      ⟨146, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 5 hp) Q2.T146_114_2 Q2.hfix146_114_2 Q2.hinj146_114_2
      Q2.hcardT146_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_114_2 i) (Q2.hfix146_114_2 i) _)
      colCert_146_114_5.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_114_10 (hp : 10 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 10 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 10 (transLenTr ⟨114, by decide⟩ 10 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 10 (transLenTr ⟨114, by decide⟩ 10 hp)) T146_114
      hfix146_114 hinj146_114 hcardT146_114
      (fun i => conj_mem_of_fixedPoints _ _ (T146_114 i) (hfix146_114 i) _)
      ⟨146, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 10 hp) Q2.T146_114_2 Q2.hfix146_114_2 Q2.hinj146_114_2
      Q2.hcardT146_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_114_2 i) (Q2.hfix146_114_2 i) _)
      colCert_146_114_10.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_114_15 (hp : 15 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 15 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 15 (transLenTr ⟨114, by decide⟩ 15 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 15 (transLenTr ⟨114, by decide⟩ 15 hp)) T146_114
      hfix146_114 hinj146_114 hcardT146_114
      (fun i => conj_mem_of_fixedPoints _ _ (T146_114 i) (hfix146_114 i) _)
      ⟨146, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 15 hp) Q2.T146_114_2 Q2.hfix146_114_2 Q2.hinj146_114_2
      Q2.hcardT146_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_114_2 i) (Q2.hfix146_114_2 i) _)
      colCert_146_114_15.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_114_20 (hp : 20 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 20 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 20 (transLenTr ⟨114, by decide⟩ 20 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 20 (transLenTr ⟨114, by decide⟩ 20 hp)) T146_114
      hfix146_114 hinj146_114 hcardT146_114
      (fun i => conj_mem_of_fixedPoints _ _ (T146_114 i) (hfix146_114 i) _)
      ⟨146, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 20 hp) Q2.T146_114_2 Q2.hfix146_114_2 Q2.hinj146_114_2
      Q2.hcardT146_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_114_2 i) (Q2.hfix146_114_2 i) _)
      colCert_146_114_20.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_115_0 (hp : 0 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 0 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 0 (transLenTr ⟨115, by decide⟩ 0 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 0 (transLenTr ⟨115, by decide⟩ 0 hp)) T146_115
      hfix146_115 hinj146_115 hcardT146_115
      (fun i => conj_mem_of_fixedPoints _ _ (T146_115 i) (hfix146_115 i) _)
      ⟨146, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 0 hp) Q2.T146_115_2 Q2.hfix146_115_2 Q2.hinj146_115_2
      Q2.hcardT146_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_115_2 i) (Q2.hfix146_115_2 i) _)
      colCert_146_115_0.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_115_1 (hp : 1 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 1 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 1 (transLenTr ⟨115, by decide⟩ 1 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 1 (transLenTr ⟨115, by decide⟩ 1 hp)) T146_115
      hfix146_115 hinj146_115 hcardT146_115
      (fun i => conj_mem_of_fixedPoints _ _ (T146_115 i) (hfix146_115 i) _)
      ⟨146, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 1 hp) Q2.T146_115_2 Q2.hfix146_115_2 Q2.hinj146_115_2
      Q2.hcardT146_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_115_2 i) (Q2.hfix146_115_2 i) _)
      colCert_146_115_1.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_115_2 (hp : 2 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 2 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 2 (transLenTr ⟨115, by decide⟩ 2 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 2 (transLenTr ⟨115, by decide⟩ 2 hp)) T146_115
      hfix146_115 hinj146_115 hcardT146_115
      (fun i => conj_mem_of_fixedPoints _ _ (T146_115 i) (hfix146_115 i) _)
      ⟨146, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 2 hp) Q2.T146_115_2 Q2.hfix146_115_2 Q2.hinj146_115_2
      Q2.hcardT146_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_115_2 i) (Q2.hfix146_115_2 i) _)
      colCert_146_115_2.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_115_3 (hp : 3 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 3 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 3 (transLenTr ⟨115, by decide⟩ 3 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 3 (transLenTr ⟨115, by decide⟩ 3 hp)) T146_115
      hfix146_115 hinj146_115 hcardT146_115
      (fun i => conj_mem_of_fixedPoints _ _ (T146_115 i) (hfix146_115 i) _)
      ⟨146, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 3 hp) Q2.T146_115_2 Q2.hfix146_115_2 Q2.hinj146_115_2
      Q2.hcardT146_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_115_2 i) (Q2.hfix146_115_2 i) _)
      colCert_146_115_3.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_115_4 (hp : 4 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 4 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 4 (transLenTr ⟨115, by decide⟩ 4 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 4 (transLenTr ⟨115, by decide⟩ 4 hp)) T146_115
      hfix146_115 hinj146_115 hcardT146_115
      (fun i => conj_mem_of_fixedPoints _ _ (T146_115 i) (hfix146_115 i) _)
      ⟨146, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 4 hp) Q2.T146_115_2 Q2.hfix146_115_2 Q2.hinj146_115_2
      Q2.hcardT146_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_115_2 i) (Q2.hfix146_115_2 i) _)
      colCert_146_115_4.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_115_5 (hp : 5 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 5 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 5 (transLenTr ⟨115, by decide⟩ 5 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 5 (transLenTr ⟨115, by decide⟩ 5 hp)) T146_115
      hfix146_115 hinj146_115 hcardT146_115
      (fun i => conj_mem_of_fixedPoints _ _ (T146_115 i) (hfix146_115 i) _)
      ⟨146, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 5 hp) Q2.T146_115_2 Q2.hfix146_115_2 Q2.hinj146_115_2
      Q2.hcardT146_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_115_2 i) (Q2.hfix146_115_2 i) _)
      colCert_146_115_5.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_115_10 (hp : 10 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 10 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 10 (transLenTr ⟨115, by decide⟩ 10 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 10 (transLenTr ⟨115, by decide⟩ 10 hp)) T146_115
      hfix146_115 hinj146_115 hcardT146_115
      (fun i => conj_mem_of_fixedPoints _ _ (T146_115 i) (hfix146_115 i) _)
      ⟨146, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 10 hp) Q2.T146_115_2 Q2.hfix146_115_2 Q2.hinj146_115_2
      Q2.hcardT146_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_115_2 i) (Q2.hfix146_115_2 i) _)
      colCert_146_115_10.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_115_15 (hp : 15 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 15 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 15 (transLenTr ⟨115, by decide⟩ 15 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 15 (transLenTr ⟨115, by decide⟩ 15 hp)) T146_115
      hfix146_115 hinj146_115 hcardT146_115
      (fun i => conj_mem_of_fixedPoints _ _ (T146_115 i) (hfix146_115 i) _)
      ⟨146, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 15 hp) Q2.T146_115_2 Q2.hfix146_115_2 Q2.hinj146_115_2
      Q2.hcardT146_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_115_2 i) (Q2.hfix146_115_2 i) _)
      colCert_146_115_15.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_115_20 (hp : 20 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 20 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 20 (transLenTr ⟨115, by decide⟩ 20 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 20 (transLenTr ⟨115, by decide⟩ 20 hp)) T146_115
      hfix146_115 hinj146_115 hcardT146_115
      (fun i => conj_mem_of_fixedPoints _ _ (T146_115 i) (hfix146_115 i) _)
      ⟨146, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 20 hp) Q2.T146_115_2 Q2.hfix146_115_2 Q2.hinj146_115_2
      Q2.hcardT146_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_115_2 i) (Q2.hfix146_115_2 i) _)
      colCert_146_115_20.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_146_0 (hp : 0 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 0 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 0 (transLenTr ⟨146, by decide⟩ 0 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 0 (transLenTr ⟨146, by decide⟩ 0 hp)) T146_146
      hfix146_146 hinj146_146 hcardT146_146
      (fun i => conj_mem_of_fixedPoints _ _ (T146_146 i) (hfix146_146 i) _)
      ⟨146, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 0 hp) Q2.T146_146_2 Q2.hfix146_146_2 Q2.hinj146_146_2
      Q2.hcardT146_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_146_2 i) (Q2.hfix146_146_2 i) _)
      colCert_146_146_0.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_146_1 (hp : 1 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 1 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 1 (transLenTr ⟨146, by decide⟩ 1 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 1 (transLenTr ⟨146, by decide⟩ 1 hp)) T146_146
      hfix146_146 hinj146_146 hcardT146_146
      (fun i => conj_mem_of_fixedPoints _ _ (T146_146 i) (hfix146_146 i) _)
      ⟨146, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 1 hp) Q2.T146_146_2 Q2.hfix146_146_2 Q2.hinj146_146_2
      Q2.hcardT146_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_146_2 i) (Q2.hfix146_146_2 i) _)
      colCert_146_146_1.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_146_2 (hp : 2 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 2 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 2 (transLenTr ⟨146, by decide⟩ 2 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 2 (transLenTr ⟨146, by decide⟩ 2 hp)) T146_146
      hfix146_146 hinj146_146 hcardT146_146
      (fun i => conj_mem_of_fixedPoints _ _ (T146_146 i) (hfix146_146 i) _)
      ⟨146, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 2 hp) Q2.T146_146_2 Q2.hfix146_146_2 Q2.hinj146_146_2
      Q2.hcardT146_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_146_2 i) (Q2.hfix146_146_2 i) _)
      colCert_146_146_2.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_146_3 (hp : 3 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 3 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 3 (transLenTr ⟨146, by decide⟩ 3 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 3 (transLenTr ⟨146, by decide⟩ 3 hp)) T146_146
      hfix146_146 hinj146_146 hcardT146_146
      (fun i => conj_mem_of_fixedPoints _ _ (T146_146 i) (hfix146_146 i) _)
      ⟨146, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 3 hp) Q2.T146_146_2 Q2.hfix146_146_2 Q2.hinj146_146_2
      Q2.hcardT146_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_146_2 i) (Q2.hfix146_146_2 i) _)
      colCert_146_146_3.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_146_4 (hp : 4 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 4 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 4 (transLenTr ⟨146, by decide⟩ 4 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 4 (transLenTr ⟨146, by decide⟩ 4 hp)) T146_146
      hfix146_146 hinj146_146 hcardT146_146
      (fun i => conj_mem_of_fixedPoints _ _ (T146_146 i) (hfix146_146 i) _)
      ⟨146, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 4 hp) Q2.T146_146_2 Q2.hfix146_146_2 Q2.hinj146_146_2
      Q2.hcardT146_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_146_2 i) (Q2.hfix146_146_2 i) _)
      colCert_146_146_4.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_146_5 (hp : 5 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 5 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 5 (transLenTr ⟨146, by decide⟩ 5 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 5 (transLenTr ⟨146, by decide⟩ 5 hp)) T146_146
      hfix146_146 hinj146_146 hcardT146_146
      (fun i => conj_mem_of_fixedPoints _ _ (T146_146 i) (hfix146_146 i) _)
      ⟨146, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 5 hp) Q2.T146_146_2 Q2.hfix146_146_2 Q2.hinj146_146_2
      Q2.hcardT146_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_146_2 i) (Q2.hfix146_146_2 i) _)
      colCert_146_146_5.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_146_6 (hp : 6 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 6 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 6 (transLenTr ⟨146, by decide⟩ 6 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 6 (transLenTr ⟨146, by decide⟩ 6 hp)) T146_146
      hfix146_146 hinj146_146 hcardT146_146
      (fun i => conj_mem_of_fixedPoints _ _ (T146_146 i) (hfix146_146 i) _)
      ⟨146, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 6 hp) Q2.T146_146_2 Q2.hfix146_146_2 Q2.hinj146_146_2
      Q2.hcardT146_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_146_2 i) (Q2.hfix146_146_2 i) _)
      colCert_146_146_6.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_146_7 (hp : 7 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 7 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 7 (transLenTr ⟨146, by decide⟩ 7 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 7 (transLenTr ⟨146, by decide⟩ 7 hp)) T146_146
      hfix146_146 hinj146_146 hcardT146_146
      (fun i => conj_mem_of_fixedPoints _ _ (T146_146 i) (hfix146_146 i) _)
      ⟨146, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 7 hp) Q2.T146_146_2 Q2.hfix146_146_2 Q2.hinj146_146_2
      Q2.hcardT146_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_146_2 i) (Q2.hfix146_146_2 i) _)
      colCert_146_146_7.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_146_8 (hp : 8 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 8 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 8 (transLenTr ⟨146, by decide⟩ 8 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 8 (transLenTr ⟨146, by decide⟩ 8 hp)) T146_146
      hfix146_146 hinj146_146 hcardT146_146
      (fun i => conj_mem_of_fixedPoints _ _ (T146_146 i) (hfix146_146 i) _)
      ⟨146, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 8 hp) Q2.T146_146_2 Q2.hfix146_146_2 Q2.hinj146_146_2
      Q2.hcardT146_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_146_2 i) (Q2.hfix146_146_2 i) _)
      colCert_146_146_8.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_146_9 (hp : 9 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 9 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 9 (transLenTr ⟨146, by decide⟩ 9 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 9 (transLenTr ⟨146, by decide⟩ 9 hp)) T146_146
      hfix146_146 hinj146_146 hcardT146_146
      (fun i => conj_mem_of_fixedPoints _ _ (T146_146 i) (hfix146_146 i) _)
      ⟨146, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 9 hp) Q2.T146_146_2 Q2.hfix146_146_2 Q2.hinj146_146_2
      Q2.hcardT146_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_146_2 i) (Q2.hfix146_146_2 i) _)
      colCert_146_146_9.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_146_10 (hp : 10 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 10 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 10 (transLenTr ⟨146, by decide⟩ 10 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 10 (transLenTr ⟨146, by decide⟩ 10 hp)) T146_146
      hfix146_146 hinj146_146 hcardT146_146
      (fun i => conj_mem_of_fixedPoints _ _ (T146_146 i) (hfix146_146 i) _)
      ⟨146, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 10 hp) Q2.T146_146_2 Q2.hfix146_146_2 Q2.hinj146_146_2
      Q2.hcardT146_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_146_2 i) (Q2.hfix146_146_2 i) _)
      colCert_146_146_10.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_146_11 (hp : 11 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 11 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 11 (transLenTr ⟨146, by decide⟩ 11 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 11 (transLenTr ⟨146, by decide⟩ 11 hp)) T146_146
      hfix146_146 hinj146_146 hcardT146_146
      (fun i => conj_mem_of_fixedPoints _ _ (T146_146 i) (hfix146_146 i) _)
      ⟨146, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 11 hp) Q2.T146_146_2 Q2.hfix146_146_2 Q2.hinj146_146_2
      Q2.hcardT146_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_146_2 i) (Q2.hfix146_146_2 i) _)
      colCert_146_146_11.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_146_12 (hp : 12 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 12 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 12 (transLenTr ⟨146, by decide⟩ 12 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 12 (transLenTr ⟨146, by decide⟩ 12 hp)) T146_146
      hfix146_146 hinj146_146 hcardT146_146
      (fun i => conj_mem_of_fixedPoints _ _ (T146_146 i) (hfix146_146 i) _)
      ⟨146, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 12 hp) Q2.T146_146_2 Q2.hfix146_146_2 Q2.hinj146_146_2
      Q2.hcardT146_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_146_2 i) (Q2.hfix146_146_2 i) _)
      colCert_146_146_12.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_146_13 (hp : 13 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 13 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 13 (transLenTr ⟨146, by decide⟩ 13 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 13 (transLenTr ⟨146, by decide⟩ 13 hp)) T146_146
      hfix146_146 hinj146_146 hcardT146_146
      (fun i => conj_mem_of_fixedPoints _ _ (T146_146 i) (hfix146_146 i) _)
      ⟨146, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 13 hp) Q2.T146_146_2 Q2.hfix146_146_2 Q2.hinj146_146_2
      Q2.hcardT146_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_146_2 i) (Q2.hfix146_146_2 i) _)
      colCert_146_146_13.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_146_14 (hp : 14 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 14 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 14 (transLenTr ⟨146, by decide⟩ 14 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 14 (transLenTr ⟨146, by decide⟩ 14 hp)) T146_146
      hfix146_146 hinj146_146 hcardT146_146
      (fun i => conj_mem_of_fixedPoints _ _ (T146_146 i) (hfix146_146 i) _)
      ⟨146, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 14 hp) Q2.T146_146_2 Q2.hfix146_146_2 Q2.hinj146_146_2
      Q2.hcardT146_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_146_2 i) (Q2.hfix146_146_2 i) _)
      colCert_146_146_14.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_146_15 (hp : 15 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 15 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 15 (transLenTr ⟨146, by decide⟩ 15 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 15 (transLenTr ⟨146, by decide⟩ 15 hp)) T146_146
      hfix146_146 hinj146_146 hcardT146_146
      (fun i => conj_mem_of_fixedPoints _ _ (T146_146 i) (hfix146_146 i) _)
      ⟨146, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 15 hp) Q2.T146_146_2 Q2.hfix146_146_2 Q2.hinj146_146_2
      Q2.hcardT146_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_146_2 i) (Q2.hfix146_146_2 i) _)
      colCert_146_146_15.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_146_16 (hp : 16 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 16 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 16 (transLenTr ⟨146, by decide⟩ 16 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 16 (transLenTr ⟨146, by decide⟩ 16 hp)) T146_146
      hfix146_146 hinj146_146 hcardT146_146
      (fun i => conj_mem_of_fixedPoints _ _ (T146_146 i) (hfix146_146 i) _)
      ⟨146, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 16 hp) Q2.T146_146_2 Q2.hfix146_146_2 Q2.hinj146_146_2
      Q2.hcardT146_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_146_2 i) (Q2.hfix146_146_2 i) _)
      colCert_146_146_16.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_146_17 (hp : 17 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 17 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 17 (transLenTr ⟨146, by decide⟩ 17 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 17 (transLenTr ⟨146, by decide⟩ 17 hp)) T146_146
      hfix146_146 hinj146_146 hcardT146_146
      (fun i => conj_mem_of_fixedPoints _ _ (T146_146 i) (hfix146_146 i) _)
      ⟨146, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 17 hp) Q2.T146_146_2 Q2.hfix146_146_2 Q2.hinj146_146_2
      Q2.hcardT146_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_146_2 i) (Q2.hfix146_146_2 i) _)
      colCert_146_146_17.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_146_18 (hp : 18 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 18 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 18 (transLenTr ⟨146, by decide⟩ 18 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 18 (transLenTr ⟨146, by decide⟩ 18 hp)) T146_146
      hfix146_146 hinj146_146 hcardT146_146
      (fun i => conj_mem_of_fixedPoints _ _ (T146_146 i) (hfix146_146 i) _)
      ⟨146, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 18 hp) Q2.T146_146_2 Q2.hfix146_146_2 Q2.hinj146_146_2
      Q2.hcardT146_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_146_2 i) (Q2.hfix146_146_2 i) _)
      colCert_146_146_18.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_146_19 (hp : 19 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 19 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 19 (transLenTr ⟨146, by decide⟩ 19 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 19 (transLenTr ⟨146, by decide⟩ 19 hp)) T146_146
      hfix146_146 hinj146_146 hcardT146_146
      (fun i => conj_mem_of_fixedPoints _ _ (T146_146 i) (hfix146_146 i) _)
      ⟨146, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 19 hp) Q2.T146_146_2 Q2.hfix146_146_2 Q2.hinj146_146_2
      Q2.hcardT146_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_146_2 i) (Q2.hfix146_146_2 i) _)
      colCert_146_146_19.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_146_20 (hp : 20 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 20 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 20 (transLenTr ⟨146, by decide⟩ 20 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 20 (transLenTr ⟨146, by decide⟩ 20 hp)) T146_146
      hfix146_146 hinj146_146 hcardT146_146
      (fun i => conj_mem_of_fixedPoints _ _ (T146_146 i) (hfix146_146 i) _)
      ⟨146, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 20 hp) Q2.T146_146_2 Q2.hfix146_146_2 Q2.hinj146_146_2
      Q2.hcardT146_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_146_2 i) (Q2.hfix146_146_2 i) _)
      colCert_146_146_20.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_146_21 (hp : 21 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 21 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 21 (transLenTr ⟨146, by decide⟩ 21 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 21 (transLenTr ⟨146, by decide⟩ 21 hp)) T146_146
      hfix146_146 hinj146_146 hcardT146_146
      (fun i => conj_mem_of_fixedPoints _ _ (T146_146 i) (hfix146_146 i) _)
      ⟨146, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 21 hp) Q2.T146_146_2 Q2.hfix146_146_2 Q2.hinj146_146_2
      Q2.hcardT146_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_146_2 i) (Q2.hfix146_146_2 i) _)
      colCert_146_146_21.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_146_22 (hp : 22 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 22 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 22 (transLenTr ⟨146, by decide⟩ 22 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 22 (transLenTr ⟨146, by decide⟩ 22 hp)) T146_146
      hfix146_146 hinj146_146 hcardT146_146
      (fun i => conj_mem_of_fixedPoints _ _ (T146_146 i) (hfix146_146 i) _)
      ⟨146, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 22 hp) Q2.T146_146_2 Q2.hfix146_146_2 Q2.hinj146_146_2
      Q2.hcardT146_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_146_2 i) (Q2.hfix146_146_2 i) _)
      colCert_146_146_22.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_146_23 (hp : 23 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 23 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 23 (transLenTr ⟨146, by decide⟩ 23 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 23 (transLenTr ⟨146, by decide⟩ 23 hp)) T146_146
      hfix146_146 hinj146_146 hcardT146_146
      (fun i => conj_mem_of_fixedPoints _ _ (T146_146 i) (hfix146_146 i) _)
      ⟨146, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 23 hp) Q2.T146_146_2 Q2.hfix146_146_2 Q2.hinj146_146_2
      Q2.hcardT146_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_146_2 i) (Q2.hfix146_146_2 i) _)
      colCert_146_146_23.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_146_146_24 (hp : 24 < (Q2.transData.getD 146 []).length)
    (j : Nat) (hj : j < (repChars.getD 146 []).length)
    (hq : (normIsRep.getD 146 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ 24 hp)
        (rowE2 (⟨146, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ 24 (transLenTr ⟨146, by decide⟩ 24 hp))
        (rowE1 (⟨146, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨146, by decide⟩ : Fin 148) ⟨146, by decide⟩ _
      (validAt ⟨146, by decide⟩ (listedAt ⟨146, by decide⟩ hj))
      (colE1 ⟨146, by decide⟩ 24 (transLenTr ⟨146, by decide⟩ 24 hp)) T146_146
      hfix146_146 hinj146_146 hcardT146_146
      (fun i => conj_mem_of_fixedPoints _ _ (T146_146 i) (hfix146_146 i) _)
      ⟨146, by decide⟩ ⟨146, by decide⟩ _
      (Q2.validAt ⟨146, by decide⟩ (Q2.listedAt ⟨146, by decide⟩
        (alnCheck_rep ⟨146, by decide⟩ hj hq).1))
      (colE2 ⟨146, by decide⟩ 24 hp) Q2.T146_146_2 Q2.hfix146_146_2 Q2.hinj146_146_2
      Q2.hcardT146_146_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T146_146_2 i) (Q2.hfix146_146_2 i) _)
      colCert_146_146_24.hD ?_).symm
  rw [alnId_146 j hj]


theorem leaf_147_1_0 (hp : 0 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp)) T147_1
      hfix147_1 hinj147_1 hcardT147_1
      (fun i => conj_mem_of_fixedPoints _ _ (T147_1 i) (hfix147_1 i) _)
      ⟨147, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 0 hp) Q2.T147_1_2 Q2.hfix147_1_2 Q2.hinj147_1_2
      Q2.hcardT147_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_1_2 i) (Q2.hfix147_1_2 i) _)
      colCert_147_1_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_1_1 (hp : 1 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp)) T147_1
      hfix147_1 hinj147_1 hcardT147_1
      (fun i => conj_mem_of_fixedPoints _ _ (T147_1 i) (hfix147_1 i) _)
      ⟨147, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 1 hp) Q2.T147_1_2 Q2.hfix147_1_2 Q2.hinj147_1_2
      Q2.hcardT147_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_1_2 i) (Q2.hfix147_1_2 i) _)
      colCert_147_1_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_1_2 (hp : 2 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp)) T147_1
      hfix147_1 hinj147_1 hcardT147_1
      (fun i => conj_mem_of_fixedPoints _ _ (T147_1 i) (hfix147_1 i) _)
      ⟨147, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 2 hp) Q2.T147_1_2 Q2.hfix147_1_2 Q2.hinj147_1_2
      Q2.hcardT147_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_1_2 i) (Q2.hfix147_1_2 i) _)
      colCert_147_1_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_1_3 (hp : 3 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp)) T147_1
      hfix147_1 hinj147_1 hcardT147_1
      (fun i => conj_mem_of_fixedPoints _ _ (T147_1 i) (hfix147_1 i) _)
      ⟨147, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 3 hp) Q2.T147_1_2 Q2.hfix147_1_2 Q2.hinj147_1_2
      Q2.hcardT147_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_1_2 i) (Q2.hfix147_1_2 i) _)
      colCert_147_1_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_1_4 (hp : 4 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp)) T147_1
      hfix147_1 hinj147_1 hcardT147_1
      (fun i => conj_mem_of_fixedPoints _ _ (T147_1 i) (hfix147_1 i) _)
      ⟨147, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 4 hp) Q2.T147_1_2 Q2.hfix147_1_2 Q2.hinj147_1_2
      Q2.hcardT147_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_1_2 i) (Q2.hfix147_1_2 i) _)
      colCert_147_1_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_2_0 (hp : 0 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp)) T147_2
      hfix147_2 hinj147_2 hcardT147_2
      (fun i => conj_mem_of_fixedPoints _ _ (T147_2 i) (hfix147_2 i) _)
      ⟨147, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 0 hp) Q2.T147_2_2 Q2.hfix147_2_2 Q2.hinj147_2_2
      Q2.hcardT147_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_2_2 i) (Q2.hfix147_2_2 i) _)
      colCert_147_2_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_2_1 (hp : 1 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp)) T147_2
      hfix147_2 hinj147_2 hcardT147_2
      (fun i => conj_mem_of_fixedPoints _ _ (T147_2 i) (hfix147_2 i) _)
      ⟨147, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 1 hp) Q2.T147_2_2 Q2.hfix147_2_2 Q2.hinj147_2_2
      Q2.hcardT147_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_2_2 i) (Q2.hfix147_2_2 i) _)
      colCert_147_2_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_2_2 (hp : 2 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp)) T147_2
      hfix147_2 hinj147_2 hcardT147_2
      (fun i => conj_mem_of_fixedPoints _ _ (T147_2 i) (hfix147_2 i) _)
      ⟨147, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 2 hp) Q2.T147_2_2 Q2.hfix147_2_2 Q2.hinj147_2_2
      Q2.hcardT147_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_2_2 i) (Q2.hfix147_2_2 i) _)
      colCert_147_2_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_2_3 (hp : 3 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp)) T147_2
      hfix147_2 hinj147_2 hcardT147_2
      (fun i => conj_mem_of_fixedPoints _ _ (T147_2 i) (hfix147_2 i) _)
      ⟨147, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 3 hp) Q2.T147_2_2 Q2.hfix147_2_2 Q2.hinj147_2_2
      Q2.hcardT147_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_2_2 i) (Q2.hfix147_2_2 i) _)
      colCert_147_2_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_2_4 (hp : 4 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp)) T147_2
      hfix147_2 hinj147_2 hcardT147_2
      (fun i => conj_mem_of_fixedPoints _ _ (T147_2 i) (hfix147_2 i) _)
      ⟨147, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 4 hp) Q2.T147_2_2 Q2.hfix147_2_2 Q2.hinj147_2_2
      Q2.hcardT147_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_2_2 i) (Q2.hfix147_2_2 i) _)
      colCert_147_2_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_3_0 (hp : 0 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp)) T147_3
      hfix147_3 hinj147_3 hcardT147_3
      (fun i => conj_mem_of_fixedPoints _ _ (T147_3 i) (hfix147_3 i) _)
      ⟨147, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 0 hp) Q2.T147_3_2 Q2.hfix147_3_2 Q2.hinj147_3_2
      Q2.hcardT147_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_3_2 i) (Q2.hfix147_3_2 i) _)
      colCert_147_3_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_3_1 (hp : 1 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp)) T147_3
      hfix147_3 hinj147_3 hcardT147_3
      (fun i => conj_mem_of_fixedPoints _ _ (T147_3 i) (hfix147_3 i) _)
      ⟨147, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 1 hp) Q2.T147_3_2 Q2.hfix147_3_2 Q2.hinj147_3_2
      Q2.hcardT147_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_3_2 i) (Q2.hfix147_3_2 i) _)
      colCert_147_3_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_3_2 (hp : 2 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp)) T147_3
      hfix147_3 hinj147_3 hcardT147_3
      (fun i => conj_mem_of_fixedPoints _ _ (T147_3 i) (hfix147_3 i) _)
      ⟨147, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 2 hp) Q2.T147_3_2 Q2.hfix147_3_2 Q2.hinj147_3_2
      Q2.hcardT147_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_3_2 i) (Q2.hfix147_3_2 i) _)
      colCert_147_3_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_3_3 (hp : 3 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp)) T147_3
      hfix147_3 hinj147_3 hcardT147_3
      (fun i => conj_mem_of_fixedPoints _ _ (T147_3 i) (hfix147_3 i) _)
      ⟨147, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 3 hp) Q2.T147_3_2 Q2.hfix147_3_2 Q2.hinj147_3_2
      Q2.hcardT147_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_3_2 i) (Q2.hfix147_3_2 i) _)
      colCert_147_3_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_3_4 (hp : 4 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp)) T147_3
      hfix147_3 hinj147_3 hcardT147_3
      (fun i => conj_mem_of_fixedPoints _ _ (T147_3 i) (hfix147_3 i) _)
      ⟨147, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 4 hp) Q2.T147_3_2 Q2.hfix147_3_2 Q2.hinj147_3_2
      Q2.hcardT147_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_3_2 i) (Q2.hfix147_3_2 i) _)
      colCert_147_3_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_4_0 (hp : 0 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp)) T147_4
      hfix147_4 hinj147_4 hcardT147_4
      (fun i => conj_mem_of_fixedPoints _ _ (T147_4 i) (hfix147_4 i) _)
      ⟨147, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 0 hp) Q2.T147_4_2 Q2.hfix147_4_2 Q2.hinj147_4_2
      Q2.hcardT147_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_4_2 i) (Q2.hfix147_4_2 i) _)
      colCert_147_4_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_4_1 (hp : 1 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp)) T147_4
      hfix147_4 hinj147_4 hcardT147_4
      (fun i => conj_mem_of_fixedPoints _ _ (T147_4 i) (hfix147_4 i) _)
      ⟨147, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 1 hp) Q2.T147_4_2 Q2.hfix147_4_2 Q2.hinj147_4_2
      Q2.hcardT147_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_4_2 i) (Q2.hfix147_4_2 i) _)
      colCert_147_4_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_4_2 (hp : 2 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp)) T147_4
      hfix147_4 hinj147_4 hcardT147_4
      (fun i => conj_mem_of_fixedPoints _ _ (T147_4 i) (hfix147_4 i) _)
      ⟨147, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 2 hp) Q2.T147_4_2 Q2.hfix147_4_2 Q2.hinj147_4_2
      Q2.hcardT147_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_4_2 i) (Q2.hfix147_4_2 i) _)
      colCert_147_4_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_4_3 (hp : 3 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp)) T147_4
      hfix147_4 hinj147_4 hcardT147_4
      (fun i => conj_mem_of_fixedPoints _ _ (T147_4 i) (hfix147_4 i) _)
      ⟨147, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 3 hp) Q2.T147_4_2 Q2.hfix147_4_2 Q2.hinj147_4_2
      Q2.hcardT147_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_4_2 i) (Q2.hfix147_4_2 i) _)
      colCert_147_4_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_4_4 (hp : 4 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp)) T147_4
      hfix147_4 hinj147_4 hcardT147_4
      (fun i => conj_mem_of_fixedPoints _ _ (T147_4 i) (hfix147_4 i) _)
      ⟨147, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 4 hp) Q2.T147_4_2 Q2.hfix147_4_2 Q2.hinj147_4_2
      Q2.hcardT147_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_4_2 i) (Q2.hfix147_4_2 i) _)
      colCert_147_4_4.hD ?_).symm
  rw [alnId_147 j hj]


end LeanDring.P5Presentation
