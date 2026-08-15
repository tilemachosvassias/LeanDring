/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C006
import LeanDring.P5.Data.ColRestCheap.C038
import LeanDring.P5.Data.ColRestCheap.C039
import LeanDring.P5.Data.ColRestCheap.C040
import LeanDring.P5.Data.ColRestCheap.C041
import LeanDring.P5.Data.ColRestCheap.C042
import LeanDring.P5.Data.ColTau.C001
import LeanDring.P5.Data.EntryK.C028
import LeanDring.P5.Data.EntryK.C029
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C058
import LeanDring.P5.Data.SpeciesDiv.C059
import LeanDring.P5.Certificate.SpeciesTable.Twin2.SpeciesTau.Chunk02

/-! # Stage-5 leaves, chunk 27 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_119_72_5 (hp : 5 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 5 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 5 (transLenTr ⟨72, by decide⟩ 5 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 5 (transLenTr ⟨72, by decide⟩ 5 hp)) T119_72
      hfix119_72 hinj119_72 hcardT119_72
      (fun i => conj_mem_of_fixedPoints _ _ (T119_72 i) (hfix119_72 i) _)
      ⟨119, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 5 hp) Q2.T119_72_2 Q2.hfix119_72_2 Q2.hinj119_72_2
      Q2.hcardT119_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_72_2 i) (Q2.hfix119_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 5 (transLenTr ⟨72, by decide⟩ 5 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T119_72 = colFn colCertDiv_119_72_5.D1 (m := 5) from colCertDiv_119_72_5.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 5 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T119_72_2 = colFn colCertDiv_119_72_5.D2 (m := 5) from colCertDiv_119_72_5.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_72_5_match


theorem leaf_119_72_6 (hp : 6 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 6 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 6 (transLenTr ⟨72, by decide⟩ 6 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 6 (transLenTr ⟨72, by decide⟩ 6 hp)) T119_72
      hfix119_72 hinj119_72 hcardT119_72
      (fun i => conj_mem_of_fixedPoints _ _ (T119_72 i) (hfix119_72 i) _)
      ⟨119, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 6 hp) Q2.T119_72_2 Q2.hfix119_72_2 Q2.hinj119_72_2
      Q2.hcardT119_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_72_2 i) (Q2.hfix119_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 6 (transLenTr ⟨72, by decide⟩ 6 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T119_72 = colFn colCertDiv_119_72_6.D1 (m := 5) from colCertDiv_119_72_6.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 6 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T119_72_2 = colFn colCertDiv_119_72_6.D2 (m := 5) from colCertDiv_119_72_6.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_72_6_match


theorem leaf_119_72_7 (hp : 7 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 7 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 7 (transLenTr ⟨72, by decide⟩ 7 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 7 (transLenTr ⟨72, by decide⟩ 7 hp)) T119_72
      hfix119_72 hinj119_72 hcardT119_72
      (fun i => conj_mem_of_fixedPoints _ _ (T119_72 i) (hfix119_72 i) _)
      ⟨119, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 7 hp) Q2.T119_72_2 Q2.hfix119_72_2 Q2.hinj119_72_2
      Q2.hcardT119_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_72_2 i) (Q2.hfix119_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 7 (transLenTr ⟨72, by decide⟩ 7 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T119_72 = colFn colCertDiv_119_72_7.D1 (m := 5) from colCertDiv_119_72_7.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 7 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T119_72_2 = colFn colCertDiv_119_72_7.D2 (m := 5) from colCertDiv_119_72_7.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_72_7_match


theorem leaf_119_72_8 (hp : 8 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 8 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 8 (transLenTr ⟨72, by decide⟩ 8 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 8 (transLenTr ⟨72, by decide⟩ 8 hp)) T119_72
      hfix119_72 hinj119_72 hcardT119_72
      (fun i => conj_mem_of_fixedPoints _ _ (T119_72 i) (hfix119_72 i) _)
      ⟨119, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 8 hp) Q2.T119_72_2 Q2.hfix119_72_2 Q2.hinj119_72_2
      Q2.hcardT119_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_72_2 i) (Q2.hfix119_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 8 (transLenTr ⟨72, by decide⟩ 8 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T119_72 = colFn colCertDiv_119_72_8.D1 (m := 5) from colCertDiv_119_72_8.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 8 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T119_72_2 = colFn colCertDiv_119_72_8.D2 (m := 5) from colCertDiv_119_72_8.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_72_8_match


theorem leaf_119_72_9 (hp : 9 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 9 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 9 (transLenTr ⟨72, by decide⟩ 9 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 9 (transLenTr ⟨72, by decide⟩ 9 hp)) T119_72
      hfix119_72 hinj119_72 hcardT119_72
      (fun i => conj_mem_of_fixedPoints _ _ (T119_72 i) (hfix119_72 i) _)
      ⟨119, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 9 hp) Q2.T119_72_2 Q2.hfix119_72_2 Q2.hinj119_72_2
      Q2.hcardT119_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_72_2 i) (Q2.hfix119_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 9 (transLenTr ⟨72, by decide⟩ 9 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T119_72 = colFn colCertDiv_119_72_9.D1 (m := 5) from colCertDiv_119_72_9.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 9 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T119_72_2 = colFn colCertDiv_119_72_9.D2 (m := 5) from colCertDiv_119_72_9.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_72_9_match


theorem leaf_119_72_10 (hp : 10 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 10 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 10 (transLenTr ⟨72, by decide⟩ 10 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 10 (transLenTr ⟨72, by decide⟩ 10 hp)) T119_72
      hfix119_72 hinj119_72 hcardT119_72
      (fun i => conj_mem_of_fixedPoints _ _ (T119_72 i) (hfix119_72 i) _)
      ⟨119, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 10 hp) Q2.T119_72_2 Q2.hfix119_72_2 Q2.hinj119_72_2
      Q2.hcardT119_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_72_2 i) (Q2.hfix119_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 10 (transLenTr ⟨72, by decide⟩ 10 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T119_72 = colFn colCertDiv_119_72_10.D1 (m := 5) from colCertDiv_119_72_10.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 10 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T119_72_2 = colFn colCertDiv_119_72_10.D2 (m := 5) from colCertDiv_119_72_10.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_72_10_match


theorem leaf_119_72_11 (hp : 11 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 11 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 11 (transLenTr ⟨72, by decide⟩ 11 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 11 (transLenTr ⟨72, by decide⟩ 11 hp)) T119_72
      hfix119_72 hinj119_72 hcardT119_72
      (fun i => conj_mem_of_fixedPoints _ _ (T119_72 i) (hfix119_72 i) _)
      ⟨119, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 11 hp) Q2.T119_72_2 Q2.hfix119_72_2 Q2.hinj119_72_2
      Q2.hcardT119_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_72_2 i) (Q2.hfix119_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 11 (transLenTr ⟨72, by decide⟩ 11 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T119_72 = colFn colCertDiv_119_72_11.D1 (m := 5) from colCertDiv_119_72_11.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 11 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T119_72_2 = colFn colCertDiv_119_72_11.D2 (m := 5) from colCertDiv_119_72_11.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_72_11_match


theorem leaf_119_72_12 (hp : 12 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 12 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 12 (transLenTr ⟨72, by decide⟩ 12 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 12 (transLenTr ⟨72, by decide⟩ 12 hp)) T119_72
      hfix119_72 hinj119_72 hcardT119_72
      (fun i => conj_mem_of_fixedPoints _ _ (T119_72 i) (hfix119_72 i) _)
      ⟨119, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 12 hp) Q2.T119_72_2 Q2.hfix119_72_2 Q2.hinj119_72_2
      Q2.hcardT119_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_72_2 i) (Q2.hfix119_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 12 (transLenTr ⟨72, by decide⟩ 12 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T119_72 = colFn colCertDiv_119_72_12.D1 (m := 5) from colCertDiv_119_72_12.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 12 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T119_72_2 = colFn colCertDiv_119_72_12.D2 (m := 5) from colCertDiv_119_72_12.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_72_12_match


theorem leaf_119_72_13 (hp : 13 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 13 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 13 (transLenTr ⟨72, by decide⟩ 13 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 13 (transLenTr ⟨72, by decide⟩ 13 hp)) T119_72
      hfix119_72 hinj119_72 hcardT119_72
      (fun i => conj_mem_of_fixedPoints _ _ (T119_72 i) (hfix119_72 i) _)
      ⟨119, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 13 hp) Q2.T119_72_2 Q2.hfix119_72_2 Q2.hinj119_72_2
      Q2.hcardT119_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_72_2 i) (Q2.hfix119_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 13 (transLenTr ⟨72, by decide⟩ 13 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T119_72 = colFn colCertDiv_119_72_13.D1 (m := 5) from colCertDiv_119_72_13.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 13 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T119_72_2 = colFn colCertDiv_119_72_13.D2 (m := 5) from colCertDiv_119_72_13.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_72_13_match


theorem leaf_119_72_14 (hp : 14 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 14 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 14 (transLenTr ⟨72, by decide⟩ 14 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 14 (transLenTr ⟨72, by decide⟩ 14 hp)) T119_72
      hfix119_72 hinj119_72 hcardT119_72
      (fun i => conj_mem_of_fixedPoints _ _ (T119_72 i) (hfix119_72 i) _)
      ⟨119, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 14 hp) Q2.T119_72_2 Q2.hfix119_72_2 Q2.hinj119_72_2
      Q2.hcardT119_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_72_2 i) (Q2.hfix119_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 14 (transLenTr ⟨72, by decide⟩ 14 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T119_72 = colFn colCertDiv_119_72_14.D1 (m := 5) from colCertDiv_119_72_14.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 14 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T119_72_2 = colFn colCertDiv_119_72_14.D2 (m := 5) from colCertDiv_119_72_14.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_72_14_match


theorem leaf_119_72_15 (hp : 15 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 15 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 15 (transLenTr ⟨72, by decide⟩ 15 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 15 (transLenTr ⟨72, by decide⟩ 15 hp)) T119_72
      hfix119_72 hinj119_72 hcardT119_72
      (fun i => conj_mem_of_fixedPoints _ _ (T119_72 i) (hfix119_72 i) _)
      ⟨119, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 15 hp) Q2.T119_72_2 Q2.hfix119_72_2 Q2.hinj119_72_2
      Q2.hcardT119_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_72_2 i) (Q2.hfix119_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 15 (transLenTr ⟨72, by decide⟩ 15 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T119_72 = colFn colCertDiv_119_72_15.D1 (m := 5) from colCertDiv_119_72_15.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 15 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T119_72_2 = colFn colCertDiv_119_72_15.D2 (m := 5) from colCertDiv_119_72_15.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_72_15_match


theorem leaf_119_72_16 (hp : 16 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 16 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 16 (transLenTr ⟨72, by decide⟩ 16 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 16 (transLenTr ⟨72, by decide⟩ 16 hp)) T119_72
      hfix119_72 hinj119_72 hcardT119_72
      (fun i => conj_mem_of_fixedPoints _ _ (T119_72 i) (hfix119_72 i) _)
      ⟨119, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 16 hp) Q2.T119_72_2 Q2.hfix119_72_2 Q2.hinj119_72_2
      Q2.hcardT119_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_72_2 i) (Q2.hfix119_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 16 (transLenTr ⟨72, by decide⟩ 16 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T119_72 = colFn colCertDiv_119_72_16.D1 (m := 5) from colCertDiv_119_72_16.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 16 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T119_72_2 = colFn colCertDiv_119_72_16.D2 (m := 5) from colCertDiv_119_72_16.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_72_16_match


theorem leaf_119_72_17 (hp : 17 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 17 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 17 (transLenTr ⟨72, by decide⟩ 17 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 17 (transLenTr ⟨72, by decide⟩ 17 hp)) T119_72
      hfix119_72 hinj119_72 hcardT119_72
      (fun i => conj_mem_of_fixedPoints _ _ (T119_72 i) (hfix119_72 i) _)
      ⟨119, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 17 hp) Q2.T119_72_2 Q2.hfix119_72_2 Q2.hinj119_72_2
      Q2.hcardT119_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_72_2 i) (Q2.hfix119_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 17 (transLenTr ⟨72, by decide⟩ 17 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T119_72 = colFn colCertDiv_119_72_17.D1 (m := 5) from colCertDiv_119_72_17.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 17 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T119_72_2 = colFn colCertDiv_119_72_17.D2 (m := 5) from colCertDiv_119_72_17.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_72_17_match


theorem leaf_119_72_18 (hp : 18 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 18 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 18 (transLenTr ⟨72, by decide⟩ 18 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 18 (transLenTr ⟨72, by decide⟩ 18 hp)) T119_72
      hfix119_72 hinj119_72 hcardT119_72
      (fun i => conj_mem_of_fixedPoints _ _ (T119_72 i) (hfix119_72 i) _)
      ⟨119, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 18 hp) Q2.T119_72_2 Q2.hfix119_72_2 Q2.hinj119_72_2
      Q2.hcardT119_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_72_2 i) (Q2.hfix119_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 18 (transLenTr ⟨72, by decide⟩ 18 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T119_72 = colFn colCertDiv_119_72_18.D1 (m := 5) from colCertDiv_119_72_18.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 18 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T119_72_2 = colFn colCertDiv_119_72_18.D2 (m := 5) from colCertDiv_119_72_18.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_72_18_match


theorem leaf_119_72_19 (hp : 19 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 19 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 19 (transLenTr ⟨72, by decide⟩ 19 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 19 (transLenTr ⟨72, by decide⟩ 19 hp)) T119_72
      hfix119_72 hinj119_72 hcardT119_72
      (fun i => conj_mem_of_fixedPoints _ _ (T119_72 i) (hfix119_72 i) _)
      ⟨119, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 19 hp) Q2.T119_72_2 Q2.hfix119_72_2 Q2.hinj119_72_2
      Q2.hcardT119_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_72_2 i) (Q2.hfix119_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 19 (transLenTr ⟨72, by decide⟩ 19 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T119_72 = colFn colCertDiv_119_72_19.D1 (m := 5) from colCertDiv_119_72_19.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 19 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T119_72_2 = colFn colCertDiv_119_72_19.D2 (m := 5) from colCertDiv_119_72_19.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_72_19_match


theorem leaf_119_72_20 (hp : 20 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 20 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 20 (transLenTr ⟨72, by decide⟩ 20 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 20 (transLenTr ⟨72, by decide⟩ 20 hp)) T119_72
      hfix119_72 hinj119_72 hcardT119_72
      (fun i => conj_mem_of_fixedPoints _ _ (T119_72 i) (hfix119_72 i) _)
      ⟨119, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 20 hp) Q2.T119_72_2 Q2.hfix119_72_2 Q2.hinj119_72_2
      Q2.hcardT119_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_72_2 i) (Q2.hfix119_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 20 (transLenTr ⟨72, by decide⟩ 20 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T119_72 = colFn colCertDiv_119_72_20.D1 (m := 5) from colCertDiv_119_72_20.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 20 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T119_72_2 = colFn colCertDiv_119_72_20.D2 (m := 5) from colCertDiv_119_72_20.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_72_20_match


theorem leaf_119_72_21 (hp : 21 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 21 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 21 (transLenTr ⟨72, by decide⟩ 21 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 21 (transLenTr ⟨72, by decide⟩ 21 hp)) T119_72
      hfix119_72 hinj119_72 hcardT119_72
      (fun i => conj_mem_of_fixedPoints _ _ (T119_72 i) (hfix119_72 i) _)
      ⟨119, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 21 hp) Q2.T119_72_2 Q2.hfix119_72_2 Q2.hinj119_72_2
      Q2.hcardT119_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_72_2 i) (Q2.hfix119_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 21 (transLenTr ⟨72, by decide⟩ 21 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T119_72 = colFn colCertDiv_119_72_21.D1 (m := 5) from colCertDiv_119_72_21.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 21 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T119_72_2 = colFn colCertDiv_119_72_21.D2 (m := 5) from colCertDiv_119_72_21.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_72_21_match


theorem leaf_119_72_22 (hp : 22 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 22 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 22 (transLenTr ⟨72, by decide⟩ 22 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 22 (transLenTr ⟨72, by decide⟩ 22 hp)) T119_72
      hfix119_72 hinj119_72 hcardT119_72
      (fun i => conj_mem_of_fixedPoints _ _ (T119_72 i) (hfix119_72 i) _)
      ⟨119, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 22 hp) Q2.T119_72_2 Q2.hfix119_72_2 Q2.hinj119_72_2
      Q2.hcardT119_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_72_2 i) (Q2.hfix119_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 22 (transLenTr ⟨72, by decide⟩ 22 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T119_72 = colFn colCertDiv_119_72_22.D1 (m := 5) from colCertDiv_119_72_22.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 22 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T119_72_2 = colFn colCertDiv_119_72_22.D2 (m := 5) from colCertDiv_119_72_22.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_72_22_match


theorem leaf_119_72_23 (hp : 23 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 23 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 23 (transLenTr ⟨72, by decide⟩ 23 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 23 (transLenTr ⟨72, by decide⟩ 23 hp)) T119_72
      hfix119_72 hinj119_72 hcardT119_72
      (fun i => conj_mem_of_fixedPoints _ _ (T119_72 i) (hfix119_72 i) _)
      ⟨119, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 23 hp) Q2.T119_72_2 Q2.hfix119_72_2 Q2.hinj119_72_2
      Q2.hcardT119_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_72_2 i) (Q2.hfix119_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 23 (transLenTr ⟨72, by decide⟩ 23 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T119_72 = colFn colCertDiv_119_72_23.D1 (m := 5) from colCertDiv_119_72_23.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 23 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T119_72_2 = colFn colCertDiv_119_72_23.D2 (m := 5) from colCertDiv_119_72_23.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_72_23_match


theorem leaf_119_72_24 (hp : 24 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 24 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 24 (transLenTr ⟨72, by decide⟩ 24 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 24 (transLenTr ⟨72, by decide⟩ 24 hp)) T119_72
      hfix119_72 hinj119_72 hcardT119_72
      (fun i => conj_mem_of_fixedPoints _ _ (T119_72 i) (hfix119_72 i) _)
      ⟨119, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 24 hp) Q2.T119_72_2 Q2.hfix119_72_2 Q2.hinj119_72_2
      Q2.hcardT119_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_72_2 i) (Q2.hfix119_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 24 (transLenTr ⟨72, by decide⟩ 24 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T119_72 = colFn colCertDiv_119_72_24.D1 (m := 5) from colCertDiv_119_72_24.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 24 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T119_72_2 = colFn colCertDiv_119_72_24.D2 (m := 5) from colCertDiv_119_72_24.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_72_24_match


theorem leaf_119_73_0 (hp : 0 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 0 (transLenTr ⟨73, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 0 (transLenTr ⟨73, by decide⟩ 0 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 0 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_1 (hp : 1 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 1 (transLenTr ⟨73, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 1 (transLenTr ⟨73, by decide⟩ 1 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 1 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_2 (hp : 2 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 2 (transLenTr ⟨73, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 2 (transLenTr ⟨73, by decide⟩ 2 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 2 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_3 (hp : 3 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 3 (transLenTr ⟨73, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 3 (transLenTr ⟨73, by decide⟩ 3 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 3 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_4 (hp : 4 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 4 (transLenTr ⟨73, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 4 (transLenTr ⟨73, by decide⟩ 4 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 4 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_5 (hp : 5 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 5 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 5 (transLenTr ⟨73, by decide⟩ 5 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 5 (transLenTr ⟨73, by decide⟩ 5 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 5 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_5.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_6 (hp : 6 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 6 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 6 (transLenTr ⟨73, by decide⟩ 6 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 6 (transLenTr ⟨73, by decide⟩ 6 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 6 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_6.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_7 (hp : 7 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 7 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 7 (transLenTr ⟨73, by decide⟩ 7 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 7 (transLenTr ⟨73, by decide⟩ 7 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 7 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_7.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_8 (hp : 8 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 8 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 8 (transLenTr ⟨73, by decide⟩ 8 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 8 (transLenTr ⟨73, by decide⟩ 8 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 8 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_8.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_9 (hp : 9 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 9 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 9 (transLenTr ⟨73, by decide⟩ 9 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 9 (transLenTr ⟨73, by decide⟩ 9 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 9 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_9.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_10 (hp : 10 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 10 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 10 (transLenTr ⟨73, by decide⟩ 10 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 10 (transLenTr ⟨73, by decide⟩ 10 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 10 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_10.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_11 (hp : 11 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 11 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 11 (transLenTr ⟨73, by decide⟩ 11 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 11 (transLenTr ⟨73, by decide⟩ 11 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 11 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_11.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_12 (hp : 12 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 12 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 12 (transLenTr ⟨73, by decide⟩ 12 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 12 (transLenTr ⟨73, by decide⟩ 12 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 12 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_12.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_13 (hp : 13 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 13 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 13 (transLenTr ⟨73, by decide⟩ 13 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 13 (transLenTr ⟨73, by decide⟩ 13 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 13 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_13.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_14 (hp : 14 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 14 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 14 (transLenTr ⟨73, by decide⟩ 14 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 14 (transLenTr ⟨73, by decide⟩ 14 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 14 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_14.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_15 (hp : 15 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 15 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 15 (transLenTr ⟨73, by decide⟩ 15 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 15 (transLenTr ⟨73, by decide⟩ 15 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 15 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_15.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_16 (hp : 16 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 16 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 16 (transLenTr ⟨73, by decide⟩ 16 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 16 (transLenTr ⟨73, by decide⟩ 16 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 16 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_16.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_17 (hp : 17 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 17 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 17 (transLenTr ⟨73, by decide⟩ 17 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 17 (transLenTr ⟨73, by decide⟩ 17 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 17 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_17.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_18 (hp : 18 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 18 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 18 (transLenTr ⟨73, by decide⟩ 18 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 18 (transLenTr ⟨73, by decide⟩ 18 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 18 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_18.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_19 (hp : 19 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 19 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 19 (transLenTr ⟨73, by decide⟩ 19 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 19 (transLenTr ⟨73, by decide⟩ 19 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 19 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_19.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_20 (hp : 20 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 20 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 20 (transLenTr ⟨73, by decide⟩ 20 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 20 (transLenTr ⟨73, by decide⟩ 20 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 20 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_20.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_21 (hp : 21 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 21 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 21 (transLenTr ⟨73, by decide⟩ 21 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 21 (transLenTr ⟨73, by decide⟩ 21 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 21 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_21.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_22 (hp : 22 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 22 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 22 (transLenTr ⟨73, by decide⟩ 22 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 22 (transLenTr ⟨73, by decide⟩ 22 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 22 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_22.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_23 (hp : 23 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 23 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 23 (transLenTr ⟨73, by decide⟩ 23 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 23 (transLenTr ⟨73, by decide⟩ 23 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 23 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_23.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_24 (hp : 24 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 24 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 24 (transLenTr ⟨73, by decide⟩ 24 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 24 (transLenTr ⟨73, by decide⟩ 24 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 24 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_24.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_25 (hp : 25 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 25 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 25 (transLenTr ⟨73, by decide⟩ 25 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 25 (transLenTr ⟨73, by decide⟩ 25 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 25 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_25.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_30 (hp : 30 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 30 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 30 (transLenTr ⟨73, by decide⟩ 30 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 30 (transLenTr ⟨73, by decide⟩ 30 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 30 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_30.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_35 (hp : 35 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 35 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 35 (transLenTr ⟨73, by decide⟩ 35 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 35 (transLenTr ⟨73, by decide⟩ 35 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 35 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_35.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_40 (hp : 40 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 40 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 40 (transLenTr ⟨73, by decide⟩ 40 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 40 (transLenTr ⟨73, by decide⟩ 40 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 40 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_40.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_45 (hp : 45 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 45 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 45 (transLenTr ⟨73, by decide⟩ 45 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 45 (transLenTr ⟨73, by decide⟩ 45 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 45 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_45.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_50 (hp : 50 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 50 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 50 (transLenTr ⟨73, by decide⟩ 50 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 50 (transLenTr ⟨73, by decide⟩ 50 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 50 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_50.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_55 (hp : 55 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 55 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 55 (transLenTr ⟨73, by decide⟩ 55 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 55 (transLenTr ⟨73, by decide⟩ 55 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 55 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_55.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_60 (hp : 60 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 60 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 60 (transLenTr ⟨73, by decide⟩ 60 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 60 (transLenTr ⟨73, by decide⟩ 60 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 60 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_60.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_65 (hp : 65 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 65 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 65 (transLenTr ⟨73, by decide⟩ 65 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 65 (transLenTr ⟨73, by decide⟩ 65 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 65 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_65.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_70 (hp : 70 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 70 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 70 (transLenTr ⟨73, by decide⟩ 70 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 70 (transLenTr ⟨73, by decide⟩ 70 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 70 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_70.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_75 (hp : 75 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 75 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 75 (transLenTr ⟨73, by decide⟩ 75 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 75 (transLenTr ⟨73, by decide⟩ 75 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 75 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_75.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_80 (hp : 80 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 80 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 80 (transLenTr ⟨73, by decide⟩ 80 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 80 (transLenTr ⟨73, by decide⟩ 80 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 80 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_80.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_85 (hp : 85 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 85 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 85 (transLenTr ⟨73, by decide⟩ 85 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 85 (transLenTr ⟨73, by decide⟩ 85 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 85 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_85.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_90 (hp : 90 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 90 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 90 (transLenTr ⟨73, by decide⟩ 90 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 90 (transLenTr ⟨73, by decide⟩ 90 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 90 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_90.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_95 (hp : 95 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 95 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 95 (transLenTr ⟨73, by decide⟩ 95 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 95 (transLenTr ⟨73, by decide⟩ 95 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 95 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_95.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_100 (hp : 100 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 100 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 100 (transLenTr ⟨73, by decide⟩ 100 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 100 (transLenTr ⟨73, by decide⟩ 100 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 100 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_100.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_105 (hp : 105 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 105 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 105 (transLenTr ⟨73, by decide⟩ 105 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 105 (transLenTr ⟨73, by decide⟩ 105 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 105 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_105.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_110 (hp : 110 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 110 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 110 (transLenTr ⟨73, by decide⟩ 110 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 110 (transLenTr ⟨73, by decide⟩ 110 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 110 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_110.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_115 (hp : 115 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 115 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 115 (transLenTr ⟨73, by decide⟩ 115 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 115 (transLenTr ⟨73, by decide⟩ 115 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 115 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_115.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_73_120 (hp : 120 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 120 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 120 (transLenTr ⟨73, by decide⟩ 120 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 120 (transLenTr ⟨73, by decide⟩ 120 hp)) T119_73
      hfix119_73 hinj119_73 hcardT119_73
      (fun i => conj_mem_of_fixedPoints _ _ (T119_73 i) (hfix119_73 i) _)
      ⟨119, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 120 hp) Q2.T119_73_2 Q2.hfix119_73_2 Q2.hinj119_73_2
      Q2.hcardT119_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_73_2 i) (Q2.hfix119_73_2 i) _)
      colCert_119_73_120.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_74_0 (hp : 0 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 0 (transLenTr ⟨74, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 0 (transLenTr ⟨74, by decide⟩ 0 hp)) T119_74
      hfix119_74 hinj119_74 hcardT119_74
      (fun i => conj_mem_of_fixedPoints _ _ (T119_74 i) (hfix119_74 i) _)
      ⟨119, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 0 hp) Q2.T119_74_2 Q2.hfix119_74_2 Q2.hinj119_74_2
      Q2.hcardT119_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_74_2 i) (Q2.hfix119_74_2 i) _)
      colCert_119_74_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_74_1 (hp : 1 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 1 (transLenTr ⟨74, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 1 (transLenTr ⟨74, by decide⟩ 1 hp)) T119_74
      hfix119_74 hinj119_74 hcardT119_74
      (fun i => conj_mem_of_fixedPoints _ _ (T119_74 i) (hfix119_74 i) _)
      ⟨119, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 1 hp) Q2.T119_74_2 Q2.hfix119_74_2 Q2.hinj119_74_2
      Q2.hcardT119_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_74_2 i) (Q2.hfix119_74_2 i) _)
      colCert_119_74_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_74_2 (hp : 2 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 2 (transLenTr ⟨74, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 2 (transLenTr ⟨74, by decide⟩ 2 hp)) T119_74
      hfix119_74 hinj119_74 hcardT119_74
      (fun i => conj_mem_of_fixedPoints _ _ (T119_74 i) (hfix119_74 i) _)
      ⟨119, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 2 hp) Q2.T119_74_2 Q2.hfix119_74_2 Q2.hinj119_74_2
      Q2.hcardT119_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_74_2 i) (Q2.hfix119_74_2 i) _)
      colCert_119_74_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_74_3 (hp : 3 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 3 (transLenTr ⟨74, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 3 (transLenTr ⟨74, by decide⟩ 3 hp)) T119_74
      hfix119_74 hinj119_74 hcardT119_74
      (fun i => conj_mem_of_fixedPoints _ _ (T119_74 i) (hfix119_74 i) _)
      ⟨119, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 3 hp) Q2.T119_74_2 Q2.hfix119_74_2 Q2.hinj119_74_2
      Q2.hcardT119_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_74_2 i) (Q2.hfix119_74_2 i) _)
      colCert_119_74_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_74_4 (hp : 4 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 4 (transLenTr ⟨74, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 4 (transLenTr ⟨74, by decide⟩ 4 hp)) T119_74
      hfix119_74 hinj119_74 hcardT119_74
      (fun i => conj_mem_of_fixedPoints _ _ (T119_74 i) (hfix119_74 i) _)
      ⟨119, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 4 hp) Q2.T119_74_2 Q2.hfix119_74_2 Q2.hinj119_74_2
      Q2.hcardT119_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_74_2 i) (Q2.hfix119_74_2 i) _)
      colCert_119_74_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_74_5 (hp : 5 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 5 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 5 (transLenTr ⟨74, by decide⟩ 5 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 5 (transLenTr ⟨74, by decide⟩ 5 hp)) T119_74
      hfix119_74 hinj119_74 hcardT119_74
      (fun i => conj_mem_of_fixedPoints _ _ (T119_74 i) (hfix119_74 i) _)
      ⟨119, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 5 hp) Q2.T119_74_2 Q2.hfix119_74_2 Q2.hinj119_74_2
      Q2.hcardT119_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_74_2 i) (Q2.hfix119_74_2 i) _)
      colCert_119_74_5.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_74_6 (hp : 6 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 6 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 6 (transLenTr ⟨74, by decide⟩ 6 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 6 (transLenTr ⟨74, by decide⟩ 6 hp)) T119_74
      hfix119_74 hinj119_74 hcardT119_74
      (fun i => conj_mem_of_fixedPoints _ _ (T119_74 i) (hfix119_74 i) _)
      ⟨119, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 6 hp) Q2.T119_74_2 Q2.hfix119_74_2 Q2.hinj119_74_2
      Q2.hcardT119_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_74_2 i) (Q2.hfix119_74_2 i) _)
      colCert_119_74_6.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_74_7 (hp : 7 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 7 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 7 (transLenTr ⟨74, by decide⟩ 7 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 7 (transLenTr ⟨74, by decide⟩ 7 hp)) T119_74
      hfix119_74 hinj119_74 hcardT119_74
      (fun i => conj_mem_of_fixedPoints _ _ (T119_74 i) (hfix119_74 i) _)
      ⟨119, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 7 hp) Q2.T119_74_2 Q2.hfix119_74_2 Q2.hinj119_74_2
      Q2.hcardT119_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_74_2 i) (Q2.hfix119_74_2 i) _)
      colCert_119_74_7.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_74_8 (hp : 8 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 8 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 8 (transLenTr ⟨74, by decide⟩ 8 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 8 (transLenTr ⟨74, by decide⟩ 8 hp)) T119_74
      hfix119_74 hinj119_74 hcardT119_74
      (fun i => conj_mem_of_fixedPoints _ _ (T119_74 i) (hfix119_74 i) _)
      ⟨119, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 8 hp) Q2.T119_74_2 Q2.hfix119_74_2 Q2.hinj119_74_2
      Q2.hcardT119_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_74_2 i) (Q2.hfix119_74_2 i) _)
      colCert_119_74_8.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_74_9 (hp : 9 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 9 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 9 (transLenTr ⟨74, by decide⟩ 9 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 9 (transLenTr ⟨74, by decide⟩ 9 hp)) T119_74
      hfix119_74 hinj119_74 hcardT119_74
      (fun i => conj_mem_of_fixedPoints _ _ (T119_74 i) (hfix119_74 i) _)
      ⟨119, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 9 hp) Q2.T119_74_2 Q2.hfix119_74_2 Q2.hinj119_74_2
      Q2.hcardT119_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_74_2 i) (Q2.hfix119_74_2 i) _)
      colCert_119_74_9.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_74_10 (hp : 10 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 10 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 10 (transLenTr ⟨74, by decide⟩ 10 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 10 (transLenTr ⟨74, by decide⟩ 10 hp)) T119_74
      hfix119_74 hinj119_74 hcardT119_74
      (fun i => conj_mem_of_fixedPoints _ _ (T119_74 i) (hfix119_74 i) _)
      ⟨119, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 10 hp) Q2.T119_74_2 Q2.hfix119_74_2 Q2.hinj119_74_2
      Q2.hcardT119_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_74_2 i) (Q2.hfix119_74_2 i) _)
      colCert_119_74_10.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_74_11 (hp : 11 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 11 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 11 (transLenTr ⟨74, by decide⟩ 11 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 11 (transLenTr ⟨74, by decide⟩ 11 hp)) T119_74
      hfix119_74 hinj119_74 hcardT119_74
      (fun i => conj_mem_of_fixedPoints _ _ (T119_74 i) (hfix119_74 i) _)
      ⟨119, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 11 hp) Q2.T119_74_2 Q2.hfix119_74_2 Q2.hinj119_74_2
      Q2.hcardT119_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_74_2 i) (Q2.hfix119_74_2 i) _)
      colCert_119_74_11.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_74_12 (hp : 12 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 12 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 12 (transLenTr ⟨74, by decide⟩ 12 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 12 (transLenTr ⟨74, by decide⟩ 12 hp)) T119_74
      hfix119_74 hinj119_74 hcardT119_74
      (fun i => conj_mem_of_fixedPoints _ _ (T119_74 i) (hfix119_74 i) _)
      ⟨119, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 12 hp) Q2.T119_74_2 Q2.hfix119_74_2 Q2.hinj119_74_2
      Q2.hcardT119_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_74_2 i) (Q2.hfix119_74_2 i) _)
      colCert_119_74_12.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_74_13 (hp : 13 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 13 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 13 (transLenTr ⟨74, by decide⟩ 13 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 13 (transLenTr ⟨74, by decide⟩ 13 hp)) T119_74
      hfix119_74 hinj119_74 hcardT119_74
      (fun i => conj_mem_of_fixedPoints _ _ (T119_74 i) (hfix119_74 i) _)
      ⟨119, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 13 hp) Q2.T119_74_2 Q2.hfix119_74_2 Q2.hinj119_74_2
      Q2.hcardT119_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_74_2 i) (Q2.hfix119_74_2 i) _)
      colCert_119_74_13.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_74_14 (hp : 14 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 14 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 14 (transLenTr ⟨74, by decide⟩ 14 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 14 (transLenTr ⟨74, by decide⟩ 14 hp)) T119_74
      hfix119_74 hinj119_74 hcardT119_74
      (fun i => conj_mem_of_fixedPoints _ _ (T119_74 i) (hfix119_74 i) _)
      ⟨119, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 14 hp) Q2.T119_74_2 Q2.hfix119_74_2 Q2.hinj119_74_2
      Q2.hcardT119_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_74_2 i) (Q2.hfix119_74_2 i) _)
      colCert_119_74_14.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_74_15 (hp : 15 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 15 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 15 (transLenTr ⟨74, by decide⟩ 15 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 15 (transLenTr ⟨74, by decide⟩ 15 hp)) T119_74
      hfix119_74 hinj119_74 hcardT119_74
      (fun i => conj_mem_of_fixedPoints _ _ (T119_74 i) (hfix119_74 i) _)
      ⟨119, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 15 hp) Q2.T119_74_2 Q2.hfix119_74_2 Q2.hinj119_74_2
      Q2.hcardT119_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_74_2 i) (Q2.hfix119_74_2 i) _)
      colCert_119_74_15.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_74_16 (hp : 16 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 16 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 16 (transLenTr ⟨74, by decide⟩ 16 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 16 (transLenTr ⟨74, by decide⟩ 16 hp)) T119_74
      hfix119_74 hinj119_74 hcardT119_74
      (fun i => conj_mem_of_fixedPoints _ _ (T119_74 i) (hfix119_74 i) _)
      ⟨119, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 16 hp) Q2.T119_74_2 Q2.hfix119_74_2 Q2.hinj119_74_2
      Q2.hcardT119_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_74_2 i) (Q2.hfix119_74_2 i) _)
      colCert_119_74_16.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_74_17 (hp : 17 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 17 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 17 (transLenTr ⟨74, by decide⟩ 17 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 17 (transLenTr ⟨74, by decide⟩ 17 hp)) T119_74
      hfix119_74 hinj119_74 hcardT119_74
      (fun i => conj_mem_of_fixedPoints _ _ (T119_74 i) (hfix119_74 i) _)
      ⟨119, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 17 hp) Q2.T119_74_2 Q2.hfix119_74_2 Q2.hinj119_74_2
      Q2.hcardT119_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_74_2 i) (Q2.hfix119_74_2 i) _)
      colCert_119_74_17.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_74_18 (hp : 18 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 18 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 18 (transLenTr ⟨74, by decide⟩ 18 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 18 (transLenTr ⟨74, by decide⟩ 18 hp)) T119_74
      hfix119_74 hinj119_74 hcardT119_74
      (fun i => conj_mem_of_fixedPoints _ _ (T119_74 i) (hfix119_74 i) _)
      ⟨119, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 18 hp) Q2.T119_74_2 Q2.hfix119_74_2 Q2.hinj119_74_2
      Q2.hcardT119_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_74_2 i) (Q2.hfix119_74_2 i) _)
      colCert_119_74_18.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_74_19 (hp : 19 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 19 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 19 (transLenTr ⟨74, by decide⟩ 19 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 19 (transLenTr ⟨74, by decide⟩ 19 hp)) T119_74
      hfix119_74 hinj119_74 hcardT119_74
      (fun i => conj_mem_of_fixedPoints _ _ (T119_74 i) (hfix119_74 i) _)
      ⟨119, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 19 hp) Q2.T119_74_2 Q2.hfix119_74_2 Q2.hinj119_74_2
      Q2.hcardT119_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_74_2 i) (Q2.hfix119_74_2 i) _)
      colCert_119_74_19.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_74_20 (hp : 20 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 20 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 20 (transLenTr ⟨74, by decide⟩ 20 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 20 (transLenTr ⟨74, by decide⟩ 20 hp)) T119_74
      hfix119_74 hinj119_74 hcardT119_74
      (fun i => conj_mem_of_fixedPoints _ _ (T119_74 i) (hfix119_74 i) _)
      ⟨119, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 20 hp) Q2.T119_74_2 Q2.hfix119_74_2 Q2.hinj119_74_2
      Q2.hcardT119_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_74_2 i) (Q2.hfix119_74_2 i) _)
      colCert_119_74_20.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_74_21 (hp : 21 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 21 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 21 (transLenTr ⟨74, by decide⟩ 21 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 21 (transLenTr ⟨74, by decide⟩ 21 hp)) T119_74
      hfix119_74 hinj119_74 hcardT119_74
      (fun i => conj_mem_of_fixedPoints _ _ (T119_74 i) (hfix119_74 i) _)
      ⟨119, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 21 hp) Q2.T119_74_2 Q2.hfix119_74_2 Q2.hinj119_74_2
      Q2.hcardT119_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_74_2 i) (Q2.hfix119_74_2 i) _)
      colCert_119_74_21.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_74_22 (hp : 22 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 22 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 22 (transLenTr ⟨74, by decide⟩ 22 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 22 (transLenTr ⟨74, by decide⟩ 22 hp)) T119_74
      hfix119_74 hinj119_74 hcardT119_74
      (fun i => conj_mem_of_fixedPoints _ _ (T119_74 i) (hfix119_74 i) _)
      ⟨119, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 22 hp) Q2.T119_74_2 Q2.hfix119_74_2 Q2.hinj119_74_2
      Q2.hcardT119_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_74_2 i) (Q2.hfix119_74_2 i) _)
      colCert_119_74_22.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_74_23 (hp : 23 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 23 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 23 (transLenTr ⟨74, by decide⟩ 23 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 23 (transLenTr ⟨74, by decide⟩ 23 hp)) T119_74
      hfix119_74 hinj119_74 hcardT119_74
      (fun i => conj_mem_of_fixedPoints _ _ (T119_74 i) (hfix119_74 i) _)
      ⟨119, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 23 hp) Q2.T119_74_2 Q2.hfix119_74_2 Q2.hinj119_74_2
      Q2.hcardT119_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_74_2 i) (Q2.hfix119_74_2 i) _)
      colCert_119_74_23.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_74_24 (hp : 24 < (Q2.transData.getD 74 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ 24 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ 24 (transLenTr ⟨74, by decide⟩ 24 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨74, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨74, by decide⟩ 24 (transLenTr ⟨74, by decide⟩ 24 hp)) T119_74
      hfix119_74 hinj119_74 hcardT119_74
      (fun i => conj_mem_of_fixedPoints _ _ (T119_74 i) (hfix119_74 i) _)
      ⟨119, by decide⟩ ⟨74, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨74, by decide⟩ 24 hp) Q2.T119_74_2 Q2.hfix119_74_2 Q2.hinj119_74_2
      Q2.hcardT119_74_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_74_2 i) (Q2.hfix119_74_2 i) _)
      colCert_119_74_24.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_0 (hp : 0 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 0 (transLenTr ⟨80, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 0 (transLenTr ⟨80, by decide⟩ 0 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 0 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_1 (hp : 1 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 1 (transLenTr ⟨80, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 1 (transLenTr ⟨80, by decide⟩ 1 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 1 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_2 (hp : 2 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 2 (transLenTr ⟨80, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 2 (transLenTr ⟨80, by decide⟩ 2 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 2 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_3 (hp : 3 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 3 (transLenTr ⟨80, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 3 (transLenTr ⟨80, by decide⟩ 3 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 3 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_4 (hp : 4 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 4 (transLenTr ⟨80, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 4 (transLenTr ⟨80, by decide⟩ 4 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 4 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_5 (hp : 5 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 5 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 5 (transLenTr ⟨80, by decide⟩ 5 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 5 (transLenTr ⟨80, by decide⟩ 5 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 5 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_5.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_10 (hp : 10 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 10 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 10 (transLenTr ⟨80, by decide⟩ 10 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 10 (transLenTr ⟨80, by decide⟩ 10 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 10 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_10.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_15 (hp : 15 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 15 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 15 (transLenTr ⟨80, by decide⟩ 15 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 15 (transLenTr ⟨80, by decide⟩ 15 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 15 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_15.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_20 (hp : 20 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 20 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 20 (transLenTr ⟨80, by decide⟩ 20 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 20 (transLenTr ⟨80, by decide⟩ 20 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 20 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_20.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_25 (hp : 25 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 25 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 25 (transLenTr ⟨80, by decide⟩ 25 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 25 (transLenTr ⟨80, by decide⟩ 25 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 25 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_25.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_30 (hp : 30 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 30 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 30 (transLenTr ⟨80, by decide⟩ 30 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 30 (transLenTr ⟨80, by decide⟩ 30 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 30 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_30.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_35 (hp : 35 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 35 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 35 (transLenTr ⟨80, by decide⟩ 35 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 35 (transLenTr ⟨80, by decide⟩ 35 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 35 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_35.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_40 (hp : 40 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 40 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 40 (transLenTr ⟨80, by decide⟩ 40 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 40 (transLenTr ⟨80, by decide⟩ 40 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 40 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_40.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_45 (hp : 45 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 45 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 45 (transLenTr ⟨80, by decide⟩ 45 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 45 (transLenTr ⟨80, by decide⟩ 45 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 45 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_45.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_50 (hp : 50 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 50 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 50 (transLenTr ⟨80, by decide⟩ 50 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 50 (transLenTr ⟨80, by decide⟩ 50 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 50 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_50.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_55 (hp : 55 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 55 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 55 (transLenTr ⟨80, by decide⟩ 55 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 55 (transLenTr ⟨80, by decide⟩ 55 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 55 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_55.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_60 (hp : 60 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 60 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 60 (transLenTr ⟨80, by decide⟩ 60 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 60 (transLenTr ⟨80, by decide⟩ 60 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 60 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_60.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_65 (hp : 65 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 65 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 65 (transLenTr ⟨80, by decide⟩ 65 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 65 (transLenTr ⟨80, by decide⟩ 65 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 65 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_65.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_70 (hp : 70 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 70 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 70 (transLenTr ⟨80, by decide⟩ 70 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 70 (transLenTr ⟨80, by decide⟩ 70 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 70 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_70.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_75 (hp : 75 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 75 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 75 (transLenTr ⟨80, by decide⟩ 75 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 75 (transLenTr ⟨80, by decide⟩ 75 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 75 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_75.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_80 (hp : 80 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 80 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 80 (transLenTr ⟨80, by decide⟩ 80 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 80 (transLenTr ⟨80, by decide⟩ 80 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 80 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_80.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_85 (hp : 85 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 85 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 85 (transLenTr ⟨80, by decide⟩ 85 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 85 (transLenTr ⟨80, by decide⟩ 85 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 85 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_85.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_90 (hp : 90 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 90 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 90 (transLenTr ⟨80, by decide⟩ 90 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 90 (transLenTr ⟨80, by decide⟩ 90 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 90 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_90.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_95 (hp : 95 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 95 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 95 (transLenTr ⟨80, by decide⟩ 95 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 95 (transLenTr ⟨80, by decide⟩ 95 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 95 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_95.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_100 (hp : 100 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 100 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 100 (transLenTr ⟨80, by decide⟩ 100 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 100 (transLenTr ⟨80, by decide⟩ 100 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 100 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_100.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_105 (hp : 105 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 105 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 105 (transLenTr ⟨80, by decide⟩ 105 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 105 (transLenTr ⟨80, by decide⟩ 105 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 105 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_105.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_110 (hp : 110 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 110 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 110 (transLenTr ⟨80, by decide⟩ 110 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 110 (transLenTr ⟨80, by decide⟩ 110 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 110 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_110.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_115 (hp : 115 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 115 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 115 (transLenTr ⟨80, by decide⟩ 115 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 115 (transLenTr ⟨80, by decide⟩ 115 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 115 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_115.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_80_120 (hp : 120 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 120 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 120 (transLenTr ⟨80, by decide⟩ 120 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 120 (transLenTr ⟨80, by decide⟩ 120 hp)) T119_80
      hfix119_80 hinj119_80 hcardT119_80
      (fun i => conj_mem_of_fixedPoints _ _ (T119_80 i) (hfix119_80 i) _)
      ⟨119, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 120 hp) Q2.T119_80_2 Q2.hfix119_80_2 Q2.hinj119_80_2
      Q2.hcardT119_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_80_2 i) (Q2.hfix119_80_2 i) _)
      colCert_119_80_120.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_93_0 (hp : 0 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 0 (transLenTr ⟨93, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 0 (transLenTr ⟨93, by decide⟩ 0 hp)) T119_93
      hfix119_93 hinj119_93 hcardT119_93
      (fun i => conj_mem_of_fixedPoints _ _ (T119_93 i) (hfix119_93 i) _)
      ⟨119, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 0 hp) Q2.T119_93_2 Q2.hfix119_93_2 Q2.hinj119_93_2
      Q2.hcardT119_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_93_2 i) (Q2.hfix119_93_2 i) _)
      colCert_119_93_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_93_1 (hp : 1 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 1 (transLenTr ⟨93, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 1 (transLenTr ⟨93, by decide⟩ 1 hp)) T119_93
      hfix119_93 hinj119_93 hcardT119_93
      (fun i => conj_mem_of_fixedPoints _ _ (T119_93 i) (hfix119_93 i) _)
      ⟨119, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 1 hp) Q2.T119_93_2 Q2.hfix119_93_2 Q2.hinj119_93_2
      Q2.hcardT119_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_93_2 i) (Q2.hfix119_93_2 i) _)
      colCert_119_93_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_93_2 (hp : 2 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 2 (transLenTr ⟨93, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 2 (transLenTr ⟨93, by decide⟩ 2 hp)) T119_93
      hfix119_93 hinj119_93 hcardT119_93
      (fun i => conj_mem_of_fixedPoints _ _ (T119_93 i) (hfix119_93 i) _)
      ⟨119, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 2 hp) Q2.T119_93_2 Q2.hfix119_93_2 Q2.hinj119_93_2
      Q2.hcardT119_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_93_2 i) (Q2.hfix119_93_2 i) _)
      colCert_119_93_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_93_3 (hp : 3 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 3 (transLenTr ⟨93, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 3 (transLenTr ⟨93, by decide⟩ 3 hp)) T119_93
      hfix119_93 hinj119_93 hcardT119_93
      (fun i => conj_mem_of_fixedPoints _ _ (T119_93 i) (hfix119_93 i) _)
      ⟨119, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 3 hp) Q2.T119_93_2 Q2.hfix119_93_2 Q2.hinj119_93_2
      Q2.hcardT119_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_93_2 i) (Q2.hfix119_93_2 i) _)
      colCert_119_93_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_93_4 (hp : 4 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 4 (transLenTr ⟨93, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 4 (transLenTr ⟨93, by decide⟩ 4 hp)) T119_93
      hfix119_93 hinj119_93 hcardT119_93
      (fun i => conj_mem_of_fixedPoints _ _ (T119_93 i) (hfix119_93 i) _)
      ⟨119, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 4 hp) Q2.T119_93_2 Q2.hfix119_93_2 Q2.hinj119_93_2
      Q2.hcardT119_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_93_2 i) (Q2.hfix119_93_2 i) _)
      colCert_119_93_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_93_5 (hp : 5 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 5 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 5 (transLenTr ⟨93, by decide⟩ 5 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 5 (transLenTr ⟨93, by decide⟩ 5 hp)) T119_93
      hfix119_93 hinj119_93 hcardT119_93
      (fun i => conj_mem_of_fixedPoints _ _ (T119_93 i) (hfix119_93 i) _)
      ⟨119, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 5 hp) Q2.T119_93_2 Q2.hfix119_93_2 Q2.hinj119_93_2
      Q2.hcardT119_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_93_2 i) (Q2.hfix119_93_2 i) _)
      colCert_119_93_5.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_93_10 (hp : 10 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 10 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 10 (transLenTr ⟨93, by decide⟩ 10 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 10 (transLenTr ⟨93, by decide⟩ 10 hp)) T119_93
      hfix119_93 hinj119_93 hcardT119_93
      (fun i => conj_mem_of_fixedPoints _ _ (T119_93 i) (hfix119_93 i) _)
      ⟨119, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 10 hp) Q2.T119_93_2 Q2.hfix119_93_2 Q2.hinj119_93_2
      Q2.hcardT119_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_93_2 i) (Q2.hfix119_93_2 i) _)
      colCert_119_93_10.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_93_15 (hp : 15 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 15 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 15 (transLenTr ⟨93, by decide⟩ 15 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 15 (transLenTr ⟨93, by decide⟩ 15 hp)) T119_93
      hfix119_93 hinj119_93 hcardT119_93
      (fun i => conj_mem_of_fixedPoints _ _ (T119_93 i) (hfix119_93 i) _)
      ⟨119, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 15 hp) Q2.T119_93_2 Q2.hfix119_93_2 Q2.hinj119_93_2
      Q2.hcardT119_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_93_2 i) (Q2.hfix119_93_2 i) _)
      colCert_119_93_15.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_93_20 (hp : 20 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 20 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 20 (transLenTr ⟨93, by decide⟩ 20 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 20 (transLenTr ⟨93, by decide⟩ 20 hp)) T119_93
      hfix119_93 hinj119_93 hcardT119_93
      (fun i => conj_mem_of_fixedPoints _ _ (T119_93 i) (hfix119_93 i) _)
      ⟨119, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 20 hp) Q2.T119_93_2 Q2.hfix119_93_2 Q2.hinj119_93_2
      Q2.hcardT119_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_93_2 i) (Q2.hfix119_93_2 i) _)
      colCert_119_93_20.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_98_0 (hp : 0 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 0 (transLenTr ⟨98, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 0 (transLenTr ⟨98, by decide⟩ 0 hp)) T119_98
      hfix119_98 hinj119_98 hcardT119_98
      (fun i => conj_mem_of_fixedPoints _ _ (T119_98 i) (hfix119_98 i) _)
      ⟨119, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 0 hp) Q2.T119_98_2 Q2.hfix119_98_2 Q2.hinj119_98_2
      Q2.hcardT119_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_98_2 i) (Q2.hfix119_98_2 i) _)
      colCert_119_98_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_98_1 (hp : 1 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 1 (transLenTr ⟨98, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 1 (transLenTr ⟨98, by decide⟩ 1 hp)) T119_98
      hfix119_98 hinj119_98 hcardT119_98
      (fun i => conj_mem_of_fixedPoints _ _ (T119_98 i) (hfix119_98 i) _)
      ⟨119, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 1 hp) Q2.T119_98_2 Q2.hfix119_98_2 Q2.hinj119_98_2
      Q2.hcardT119_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_98_2 i) (Q2.hfix119_98_2 i) _)
      colCert_119_98_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_98_2 (hp : 2 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 2 (transLenTr ⟨98, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 2 (transLenTr ⟨98, by decide⟩ 2 hp)) T119_98
      hfix119_98 hinj119_98 hcardT119_98
      (fun i => conj_mem_of_fixedPoints _ _ (T119_98 i) (hfix119_98 i) _)
      ⟨119, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 2 hp) Q2.T119_98_2 Q2.hfix119_98_2 Q2.hinj119_98_2
      Q2.hcardT119_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_98_2 i) (Q2.hfix119_98_2 i) _)
      colCert_119_98_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_98_3 (hp : 3 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 3 (transLenTr ⟨98, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 3 (transLenTr ⟨98, by decide⟩ 3 hp)) T119_98
      hfix119_98 hinj119_98 hcardT119_98
      (fun i => conj_mem_of_fixedPoints _ _ (T119_98 i) (hfix119_98 i) _)
      ⟨119, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 3 hp) Q2.T119_98_2 Q2.hfix119_98_2 Q2.hinj119_98_2
      Q2.hcardT119_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_98_2 i) (Q2.hfix119_98_2 i) _)
      colCert_119_98_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_98_4 (hp : 4 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 4 (transLenTr ⟨98, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 4 (transLenTr ⟨98, by decide⟩ 4 hp)) T119_98
      hfix119_98 hinj119_98 hcardT119_98
      (fun i => conj_mem_of_fixedPoints _ _ (T119_98 i) (hfix119_98 i) _)
      ⟨119, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 4 hp) Q2.T119_98_2 Q2.hfix119_98_2 Q2.hinj119_98_2
      Q2.hcardT119_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_98_2 i) (Q2.hfix119_98_2 i) _)
      colCert_119_98_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_98_5 (hp : 5 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 5 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 5 (transLenTr ⟨98, by decide⟩ 5 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 5 (transLenTr ⟨98, by decide⟩ 5 hp)) T119_98
      hfix119_98 hinj119_98 hcardT119_98
      (fun i => conj_mem_of_fixedPoints _ _ (T119_98 i) (hfix119_98 i) _)
      ⟨119, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 5 hp) Q2.T119_98_2 Q2.hfix119_98_2 Q2.hinj119_98_2
      Q2.hcardT119_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_98_2 i) (Q2.hfix119_98_2 i) _)
      colCert_119_98_5.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_98_10 (hp : 10 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 10 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 10 (transLenTr ⟨98, by decide⟩ 10 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 10 (transLenTr ⟨98, by decide⟩ 10 hp)) T119_98
      hfix119_98 hinj119_98 hcardT119_98
      (fun i => conj_mem_of_fixedPoints _ _ (T119_98 i) (hfix119_98 i) _)
      ⟨119, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 10 hp) Q2.T119_98_2 Q2.hfix119_98_2 Q2.hinj119_98_2
      Q2.hcardT119_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_98_2 i) (Q2.hfix119_98_2 i) _)
      colCert_119_98_10.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_98_15 (hp : 15 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 15 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 15 (transLenTr ⟨98, by decide⟩ 15 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 15 (transLenTr ⟨98, by decide⟩ 15 hp)) T119_98
      hfix119_98 hinj119_98 hcardT119_98
      (fun i => conj_mem_of_fixedPoints _ _ (T119_98 i) (hfix119_98 i) _)
      ⟨119, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 15 hp) Q2.T119_98_2 Q2.hfix119_98_2 Q2.hinj119_98_2
      Q2.hcardT119_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_98_2 i) (Q2.hfix119_98_2 i) _)
      colCert_119_98_15.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_98_20 (hp : 20 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 20 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 20 (transLenTr ⟨98, by decide⟩ 20 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 20 (transLenTr ⟨98, by decide⟩ 20 hp)) T119_98
      hfix119_98 hinj119_98 hcardT119_98
      (fun i => conj_mem_of_fixedPoints _ _ (T119_98 i) (hfix119_98 i) _)
      ⟨119, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 20 hp) Q2.T119_98_2 Q2.hfix119_98_2 Q2.hinj119_98_2
      Q2.hcardT119_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_98_2 i) (Q2.hfix119_98_2 i) _)
      colCert_119_98_20.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_103_0 (hp : 0 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 0 (transLenTr ⟨103, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 0 (transLenTr ⟨103, by decide⟩ 0 hp)) T119_103
      hfix119_103 hinj119_103 hcardT119_103
      (fun i => conj_mem_of_fixedPoints _ _ (T119_103 i) (hfix119_103 i) _)
      ⟨119, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 0 hp) Q2.T119_103_2 Q2.hfix119_103_2 Q2.hinj119_103_2
      Q2.hcardT119_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_103_2 i) (Q2.hfix119_103_2 i) _)
      colCert_119_103_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_103_1 (hp : 1 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 1 (transLenTr ⟨103, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 1 (transLenTr ⟨103, by decide⟩ 1 hp)) T119_103
      hfix119_103 hinj119_103 hcardT119_103
      (fun i => conj_mem_of_fixedPoints _ _ (T119_103 i) (hfix119_103 i) _)
      ⟨119, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 1 hp) Q2.T119_103_2 Q2.hfix119_103_2 Q2.hinj119_103_2
      Q2.hcardT119_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_103_2 i) (Q2.hfix119_103_2 i) _)
      colCert_119_103_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_103_2 (hp : 2 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 2 (transLenTr ⟨103, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 2 (transLenTr ⟨103, by decide⟩ 2 hp)) T119_103
      hfix119_103 hinj119_103 hcardT119_103
      (fun i => conj_mem_of_fixedPoints _ _ (T119_103 i) (hfix119_103 i) _)
      ⟨119, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 2 hp) Q2.T119_103_2 Q2.hfix119_103_2 Q2.hinj119_103_2
      Q2.hcardT119_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_103_2 i) (Q2.hfix119_103_2 i) _)
      colCert_119_103_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_103_3 (hp : 3 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 3 (transLenTr ⟨103, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 3 (transLenTr ⟨103, by decide⟩ 3 hp)) T119_103
      hfix119_103 hinj119_103 hcardT119_103
      (fun i => conj_mem_of_fixedPoints _ _ (T119_103 i) (hfix119_103 i) _)
      ⟨119, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 3 hp) Q2.T119_103_2 Q2.hfix119_103_2 Q2.hinj119_103_2
      Q2.hcardT119_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_103_2 i) (Q2.hfix119_103_2 i) _)
      colCert_119_103_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_103_4 (hp : 4 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 4 (transLenTr ⟨103, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 4 (transLenTr ⟨103, by decide⟩ 4 hp)) T119_103
      hfix119_103 hinj119_103 hcardT119_103
      (fun i => conj_mem_of_fixedPoints _ _ (T119_103 i) (hfix119_103 i) _)
      ⟨119, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 4 hp) Q2.T119_103_2 Q2.hfix119_103_2 Q2.hinj119_103_2
      Q2.hcardT119_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_103_2 i) (Q2.hfix119_103_2 i) _)
      colCert_119_103_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_103_5 (hp : 5 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 5 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 5 (transLenTr ⟨103, by decide⟩ 5 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 5 (transLenTr ⟨103, by decide⟩ 5 hp)) T119_103
      hfix119_103 hinj119_103 hcardT119_103
      (fun i => conj_mem_of_fixedPoints _ _ (T119_103 i) (hfix119_103 i) _)
      ⟨119, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 5 hp) Q2.T119_103_2 Q2.hfix119_103_2 Q2.hinj119_103_2
      Q2.hcardT119_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_103_2 i) (Q2.hfix119_103_2 i) _)
      colCert_119_103_5.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_103_10 (hp : 10 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 10 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 10 (transLenTr ⟨103, by decide⟩ 10 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 10 (transLenTr ⟨103, by decide⟩ 10 hp)) T119_103
      hfix119_103 hinj119_103 hcardT119_103
      (fun i => conj_mem_of_fixedPoints _ _ (T119_103 i) (hfix119_103 i) _)
      ⟨119, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 10 hp) Q2.T119_103_2 Q2.hfix119_103_2 Q2.hinj119_103_2
      Q2.hcardT119_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_103_2 i) (Q2.hfix119_103_2 i) _)
      colCert_119_103_10.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_103_15 (hp : 15 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 15 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 15 (transLenTr ⟨103, by decide⟩ 15 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 15 (transLenTr ⟨103, by decide⟩ 15 hp)) T119_103
      hfix119_103 hinj119_103 hcardT119_103
      (fun i => conj_mem_of_fixedPoints _ _ (T119_103 i) (hfix119_103 i) _)
      ⟨119, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 15 hp) Q2.T119_103_2 Q2.hfix119_103_2 Q2.hinj119_103_2
      Q2.hcardT119_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_103_2 i) (Q2.hfix119_103_2 i) _)
      colCert_119_103_15.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_103_20 (hp : 20 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 20 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 20 (transLenTr ⟨103, by decide⟩ 20 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 20 (transLenTr ⟨103, by decide⟩ 20 hp)) T119_103
      hfix119_103 hinj119_103 hcardT119_103
      (fun i => conj_mem_of_fixedPoints _ _ (T119_103 i) (hfix119_103 i) _)
      ⟨119, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 20 hp) Q2.T119_103_2 Q2.hfix119_103_2 Q2.hinj119_103_2
      Q2.hcardT119_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_103_2 i) (Q2.hfix119_103_2 i) _)
      colCert_119_103_20.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_108_0 (hp : 0 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 0 (transLenTr ⟨108, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 0 (transLenTr ⟨108, by decide⟩ 0 hp)) T119_108
      hfix119_108 hinj119_108 hcardT119_108
      (fun i => conj_mem_of_fixedPoints _ _ (T119_108 i) (hfix119_108 i) _)
      ⟨119, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 0 hp) Q2.T119_108_2 Q2.hfix119_108_2 Q2.hinj119_108_2
      Q2.hcardT119_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_108_2 i) (Q2.hfix119_108_2 i) _)
      colCert_119_108_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_108_1 (hp : 1 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 1 (transLenTr ⟨108, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 1 (transLenTr ⟨108, by decide⟩ 1 hp)) T119_108
      hfix119_108 hinj119_108 hcardT119_108
      (fun i => conj_mem_of_fixedPoints _ _ (T119_108 i) (hfix119_108 i) _)
      ⟨119, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 1 hp) Q2.T119_108_2 Q2.hfix119_108_2 Q2.hinj119_108_2
      Q2.hcardT119_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_108_2 i) (Q2.hfix119_108_2 i) _)
      colCert_119_108_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_108_2 (hp : 2 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 2 (transLenTr ⟨108, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 2 (transLenTr ⟨108, by decide⟩ 2 hp)) T119_108
      hfix119_108 hinj119_108 hcardT119_108
      (fun i => conj_mem_of_fixedPoints _ _ (T119_108 i) (hfix119_108 i) _)
      ⟨119, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 2 hp) Q2.T119_108_2 Q2.hfix119_108_2 Q2.hinj119_108_2
      Q2.hcardT119_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_108_2 i) (Q2.hfix119_108_2 i) _)
      colCert_119_108_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_108_3 (hp : 3 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 3 (transLenTr ⟨108, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 3 (transLenTr ⟨108, by decide⟩ 3 hp)) T119_108
      hfix119_108 hinj119_108 hcardT119_108
      (fun i => conj_mem_of_fixedPoints _ _ (T119_108 i) (hfix119_108 i) _)
      ⟨119, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 3 hp) Q2.T119_108_2 Q2.hfix119_108_2 Q2.hinj119_108_2
      Q2.hcardT119_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_108_2 i) (Q2.hfix119_108_2 i) _)
      colCert_119_108_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_108_4 (hp : 4 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 4 (transLenTr ⟨108, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 4 (transLenTr ⟨108, by decide⟩ 4 hp)) T119_108
      hfix119_108 hinj119_108 hcardT119_108
      (fun i => conj_mem_of_fixedPoints _ _ (T119_108 i) (hfix119_108 i) _)
      ⟨119, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 4 hp) Q2.T119_108_2 Q2.hfix119_108_2 Q2.hinj119_108_2
      Q2.hcardT119_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_108_2 i) (Q2.hfix119_108_2 i) _)
      colCert_119_108_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_108_5 (hp : 5 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 5 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 5 (transLenTr ⟨108, by decide⟩ 5 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 5 (transLenTr ⟨108, by decide⟩ 5 hp)) T119_108
      hfix119_108 hinj119_108 hcardT119_108
      (fun i => conj_mem_of_fixedPoints _ _ (T119_108 i) (hfix119_108 i) _)
      ⟨119, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 5 hp) Q2.T119_108_2 Q2.hfix119_108_2 Q2.hinj119_108_2
      Q2.hcardT119_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_108_2 i) (Q2.hfix119_108_2 i) _)
      colCert_119_108_5.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_108_10 (hp : 10 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 10 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 10 (transLenTr ⟨108, by decide⟩ 10 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 10 (transLenTr ⟨108, by decide⟩ 10 hp)) T119_108
      hfix119_108 hinj119_108 hcardT119_108
      (fun i => conj_mem_of_fixedPoints _ _ (T119_108 i) (hfix119_108 i) _)
      ⟨119, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 10 hp) Q2.T119_108_2 Q2.hfix119_108_2 Q2.hinj119_108_2
      Q2.hcardT119_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_108_2 i) (Q2.hfix119_108_2 i) _)
      colCert_119_108_10.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_108_15 (hp : 15 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 15 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 15 (transLenTr ⟨108, by decide⟩ 15 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 15 (transLenTr ⟨108, by decide⟩ 15 hp)) T119_108
      hfix119_108 hinj119_108 hcardT119_108
      (fun i => conj_mem_of_fixedPoints _ _ (T119_108 i) (hfix119_108 i) _)
      ⟨119, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 15 hp) Q2.T119_108_2 Q2.hfix119_108_2 Q2.hinj119_108_2
      Q2.hcardT119_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_108_2 i) (Q2.hfix119_108_2 i) _)
      colCert_119_108_15.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_108_20 (hp : 20 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 20 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 20 (transLenTr ⟨108, by decide⟩ 20 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 20 (transLenTr ⟨108, by decide⟩ 20 hp)) T119_108
      hfix119_108 hinj119_108 hcardT119_108
      (fun i => conj_mem_of_fixedPoints _ _ (T119_108 i) (hfix119_108 i) _)
      ⟨119, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 20 hp) Q2.T119_108_2 Q2.hfix119_108_2 Q2.hinj119_108_2
      Q2.hcardT119_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_108_2 i) (Q2.hfix119_108_2 i) _)
      colCert_119_108_20.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_113_0 (hp : 0 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 0 (transLenTr ⟨113, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 0 (transLenTr ⟨113, by decide⟩ 0 hp)) T119_113
      hfix119_113 hinj119_113 hcardT119_113
      (fun i => conj_mem_of_fixedPoints _ _ (T119_113 i) (hfix119_113 i) _)
      ⟨119, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 0 hp) Q2.T119_113_2 Q2.hfix119_113_2 Q2.hinj119_113_2
      Q2.hcardT119_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_113_2 i) (Q2.hfix119_113_2 i) _)
      colCert_119_113_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_113_1 (hp : 1 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 1 (transLenTr ⟨113, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 1 (transLenTr ⟨113, by decide⟩ 1 hp)) T119_113
      hfix119_113 hinj119_113 hcardT119_113
      (fun i => conj_mem_of_fixedPoints _ _ (T119_113 i) (hfix119_113 i) _)
      ⟨119, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 1 hp) Q2.T119_113_2 Q2.hfix119_113_2 Q2.hinj119_113_2
      Q2.hcardT119_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_113_2 i) (Q2.hfix119_113_2 i) _)
      colCert_119_113_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_113_2 (hp : 2 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 2 (transLenTr ⟨113, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 2 (transLenTr ⟨113, by decide⟩ 2 hp)) T119_113
      hfix119_113 hinj119_113 hcardT119_113
      (fun i => conj_mem_of_fixedPoints _ _ (T119_113 i) (hfix119_113 i) _)
      ⟨119, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 2 hp) Q2.T119_113_2 Q2.hfix119_113_2 Q2.hinj119_113_2
      Q2.hcardT119_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_113_2 i) (Q2.hfix119_113_2 i) _)
      colCert_119_113_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_113_3 (hp : 3 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 3 (transLenTr ⟨113, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 3 (transLenTr ⟨113, by decide⟩ 3 hp)) T119_113
      hfix119_113 hinj119_113 hcardT119_113
      (fun i => conj_mem_of_fixedPoints _ _ (T119_113 i) (hfix119_113 i) _)
      ⟨119, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 3 hp) Q2.T119_113_2 Q2.hfix119_113_2 Q2.hinj119_113_2
      Q2.hcardT119_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_113_2 i) (Q2.hfix119_113_2 i) _)
      colCert_119_113_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_113_4 (hp : 4 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 4 (transLenTr ⟨113, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 4 (transLenTr ⟨113, by decide⟩ 4 hp)) T119_113
      hfix119_113 hinj119_113 hcardT119_113
      (fun i => conj_mem_of_fixedPoints _ _ (T119_113 i) (hfix119_113 i) _)
      ⟨119, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 4 hp) Q2.T119_113_2 Q2.hfix119_113_2 Q2.hinj119_113_2
      Q2.hcardT119_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_113_2 i) (Q2.hfix119_113_2 i) _)
      colCert_119_113_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_113_5 (hp : 5 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 5 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 5 (transLenTr ⟨113, by decide⟩ 5 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 5 (transLenTr ⟨113, by decide⟩ 5 hp)) T119_113
      hfix119_113 hinj119_113 hcardT119_113
      (fun i => conj_mem_of_fixedPoints _ _ (T119_113 i) (hfix119_113 i) _)
      ⟨119, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 5 hp) Q2.T119_113_2 Q2.hfix119_113_2 Q2.hinj119_113_2
      Q2.hcardT119_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_113_2 i) (Q2.hfix119_113_2 i) _)
      colCert_119_113_5.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_113_10 (hp : 10 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 10 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 10 (transLenTr ⟨113, by decide⟩ 10 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 10 (transLenTr ⟨113, by decide⟩ 10 hp)) T119_113
      hfix119_113 hinj119_113 hcardT119_113
      (fun i => conj_mem_of_fixedPoints _ _ (T119_113 i) (hfix119_113 i) _)
      ⟨119, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 10 hp) Q2.T119_113_2 Q2.hfix119_113_2 Q2.hinj119_113_2
      Q2.hcardT119_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_113_2 i) (Q2.hfix119_113_2 i) _)
      colCert_119_113_10.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_113_15 (hp : 15 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 15 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 15 (transLenTr ⟨113, by decide⟩ 15 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 15 (transLenTr ⟨113, by decide⟩ 15 hp)) T119_113
      hfix119_113 hinj119_113 hcardT119_113
      (fun i => conj_mem_of_fixedPoints _ _ (T119_113 i) (hfix119_113 i) _)
      ⟨119, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 15 hp) Q2.T119_113_2 Q2.hfix119_113_2 Q2.hinj119_113_2
      Q2.hcardT119_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_113_2 i) (Q2.hfix119_113_2 i) _)
      colCert_119_113_15.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_113_20 (hp : 20 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 20 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 20 (transLenTr ⟨113, by decide⟩ 20 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 20 (transLenTr ⟨113, by decide⟩ 20 hp)) T119_113
      hfix119_113 hinj119_113 hcardT119_113
      (fun i => conj_mem_of_fixedPoints _ _ (T119_113 i) (hfix119_113 i) _)
      ⟨119, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 20 hp) Q2.T119_113_2 Q2.hfix119_113_2 Q2.hinj119_113_2
      Q2.hcardT119_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_113_2 i) (Q2.hfix119_113_2 i) _)
      colCert_119_113_20.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_0 (hp : 0 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 0 (transLenTr ⟨119, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 0 (transLenTr ⟨119, by decide⟩ 0 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 0 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_1 (hp : 1 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 1 (transLenTr ⟨119, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 1 (transLenTr ⟨119, by decide⟩ 1 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 1 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_2 (hp : 2 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 2 (transLenTr ⟨119, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 2 (transLenTr ⟨119, by decide⟩ 2 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 2 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_3 (hp : 3 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 3 (transLenTr ⟨119, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 3 (transLenTr ⟨119, by decide⟩ 3 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 3 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_4 (hp : 4 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 4 (transLenTr ⟨119, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 4 (transLenTr ⟨119, by decide⟩ 4 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 4 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_5 (hp : 5 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 5 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 5 (transLenTr ⟨119, by decide⟩ 5 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 5 (transLenTr ⟨119, by decide⟩ 5 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 5 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_5.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_6 (hp : 6 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 6 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 6 (transLenTr ⟨119, by decide⟩ 6 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 6 (transLenTr ⟨119, by decide⟩ 6 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 6 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_6.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_7 (hp : 7 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 7 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 7 (transLenTr ⟨119, by decide⟩ 7 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 7 (transLenTr ⟨119, by decide⟩ 7 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 7 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_7.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_8 (hp : 8 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 8 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 8 (transLenTr ⟨119, by decide⟩ 8 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 8 (transLenTr ⟨119, by decide⟩ 8 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 8 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_8.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_9 (hp : 9 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 9 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 9 (transLenTr ⟨119, by decide⟩ 9 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 9 (transLenTr ⟨119, by decide⟩ 9 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 9 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_9.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_10 (hp : 10 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 10 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 10 (transLenTr ⟨119, by decide⟩ 10 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 10 (transLenTr ⟨119, by decide⟩ 10 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 10 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_10.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_11 (hp : 11 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 11 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 11 (transLenTr ⟨119, by decide⟩ 11 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 11 (transLenTr ⟨119, by decide⟩ 11 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 11 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_11.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_12 (hp : 12 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 12 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 12 (transLenTr ⟨119, by decide⟩ 12 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 12 (transLenTr ⟨119, by decide⟩ 12 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 12 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_12.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_13 (hp : 13 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 13 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 13 (transLenTr ⟨119, by decide⟩ 13 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 13 (transLenTr ⟨119, by decide⟩ 13 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 13 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_13.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_14 (hp : 14 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 14 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 14 (transLenTr ⟨119, by decide⟩ 14 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 14 (transLenTr ⟨119, by decide⟩ 14 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 14 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_14.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_15 (hp : 15 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 15 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 15 (transLenTr ⟨119, by decide⟩ 15 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 15 (transLenTr ⟨119, by decide⟩ 15 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 15 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_15.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_16 (hp : 16 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 16 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 16 (transLenTr ⟨119, by decide⟩ 16 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 16 (transLenTr ⟨119, by decide⟩ 16 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 16 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_16.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_17 (hp : 17 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 17 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 17 (transLenTr ⟨119, by decide⟩ 17 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 17 (transLenTr ⟨119, by decide⟩ 17 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 17 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_17.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_18 (hp : 18 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 18 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 18 (transLenTr ⟨119, by decide⟩ 18 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 18 (transLenTr ⟨119, by decide⟩ 18 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 18 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_18.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_19 (hp : 19 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 19 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 19 (transLenTr ⟨119, by decide⟩ 19 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 19 (transLenTr ⟨119, by decide⟩ 19 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 19 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_19.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_20 (hp : 20 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 20 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 20 (transLenTr ⟨119, by decide⟩ 20 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 20 (transLenTr ⟨119, by decide⟩ 20 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 20 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_20.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_21 (hp : 21 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 21 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 21 (transLenTr ⟨119, by decide⟩ 21 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 21 (transLenTr ⟨119, by decide⟩ 21 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 21 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_21.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_22 (hp : 22 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 22 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 22 (transLenTr ⟨119, by decide⟩ 22 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 22 (transLenTr ⟨119, by decide⟩ 22 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 22 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_22.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_23 (hp : 23 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 23 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 23 (transLenTr ⟨119, by decide⟩ 23 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 23 (transLenTr ⟨119, by decide⟩ 23 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 23 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_23.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_24 (hp : 24 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 24 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 24 (transLenTr ⟨119, by decide⟩ 24 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 24 (transLenTr ⟨119, by decide⟩ 24 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 24 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_24.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_25 (hp : 25 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 25 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 25 (transLenTr ⟨119, by decide⟩ 25 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 25 (transLenTr ⟨119, by decide⟩ 25 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 25 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_25.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_30 (hp : 30 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 30 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 30 (transLenTr ⟨119, by decide⟩ 30 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 30 (transLenTr ⟨119, by decide⟩ 30 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 30 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_30.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_35 (hp : 35 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 35 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 35 (transLenTr ⟨119, by decide⟩ 35 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 35 (transLenTr ⟨119, by decide⟩ 35 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 35 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_35.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_40 (hp : 40 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 40 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 40 (transLenTr ⟨119, by decide⟩ 40 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 40 (transLenTr ⟨119, by decide⟩ 40 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 40 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_40.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_45 (hp : 45 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 45 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 45 (transLenTr ⟨119, by decide⟩ 45 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 45 (transLenTr ⟨119, by decide⟩ 45 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 45 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_45.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_50 (hp : 50 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 50 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 50 (transLenTr ⟨119, by decide⟩ 50 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 50 (transLenTr ⟨119, by decide⟩ 50 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 50 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_50.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_55 (hp : 55 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 55 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 55 (transLenTr ⟨119, by decide⟩ 55 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 55 (transLenTr ⟨119, by decide⟩ 55 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 55 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_55.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_60 (hp : 60 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 60 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 60 (transLenTr ⟨119, by decide⟩ 60 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 60 (transLenTr ⟨119, by decide⟩ 60 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 60 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_60.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_65 (hp : 65 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 65 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 65 (transLenTr ⟨119, by decide⟩ 65 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 65 (transLenTr ⟨119, by decide⟩ 65 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 65 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_65.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_70 (hp : 70 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 70 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 70 (transLenTr ⟨119, by decide⟩ 70 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 70 (transLenTr ⟨119, by decide⟩ 70 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 70 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_70.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_75 (hp : 75 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 75 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 75 (transLenTr ⟨119, by decide⟩ 75 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 75 (transLenTr ⟨119, by decide⟩ 75 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 75 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_75.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_80 (hp : 80 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 80 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 80 (transLenTr ⟨119, by decide⟩ 80 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 80 (transLenTr ⟨119, by decide⟩ 80 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 80 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_80.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_85 (hp : 85 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 85 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 85 (transLenTr ⟨119, by decide⟩ 85 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 85 (transLenTr ⟨119, by decide⟩ 85 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 85 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_85.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_90 (hp : 90 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 90 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 90 (transLenTr ⟨119, by decide⟩ 90 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 90 (transLenTr ⟨119, by decide⟩ 90 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 90 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_90.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_95 (hp : 95 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 95 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 95 (transLenTr ⟨119, by decide⟩ 95 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 95 (transLenTr ⟨119, by decide⟩ 95 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 95 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_95.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_100 (hp : 100 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 100 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 100 (transLenTr ⟨119, by decide⟩ 100 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 100 (transLenTr ⟨119, by decide⟩ 100 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 100 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_100.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_105 (hp : 105 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 105 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 105 (transLenTr ⟨119, by decide⟩ 105 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 105 (transLenTr ⟨119, by decide⟩ 105 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 105 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_105.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_110 (hp : 110 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 110 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 110 (transLenTr ⟨119, by decide⟩ 110 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 110 (transLenTr ⟨119, by decide⟩ 110 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 110 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_110.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_115 (hp : 115 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 115 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 115 (transLenTr ⟨119, by decide⟩ 115 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 115 (transLenTr ⟨119, by decide⟩ 115 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 115 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_115.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_119_120 (hp : 120 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 120 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 120 (transLenTr ⟨119, by decide⟩ 120 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 120 (transLenTr ⟨119, by decide⟩ 120 hp)) T119_119
      hfix119_119 hinj119_119 hcardT119_119
      (fun i => conj_mem_of_fixedPoints _ _ (T119_119 i) (hfix119_119 i) _)
      ⟨119, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 120 hp) Q2.T119_119_2 Q2.hfix119_119_2 Q2.hinj119_119_2
      Q2.hcardT119_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_119_2 i) (Q2.hfix119_119_2 i) _)
      colCert_119_119_120.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_120_1_0 (hp : 0 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp)) T120_1
      hfix120_1 hinj120_1 hcardT120_1
      (fun i => conj_mem_of_fixedPoints _ _ (T120_1 i) (hfix120_1 i) _)
      ⟨120, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 0 hp) Q2.T120_1_2 Q2.hfix120_1_2 Q2.hinj120_1_2
      Q2.hcardT120_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_1_2 i) (Q2.hfix120_1_2 i) _)
      colCert_120_1_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_1_1 (hp : 1 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp)) T120_1
      hfix120_1 hinj120_1 hcardT120_1
      (fun i => conj_mem_of_fixedPoints _ _ (T120_1 i) (hfix120_1 i) _)
      ⟨120, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 1 hp) Q2.T120_1_2 Q2.hfix120_1_2 Q2.hinj120_1_2
      Q2.hcardT120_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_1_2 i) (Q2.hfix120_1_2 i) _)
      colCert_120_1_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_1_2 (hp : 2 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp)) T120_1
      hfix120_1 hinj120_1 hcardT120_1
      (fun i => conj_mem_of_fixedPoints _ _ (T120_1 i) (hfix120_1 i) _)
      ⟨120, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 2 hp) Q2.T120_1_2 Q2.hfix120_1_2 Q2.hinj120_1_2
      Q2.hcardT120_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_1_2 i) (Q2.hfix120_1_2 i) _)
      colCert_120_1_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_1_3 (hp : 3 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp)) T120_1
      hfix120_1 hinj120_1 hcardT120_1
      (fun i => conj_mem_of_fixedPoints _ _ (T120_1 i) (hfix120_1 i) _)
      ⟨120, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 3 hp) Q2.T120_1_2 Q2.hfix120_1_2 Q2.hinj120_1_2
      Q2.hcardT120_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_1_2 i) (Q2.hfix120_1_2 i) _)
      colCert_120_1_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_1_4 (hp : 4 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp)) T120_1
      hfix120_1 hinj120_1 hcardT120_1
      (fun i => conj_mem_of_fixedPoints _ _ (T120_1 i) (hfix120_1 i) _)
      ⟨120, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 4 hp) Q2.T120_1_2 Q2.hfix120_1_2 Q2.hinj120_1_2
      Q2.hcardT120_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_1_2 i) (Q2.hfix120_1_2 i) _)
      colCert_120_1_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_6_0 (hp : 0 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp)) T120_6
      hfix120_6 hinj120_6 hcardT120_6
      (fun i => conj_mem_of_fixedPoints _ _ (T120_6 i) (hfix120_6 i) _)
      ⟨120, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 0 hp) Q2.T120_6_2 Q2.hfix120_6_2 Q2.hinj120_6_2
      Q2.hcardT120_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_6_2 i) (Q2.hfix120_6_2 i) _)
      colCert_120_6_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_6_1 (hp : 1 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp)) T120_6
      hfix120_6 hinj120_6 hcardT120_6
      (fun i => conj_mem_of_fixedPoints _ _ (T120_6 i) (hfix120_6 i) _)
      ⟨120, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 1 hp) Q2.T120_6_2 Q2.hfix120_6_2 Q2.hinj120_6_2
      Q2.hcardT120_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_6_2 i) (Q2.hfix120_6_2 i) _)
      colCert_120_6_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_6_2 (hp : 2 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp)) T120_6
      hfix120_6 hinj120_6 hcardT120_6
      (fun i => conj_mem_of_fixedPoints _ _ (T120_6 i) (hfix120_6 i) _)
      ⟨120, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 2 hp) Q2.T120_6_2 Q2.hfix120_6_2 Q2.hinj120_6_2
      Q2.hcardT120_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_6_2 i) (Q2.hfix120_6_2 i) _)
      colCert_120_6_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_6_3 (hp : 3 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp)) T120_6
      hfix120_6 hinj120_6 hcardT120_6
      (fun i => conj_mem_of_fixedPoints _ _ (T120_6 i) (hfix120_6 i) _)
      ⟨120, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 3 hp) Q2.T120_6_2 Q2.hfix120_6_2 Q2.hinj120_6_2
      Q2.hcardT120_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_6_2 i) (Q2.hfix120_6_2 i) _)
      colCert_120_6_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_6_4 (hp : 4 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp)) T120_6
      hfix120_6 hinj120_6 hcardT120_6
      (fun i => conj_mem_of_fixedPoints _ _ (T120_6 i) (hfix120_6 i) _)
      ⟨120, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 4 hp) Q2.T120_6_2 Q2.hfix120_6_2 Q2.hinj120_6_2
      Q2.hcardT120_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_6_2 i) (Q2.hfix120_6_2 i) _)
      colCert_120_6_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_7_0 (hp : 0 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp)) T120_7
      hfix120_7 hinj120_7 hcardT120_7
      (fun i => conj_mem_of_fixedPoints _ _ (T120_7 i) (hfix120_7 i) _)
      ⟨120, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 0 hp) Q2.T120_7_2 Q2.hfix120_7_2 Q2.hinj120_7_2
      Q2.hcardT120_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_7_2 i) (Q2.hfix120_7_2 i) _)
      colCert_120_7_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_7_1 (hp : 1 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp)) T120_7
      hfix120_7 hinj120_7 hcardT120_7
      (fun i => conj_mem_of_fixedPoints _ _ (T120_7 i) (hfix120_7 i) _)
      ⟨120, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 1 hp) Q2.T120_7_2 Q2.hfix120_7_2 Q2.hinj120_7_2
      Q2.hcardT120_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_7_2 i) (Q2.hfix120_7_2 i) _)
      colCert_120_7_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_7_2 (hp : 2 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp)) T120_7
      hfix120_7 hinj120_7 hcardT120_7
      (fun i => conj_mem_of_fixedPoints _ _ (T120_7 i) (hfix120_7 i) _)
      ⟨120, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 2 hp) Q2.T120_7_2 Q2.hfix120_7_2 Q2.hinj120_7_2
      Q2.hcardT120_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_7_2 i) (Q2.hfix120_7_2 i) _)
      colCert_120_7_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_7_3 (hp : 3 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp)) T120_7
      hfix120_7 hinj120_7 hcardT120_7
      (fun i => conj_mem_of_fixedPoints _ _ (T120_7 i) (hfix120_7 i) _)
      ⟨120, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 3 hp) Q2.T120_7_2 Q2.hfix120_7_2 Q2.hinj120_7_2
      Q2.hcardT120_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_7_2 i) (Q2.hfix120_7_2 i) _)
      colCert_120_7_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_7_4 (hp : 4 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp)) T120_7
      hfix120_7 hinj120_7 hcardT120_7
      (fun i => conj_mem_of_fixedPoints _ _ (T120_7 i) (hfix120_7 i) _)
      ⟨120, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 4 hp) Q2.T120_7_2 Q2.hfix120_7_2 Q2.hinj120_7_2
      Q2.hcardT120_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_7_2 i) (Q2.hfix120_7_2 i) _)
      colCert_120_7_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_8_0 (hp : 0 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp)) T120_8
      hfix120_8 hinj120_8 hcardT120_8
      (fun i => conj_mem_of_fixedPoints _ _ (T120_8 i) (hfix120_8 i) _)
      ⟨120, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 0 hp) Q2.T120_8_2 Q2.hfix120_8_2 Q2.hinj120_8_2
      Q2.hcardT120_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_8_2 i) (Q2.hfix120_8_2 i) _)
      colCert_120_8_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_8_1 (hp : 1 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp)) T120_8
      hfix120_8 hinj120_8 hcardT120_8
      (fun i => conj_mem_of_fixedPoints _ _ (T120_8 i) (hfix120_8 i) _)
      ⟨120, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 1 hp) Q2.T120_8_2 Q2.hfix120_8_2 Q2.hinj120_8_2
      Q2.hcardT120_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_8_2 i) (Q2.hfix120_8_2 i) _)
      colCert_120_8_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_8_2 (hp : 2 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp)) T120_8
      hfix120_8 hinj120_8 hcardT120_8
      (fun i => conj_mem_of_fixedPoints _ _ (T120_8 i) (hfix120_8 i) _)
      ⟨120, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 2 hp) Q2.T120_8_2 Q2.hfix120_8_2 Q2.hinj120_8_2
      Q2.hcardT120_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_8_2 i) (Q2.hfix120_8_2 i) _)
      colCert_120_8_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_8_3 (hp : 3 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp)) T120_8
      hfix120_8 hinj120_8 hcardT120_8
      (fun i => conj_mem_of_fixedPoints _ _ (T120_8 i) (hfix120_8 i) _)
      ⟨120, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 3 hp) Q2.T120_8_2 Q2.hfix120_8_2 Q2.hinj120_8_2
      Q2.hcardT120_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_8_2 i) (Q2.hfix120_8_2 i) _)
      colCert_120_8_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_8_4 (hp : 4 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp)) T120_8
      hfix120_8 hinj120_8 hcardT120_8
      (fun i => conj_mem_of_fixedPoints _ _ (T120_8 i) (hfix120_8 i) _)
      ⟨120, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 4 hp) Q2.T120_8_2 Q2.hfix120_8_2 Q2.hinj120_8_2
      Q2.hcardT120_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_8_2 i) (Q2.hfix120_8_2 i) _)
      colCert_120_8_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_9_0 (hp : 0 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp)) T120_9
      hfix120_9 hinj120_9 hcardT120_9
      (fun i => conj_mem_of_fixedPoints _ _ (T120_9 i) (hfix120_9 i) _)
      ⟨120, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 0 hp) Q2.T120_9_2 Q2.hfix120_9_2 Q2.hinj120_9_2
      Q2.hcardT120_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_9_2 i) (Q2.hfix120_9_2 i) _)
      colCert_120_9_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_9_1 (hp : 1 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp)) T120_9
      hfix120_9 hinj120_9 hcardT120_9
      (fun i => conj_mem_of_fixedPoints _ _ (T120_9 i) (hfix120_9 i) _)
      ⟨120, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 1 hp) Q2.T120_9_2 Q2.hfix120_9_2 Q2.hinj120_9_2
      Q2.hcardT120_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_9_2 i) (Q2.hfix120_9_2 i) _)
      colCert_120_9_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_9_2 (hp : 2 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp)) T120_9
      hfix120_9 hinj120_9 hcardT120_9
      (fun i => conj_mem_of_fixedPoints _ _ (T120_9 i) (hfix120_9 i) _)
      ⟨120, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 2 hp) Q2.T120_9_2 Q2.hfix120_9_2 Q2.hinj120_9_2
      Q2.hcardT120_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_9_2 i) (Q2.hfix120_9_2 i) _)
      colCert_120_9_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_9_3 (hp : 3 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp)) T120_9
      hfix120_9 hinj120_9 hcardT120_9
      (fun i => conj_mem_of_fixedPoints _ _ (T120_9 i) (hfix120_9 i) _)
      ⟨120, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 3 hp) Q2.T120_9_2 Q2.hfix120_9_2 Q2.hinj120_9_2
      Q2.hcardT120_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_9_2 i) (Q2.hfix120_9_2 i) _)
      colCert_120_9_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_9_4 (hp : 4 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp)) T120_9
      hfix120_9 hinj120_9 hcardT120_9
      (fun i => conj_mem_of_fixedPoints _ _ (T120_9 i) (hfix120_9 i) _)
      ⟨120, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 4 hp) Q2.T120_9_2 Q2.hfix120_9_2 Q2.hinj120_9_2
      Q2.hcardT120_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_9_2 i) (Q2.hfix120_9_2 i) _)
      colCert_120_9_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T120_10
      hfix120_10 hinj120_10 hcardT120_10
      (fun i => conj_mem_of_fixedPoints _ _ (T120_10 i) (hfix120_10 i) _)
      ⟨120, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T120_10_2 Q2.hfix120_10_2 Q2.hinj120_10_2
      Q2.hcardT120_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_10_2 i) (Q2.hfix120_10_2 i) _)
      colCert_120_10_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T120_10
      hfix120_10 hinj120_10 hcardT120_10
      (fun i => conj_mem_of_fixedPoints _ _ (T120_10 i) (hfix120_10 i) _)
      ⟨120, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T120_10_2 Q2.hfix120_10_2 Q2.hinj120_10_2
      Q2.hcardT120_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_10_2 i) (Q2.hfix120_10_2 i) _)
      colCert_120_10_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T120_10
      hfix120_10 hinj120_10 hcardT120_10
      (fun i => conj_mem_of_fixedPoints _ _ (T120_10 i) (hfix120_10 i) _)
      ⟨120, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T120_10_2 Q2.hfix120_10_2 Q2.hinj120_10_2
      Q2.hcardT120_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_10_2 i) (Q2.hfix120_10_2 i) _)
      colCert_120_10_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T120_10
      hfix120_10 hinj120_10 hcardT120_10
      (fun i => conj_mem_of_fixedPoints _ _ (T120_10 i) (hfix120_10 i) _)
      ⟨120, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T120_10_2 Q2.hfix120_10_2 Q2.hinj120_10_2
      Q2.hcardT120_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_10_2 i) (Q2.hfix120_10_2 i) _)
      colCert_120_10_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T120_10
      hfix120_10 hinj120_10 hcardT120_10
      (fun i => conj_mem_of_fixedPoints _ _ (T120_10 i) (hfix120_10 i) _)
      ⟨120, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T120_10_2 Q2.hfix120_10_2 Q2.hinj120_10_2
      Q2.hcardT120_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_10_2 i) (Q2.hfix120_10_2 i) _)
      colCert_120_10_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T120_12
      hfix120_12 hinj120_12 hcardT120_12
      (fun i => conj_mem_of_fixedPoints _ _ (T120_12 i) (hfix120_12 i) _)
      ⟨120, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T120_12_2 Q2.hfix120_12_2 Q2.hinj120_12_2
      Q2.hcardT120_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_12_2 i) (Q2.hfix120_12_2 i) _)
      colCert_120_12_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T120_12
      hfix120_12 hinj120_12 hcardT120_12
      (fun i => conj_mem_of_fixedPoints _ _ (T120_12 i) (hfix120_12 i) _)
      ⟨120, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T120_12_2 Q2.hfix120_12_2 Q2.hinj120_12_2
      Q2.hcardT120_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_12_2 i) (Q2.hfix120_12_2 i) _)
      colCert_120_12_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T120_12
      hfix120_12 hinj120_12 hcardT120_12
      (fun i => conj_mem_of_fixedPoints _ _ (T120_12 i) (hfix120_12 i) _)
      ⟨120, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T120_12_2 Q2.hfix120_12_2 Q2.hinj120_12_2
      Q2.hcardT120_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_12_2 i) (Q2.hfix120_12_2 i) _)
      colCert_120_12_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T120_12
      hfix120_12 hinj120_12 hcardT120_12
      (fun i => conj_mem_of_fixedPoints _ _ (T120_12 i) (hfix120_12 i) _)
      ⟨120, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T120_12_2 Q2.hfix120_12_2 Q2.hinj120_12_2
      Q2.hcardT120_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_12_2 i) (Q2.hfix120_12_2 i) _)
      colCert_120_12_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T120_12
      hfix120_12 hinj120_12 hcardT120_12
      (fun i => conj_mem_of_fixedPoints _ _ (T120_12 i) (hfix120_12 i) _)
      ⟨120, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T120_12_2 Q2.hfix120_12_2 Q2.hinj120_12_2
      Q2.hcardT120_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_12_2 i) (Q2.hfix120_12_2 i) _)
      colCert_120_12_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_13_0 (hp : 0 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 0 (transLenTr ⟨13, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 0 (transLenTr ⟨13, by decide⟩ 0 hp)) T120_13
      hfix120_13 hinj120_13 hcardT120_13
      (fun i => conj_mem_of_fixedPoints _ _ (T120_13 i) (hfix120_13 i) _)
      ⟨120, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 0 hp) Q2.T120_13_2 Q2.hfix120_13_2 Q2.hinj120_13_2
      Q2.hcardT120_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_13_2 i) (Q2.hfix120_13_2 i) _)
      colCert_120_13_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_13_1 (hp : 1 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 1 (transLenTr ⟨13, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 1 (transLenTr ⟨13, by decide⟩ 1 hp)) T120_13
      hfix120_13 hinj120_13 hcardT120_13
      (fun i => conj_mem_of_fixedPoints _ _ (T120_13 i) (hfix120_13 i) _)
      ⟨120, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 1 hp) Q2.T120_13_2 Q2.hfix120_13_2 Q2.hinj120_13_2
      Q2.hcardT120_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_13_2 i) (Q2.hfix120_13_2 i) _)
      colCert_120_13_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_13_2 (hp : 2 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 2 (transLenTr ⟨13, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 2 (transLenTr ⟨13, by decide⟩ 2 hp)) T120_13
      hfix120_13 hinj120_13 hcardT120_13
      (fun i => conj_mem_of_fixedPoints _ _ (T120_13 i) (hfix120_13 i) _)
      ⟨120, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 2 hp) Q2.T120_13_2 Q2.hfix120_13_2 Q2.hinj120_13_2
      Q2.hcardT120_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_13_2 i) (Q2.hfix120_13_2 i) _)
      colCert_120_13_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_13_3 (hp : 3 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 3 (transLenTr ⟨13, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 3 (transLenTr ⟨13, by decide⟩ 3 hp)) T120_13
      hfix120_13 hinj120_13 hcardT120_13
      (fun i => conj_mem_of_fixedPoints _ _ (T120_13 i) (hfix120_13 i) _)
      ⟨120, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 3 hp) Q2.T120_13_2 Q2.hfix120_13_2 Q2.hinj120_13_2
      Q2.hcardT120_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_13_2 i) (Q2.hfix120_13_2 i) _)
      colCert_120_13_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_13_4 (hp : 4 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 4 (transLenTr ⟨13, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 4 (transLenTr ⟨13, by decide⟩ 4 hp)) T120_13
      hfix120_13 hinj120_13 hcardT120_13
      (fun i => conj_mem_of_fixedPoints _ _ (T120_13 i) (hfix120_13 i) _)
      ⟨120, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 4 hp) Q2.T120_13_2 Q2.hfix120_13_2 Q2.hinj120_13_2
      Q2.hcardT120_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_13_2 i) (Q2.hfix120_13_2 i) _)
      colCert_120_13_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_13_5 (hp : 5 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 5 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 5 (transLenTr ⟨13, by decide⟩ 5 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 5 (transLenTr ⟨13, by decide⟩ 5 hp)) T120_13
      hfix120_13 hinj120_13 hcardT120_13
      (fun i => conj_mem_of_fixedPoints _ _ (T120_13 i) (hfix120_13 i) _)
      ⟨120, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 5 hp) Q2.T120_13_2 Q2.hfix120_13_2 Q2.hinj120_13_2
      Q2.hcardT120_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_13_2 i) (Q2.hfix120_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 5 (transLenTr ⟨13, by decide⟩ 5 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T120_13 = colFn colCertDiv_120_13_5.D1 (m := 5) from colCertDiv_120_13_5.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 5 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T120_13_2 = colFn colCertDiv_120_13_5.D2 (m := 5) from colCertDiv_120_13_5.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_tau ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_13_5_tau_match


end LeanDring.P5Presentation
