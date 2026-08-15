/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C011
import LeanDring.P5.Data.ColCdd.C012
import LeanDring.P5.Data.ColRestCheap.C058
import LeanDring.P5.Data.ColRestCheap.C059
import LeanDring.P5.Data.ColRestCheap.C060
import LeanDring.P5.Data.ColRestCheap.C061
import LeanDring.P5.Data.EntryK.C032
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C011
import LeanDring.P5.Data.SpeciesDiv.C012
import LeanDring.P5.Data.SpeciesDiv.C010

/-! # Stage-5 leaves, chunk 33 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_126_48_3 (hp : 3 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 3 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp)) T126_48
      hfix126_48 hinj126_48 hcardT126_48
      (fun i => conj_mem_of_fixedPoints _ _ (T126_48 i) (hfix126_48 i) _)
      ⟨126, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 3 hp) Q2.T126_48_2 Q2.hfix126_48_2 Q2.hinj126_48_2
      Q2.hcardT126_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_48_2 i) (Q2.hfix126_48_2 i) _)
      colCert_126_48_3.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_48_4 (hp : 4 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 4 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp)) T126_48
      hfix126_48 hinj126_48 hcardT126_48
      (fun i => conj_mem_of_fixedPoints _ _ (T126_48 i) (hfix126_48 i) _)
      ⟨126, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 4 hp) Q2.T126_48_2 Q2.hfix126_48_2 Q2.hinj126_48_2
      Q2.hcardT126_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_48_2 i) (Q2.hfix126_48_2 i) _)
      colCert_126_48_4.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_48_5 (hp : 5 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 5 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨126, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp)) T126_48
      hfix126_48 hinj126_48 hcardT126_48
      (fun i => conj_mem_of_fixedPoints _ _ (T126_48 i) (hfix126_48 i) _)
      ⟨126, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 5 hp) Q2.T126_48_2 Q2.hfix126_48_2 Q2.hinj126_48_2
      Q2.hcardT126_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_48_2 i) (Q2.hfix126_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨126, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T126_48 = colFn colCertDiv_126_48_5.D1 (m := 5) from colCertDiv_126_48_5.bind1,
    show colData2 (⟨126, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 5 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T126_48_2 = colFn colCertDiv_126_48_5.D2 (m := 5) from colCertDiv_126_48_5.bind2]
  rw [alnId_126 j hj]
  exact fastcode_of_div ⟨126, by decide⟩ _ _ _
    ((alnId_126 j hj) ▸ Q2.listedAt (⟨126, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨126, by decide⟩ : Fin 148) hj hq).1) colCertDiv_126_48_5_match


theorem leaf_126_48_10 (hp : 10 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 10 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨126, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp)) T126_48
      hfix126_48 hinj126_48 hcardT126_48
      (fun i => conj_mem_of_fixedPoints _ _ (T126_48 i) (hfix126_48 i) _)
      ⟨126, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 10 hp) Q2.T126_48_2 Q2.hfix126_48_2 Q2.hinj126_48_2
      Q2.hcardT126_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_48_2 i) (Q2.hfix126_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨126, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T126_48 = colFn colCertDiv_126_48_10.D1 (m := 5) from colCertDiv_126_48_10.bind1,
    show colData2 (⟨126, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 10 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T126_48_2 = colFn colCertDiv_126_48_10.D2 (m := 5) from colCertDiv_126_48_10.bind2]
  rw [alnId_126 j hj]
  exact fastcode_of_div ⟨126, by decide⟩ _ _ _
    ((alnId_126 j hj) ▸ Q2.listedAt (⟨126, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨126, by decide⟩ : Fin 148) hj hq).1) colCertDiv_126_48_10_match


theorem leaf_126_48_15 (hp : 15 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 15 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨126, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp)) T126_48
      hfix126_48 hinj126_48 hcardT126_48
      (fun i => conj_mem_of_fixedPoints _ _ (T126_48 i) (hfix126_48 i) _)
      ⟨126, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 15 hp) Q2.T126_48_2 Q2.hfix126_48_2 Q2.hinj126_48_2
      Q2.hcardT126_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_48_2 i) (Q2.hfix126_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨126, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T126_48 = colFn colCertDiv_126_48_15.D1 (m := 5) from colCertDiv_126_48_15.bind1,
    show colData2 (⟨126, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 15 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T126_48_2 = colFn colCertDiv_126_48_15.D2 (m := 5) from colCertDiv_126_48_15.bind2]
  rw [alnId_126 j hj]
  exact fastcode_of_div ⟨126, by decide⟩ _ _ _
    ((alnId_126 j hj) ▸ Q2.listedAt (⟨126, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨126, by decide⟩ : Fin 148) hj hq).1) colCertDiv_126_48_15_match


theorem leaf_126_48_20 (hp : 20 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 20 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨126, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp)) T126_48
      hfix126_48 hinj126_48 hcardT126_48
      (fun i => conj_mem_of_fixedPoints _ _ (T126_48 i) (hfix126_48 i) _)
      ⟨126, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 20 hp) Q2.T126_48_2 Q2.hfix126_48_2 Q2.hinj126_48_2
      Q2.hcardT126_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_48_2 i) (Q2.hfix126_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨126, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T126_48 = colFn colCertDiv_126_48_20.D1 (m := 5) from colCertDiv_126_48_20.bind1,
    show colData2 (⟨126, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 20 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T126_48_2 = colFn colCertDiv_126_48_20.D2 (m := 5) from colCertDiv_126_48_20.bind2]
  rw [alnId_126 j hj]
  exact fastcode_of_div ⟨126, by decide⟩ _ _ _
    ((alnId_126 j hj) ▸ Q2.listedAt (⟨126, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨126, by decide⟩ : Fin 148) hj hq).1) colCertDiv_126_48_20_match


theorem leaf_126_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T126_53
      hfix126_53 hinj126_53 hcardT126_53
      (fun i => conj_mem_of_fixedPoints _ _ (T126_53 i) (hfix126_53 i) _)
      ⟨126, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T126_53_2 Q2.hfix126_53_2 Q2.hinj126_53_2
      Q2.hcardT126_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_53_2 i) (Q2.hfix126_53_2 i) _)
      colCert_126_53_0.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T126_53
      hfix126_53 hinj126_53 hcardT126_53
      (fun i => conj_mem_of_fixedPoints _ _ (T126_53 i) (hfix126_53 i) _)
      ⟨126, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T126_53_2 Q2.hfix126_53_2 Q2.hinj126_53_2
      Q2.hcardT126_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_53_2 i) (Q2.hfix126_53_2 i) _)
      colCert_126_53_1.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T126_53
      hfix126_53 hinj126_53 hcardT126_53
      (fun i => conj_mem_of_fixedPoints _ _ (T126_53 i) (hfix126_53 i) _)
      ⟨126, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T126_53_2 Q2.hfix126_53_2 Q2.hinj126_53_2
      Q2.hcardT126_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_53_2 i) (Q2.hfix126_53_2 i) _)
      colCert_126_53_2.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T126_53
      hfix126_53 hinj126_53 hcardT126_53
      (fun i => conj_mem_of_fixedPoints _ _ (T126_53 i) (hfix126_53 i) _)
      ⟨126, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T126_53_2 Q2.hfix126_53_2 Q2.hinj126_53_2
      Q2.hcardT126_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_53_2 i) (Q2.hfix126_53_2 i) _)
      colCert_126_53_3.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T126_53
      hfix126_53 hinj126_53 hcardT126_53
      (fun i => conj_mem_of_fixedPoints _ _ (T126_53 i) (hfix126_53 i) _)
      ⟨126, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T126_53_2 Q2.hfix126_53_2 Q2.hinj126_53_2
      Q2.hcardT126_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_53_2 i) (Q2.hfix126_53_2 i) _)
      colCert_126_53_4.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T126_53
      hfix126_53 hinj126_53 hcardT126_53
      (fun i => conj_mem_of_fixedPoints _ _ (T126_53 i) (hfix126_53 i) _)
      ⟨126, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T126_53_2 Q2.hfix126_53_2 Q2.hinj126_53_2
      Q2.hcardT126_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_53_2 i) (Q2.hfix126_53_2 i) _)
      colCert_126_53_5.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T126_53
      hfix126_53 hinj126_53 hcardT126_53
      (fun i => conj_mem_of_fixedPoints _ _ (T126_53 i) (hfix126_53 i) _)
      ⟨126, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T126_53_2 Q2.hfix126_53_2 Q2.hinj126_53_2
      Q2.hcardT126_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_53_2 i) (Q2.hfix126_53_2 i) _)
      colCert_126_53_10.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T126_53
      hfix126_53 hinj126_53 hcardT126_53
      (fun i => conj_mem_of_fixedPoints _ _ (T126_53 i) (hfix126_53 i) _)
      ⟨126, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T126_53_2 Q2.hfix126_53_2 Q2.hinj126_53_2
      Q2.hcardT126_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_53_2 i) (Q2.hfix126_53_2 i) _)
      colCert_126_53_15.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T126_53
      hfix126_53 hinj126_53 hcardT126_53
      (fun i => conj_mem_of_fixedPoints _ _ (T126_53 i) (hfix126_53 i) _)
      ⟨126, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T126_53_2 Q2.hfix126_53_2 Q2.hinj126_53_2
      Q2.hcardT126_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_53_2 i) (Q2.hfix126_53_2 i) _)
      colCert_126_53_20.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_82_0 (hp : 0 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 0 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 0 (transLenTr ⟨82, by decide⟩ 0 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 0 (transLenTr ⟨82, by decide⟩ 0 hp)) T126_82
      hfix126_82 hinj126_82 hcardT126_82
      (fun i => conj_mem_of_fixedPoints _ _ (T126_82 i) (hfix126_82 i) _)
      ⟨126, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 0 hp) Q2.T126_82_2 Q2.hfix126_82_2 Q2.hinj126_82_2
      Q2.hcardT126_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_82_2 i) (Q2.hfix126_82_2 i) _)
      colCert_126_82_0.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_82_1 (hp : 1 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 1 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 1 (transLenTr ⟨82, by decide⟩ 1 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 1 (transLenTr ⟨82, by decide⟩ 1 hp)) T126_82
      hfix126_82 hinj126_82 hcardT126_82
      (fun i => conj_mem_of_fixedPoints _ _ (T126_82 i) (hfix126_82 i) _)
      ⟨126, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 1 hp) Q2.T126_82_2 Q2.hfix126_82_2 Q2.hinj126_82_2
      Q2.hcardT126_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_82_2 i) (Q2.hfix126_82_2 i) _)
      colCert_126_82_1.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_82_2 (hp : 2 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 2 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 2 (transLenTr ⟨82, by decide⟩ 2 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 2 (transLenTr ⟨82, by decide⟩ 2 hp)) T126_82
      hfix126_82 hinj126_82 hcardT126_82
      (fun i => conj_mem_of_fixedPoints _ _ (T126_82 i) (hfix126_82 i) _)
      ⟨126, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 2 hp) Q2.T126_82_2 Q2.hfix126_82_2 Q2.hinj126_82_2
      Q2.hcardT126_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_82_2 i) (Q2.hfix126_82_2 i) _)
      colCert_126_82_2.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_82_3 (hp : 3 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 3 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 3 (transLenTr ⟨82, by decide⟩ 3 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 3 (transLenTr ⟨82, by decide⟩ 3 hp)) T126_82
      hfix126_82 hinj126_82 hcardT126_82
      (fun i => conj_mem_of_fixedPoints _ _ (T126_82 i) (hfix126_82 i) _)
      ⟨126, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 3 hp) Q2.T126_82_2 Q2.hfix126_82_2 Q2.hinj126_82_2
      Q2.hcardT126_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_82_2 i) (Q2.hfix126_82_2 i) _)
      colCert_126_82_3.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_82_4 (hp : 4 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 4 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 4 (transLenTr ⟨82, by decide⟩ 4 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 4 (transLenTr ⟨82, by decide⟩ 4 hp)) T126_82
      hfix126_82 hinj126_82 hcardT126_82
      (fun i => conj_mem_of_fixedPoints _ _ (T126_82 i) (hfix126_82 i) _)
      ⟨126, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 4 hp) Q2.T126_82_2 Q2.hfix126_82_2 Q2.hinj126_82_2
      Q2.hcardT126_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_82_2 i) (Q2.hfix126_82_2 i) _)
      colCert_126_82_4.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_82_5 (hp : 5 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 5 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 5 (transLenTr ⟨82, by decide⟩ 5 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 5 (transLenTr ⟨82, by decide⟩ 5 hp)) T126_82
      hfix126_82 hinj126_82 hcardT126_82
      (fun i => conj_mem_of_fixedPoints _ _ (T126_82 i) (hfix126_82 i) _)
      ⟨126, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 5 hp) Q2.T126_82_2 Q2.hfix126_82_2 Q2.hinj126_82_2
      Q2.hcardT126_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_82_2 i) (Q2.hfix126_82_2 i) _)
      colCert_126_82_5.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_82_10 (hp : 10 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 10 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 10 (transLenTr ⟨82, by decide⟩ 10 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 10 (transLenTr ⟨82, by decide⟩ 10 hp)) T126_82
      hfix126_82 hinj126_82 hcardT126_82
      (fun i => conj_mem_of_fixedPoints _ _ (T126_82 i) (hfix126_82 i) _)
      ⟨126, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 10 hp) Q2.T126_82_2 Q2.hfix126_82_2 Q2.hinj126_82_2
      Q2.hcardT126_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_82_2 i) (Q2.hfix126_82_2 i) _)
      colCert_126_82_10.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_82_15 (hp : 15 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 15 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 15 (transLenTr ⟨82, by decide⟩ 15 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 15 (transLenTr ⟨82, by decide⟩ 15 hp)) T126_82
      hfix126_82 hinj126_82 hcardT126_82
      (fun i => conj_mem_of_fixedPoints _ _ (T126_82 i) (hfix126_82 i) _)
      ⟨126, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 15 hp) Q2.T126_82_2 Q2.hfix126_82_2 Q2.hinj126_82_2
      Q2.hcardT126_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_82_2 i) (Q2.hfix126_82_2 i) _)
      colCert_126_82_15.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_82_20 (hp : 20 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 20 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 20 (transLenTr ⟨82, by decide⟩ 20 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 20 (transLenTr ⟨82, by decide⟩ 20 hp)) T126_82
      hfix126_82 hinj126_82 hcardT126_82
      (fun i => conj_mem_of_fixedPoints _ _ (T126_82 i) (hfix126_82 i) _)
      ⟨126, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 20 hp) Q2.T126_82_2 Q2.hfix126_82_2 Q2.hinj126_82_2
      Q2.hcardT126_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_82_2 i) (Q2.hfix126_82_2 i) _)
      colCert_126_82_20.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_93_0 (hp : 0 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 0 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 0 (transLenTr ⟨93, by decide⟩ 0 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 0 (transLenTr ⟨93, by decide⟩ 0 hp)) T126_93
      hfix126_93 hinj126_93 hcardT126_93
      (fun i => conj_mem_of_fixedPoints _ _ (T126_93 i) (hfix126_93 i) _)
      ⟨126, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 0 hp) Q2.T126_93_2 Q2.hfix126_93_2 Q2.hinj126_93_2
      Q2.hcardT126_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_93_2 i) (Q2.hfix126_93_2 i) _)
      colCert_126_93_0.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_93_1 (hp : 1 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 1 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 1 (transLenTr ⟨93, by decide⟩ 1 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 1 (transLenTr ⟨93, by decide⟩ 1 hp)) T126_93
      hfix126_93 hinj126_93 hcardT126_93
      (fun i => conj_mem_of_fixedPoints _ _ (T126_93 i) (hfix126_93 i) _)
      ⟨126, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 1 hp) Q2.T126_93_2 Q2.hfix126_93_2 Q2.hinj126_93_2
      Q2.hcardT126_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_93_2 i) (Q2.hfix126_93_2 i) _)
      colCert_126_93_1.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_93_2 (hp : 2 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 2 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 2 (transLenTr ⟨93, by decide⟩ 2 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 2 (transLenTr ⟨93, by decide⟩ 2 hp)) T126_93
      hfix126_93 hinj126_93 hcardT126_93
      (fun i => conj_mem_of_fixedPoints _ _ (T126_93 i) (hfix126_93 i) _)
      ⟨126, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 2 hp) Q2.T126_93_2 Q2.hfix126_93_2 Q2.hinj126_93_2
      Q2.hcardT126_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_93_2 i) (Q2.hfix126_93_2 i) _)
      colCert_126_93_2.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_93_3 (hp : 3 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 3 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 3 (transLenTr ⟨93, by decide⟩ 3 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 3 (transLenTr ⟨93, by decide⟩ 3 hp)) T126_93
      hfix126_93 hinj126_93 hcardT126_93
      (fun i => conj_mem_of_fixedPoints _ _ (T126_93 i) (hfix126_93 i) _)
      ⟨126, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 3 hp) Q2.T126_93_2 Q2.hfix126_93_2 Q2.hinj126_93_2
      Q2.hcardT126_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_93_2 i) (Q2.hfix126_93_2 i) _)
      colCert_126_93_3.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_93_4 (hp : 4 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 4 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 4 (transLenTr ⟨93, by decide⟩ 4 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 4 (transLenTr ⟨93, by decide⟩ 4 hp)) T126_93
      hfix126_93 hinj126_93 hcardT126_93
      (fun i => conj_mem_of_fixedPoints _ _ (T126_93 i) (hfix126_93 i) _)
      ⟨126, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 4 hp) Q2.T126_93_2 Q2.hfix126_93_2 Q2.hinj126_93_2
      Q2.hcardT126_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_93_2 i) (Q2.hfix126_93_2 i) _)
      colCert_126_93_4.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_93_5 (hp : 5 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 5 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 5 (transLenTr ⟨93, by decide⟩ 5 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 5 (transLenTr ⟨93, by decide⟩ 5 hp)) T126_93
      hfix126_93 hinj126_93 hcardT126_93
      (fun i => conj_mem_of_fixedPoints _ _ (T126_93 i) (hfix126_93 i) _)
      ⟨126, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 5 hp) Q2.T126_93_2 Q2.hfix126_93_2 Q2.hinj126_93_2
      Q2.hcardT126_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_93_2 i) (Q2.hfix126_93_2 i) _)
      colCert_126_93_5.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_93_10 (hp : 10 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 10 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 10 (transLenTr ⟨93, by decide⟩ 10 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨126, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 10 (transLenTr ⟨93, by decide⟩ 10 hp)) T126_93
      hfix126_93 hinj126_93 hcardT126_93
      (fun i => conj_mem_of_fixedPoints _ _ (T126_93 i) (hfix126_93 i) _)
      ⟨126, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 10 hp) Q2.T126_93_2 Q2.hfix126_93_2 Q2.hinj126_93_2
      Q2.hcardT126_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_93_2 i) (Q2.hfix126_93_2 i) _)
      ?_).symm
  rw [show colData1 (⟨126, by decide⟩ : Fin 148)
        ((colE1 ⟨93, by decide⟩ 10 (transLenTr ⟨93, by decide⟩ 10 hp) : ↥(reps ⟨93, by decide⟩)) : Coordinate 1)
        T126_93 = colFn colCertDiv_126_93_10.D1 (m := 5) from colCertDiv_126_93_10.bind1,
    show colData2 (⟨126, by decide⟩ : Fin 148)
        ((colE2 ⟨93, by decide⟩ 10 hp : ↥(Q2.reps ⟨93, by decide⟩)) : Coordinate 2)
        Q2.T126_93_2 = colFn colCertDiv_126_93_10.D2 (m := 5) from colCertDiv_126_93_10.bind2]
  rw [alnId_126 j hj]
  exact fastcode_of_div ⟨126, by decide⟩ _ _ _
    ((alnId_126 j hj) ▸ Q2.listedAt (⟨126, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨126, by decide⟩ : Fin 148) hj hq).1) colCertDiv_126_93_10_match


theorem leaf_126_93_15 (hp : 15 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 15 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 15 (transLenTr ⟨93, by decide⟩ 15 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨126, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 15 (transLenTr ⟨93, by decide⟩ 15 hp)) T126_93
      hfix126_93 hinj126_93 hcardT126_93
      (fun i => conj_mem_of_fixedPoints _ _ (T126_93 i) (hfix126_93 i) _)
      ⟨126, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 15 hp) Q2.T126_93_2 Q2.hfix126_93_2 Q2.hinj126_93_2
      Q2.hcardT126_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_93_2 i) (Q2.hfix126_93_2 i) _)
      ?_).symm
  rw [show colData1 (⟨126, by decide⟩ : Fin 148)
        ((colE1 ⟨93, by decide⟩ 15 (transLenTr ⟨93, by decide⟩ 15 hp) : ↥(reps ⟨93, by decide⟩)) : Coordinate 1)
        T126_93 = colFn colCertDiv_126_93_15.D1 (m := 5) from colCertDiv_126_93_15.bind1,
    show colData2 (⟨126, by decide⟩ : Fin 148)
        ((colE2 ⟨93, by decide⟩ 15 hp : ↥(Q2.reps ⟨93, by decide⟩)) : Coordinate 2)
        Q2.T126_93_2 = colFn colCertDiv_126_93_15.D2 (m := 5) from colCertDiv_126_93_15.bind2]
  rw [alnId_126 j hj]
  exact fastcode_of_div ⟨126, by decide⟩ _ _ _
    ((alnId_126 j hj) ▸ Q2.listedAt (⟨126, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨126, by decide⟩ : Fin 148) hj hq).1) colCertDiv_126_93_15_match


theorem leaf_126_93_20 (hp : 20 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 20 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 20 (transLenTr ⟨93, by decide⟩ 20 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨126, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 20 (transLenTr ⟨93, by decide⟩ 20 hp)) T126_93
      hfix126_93 hinj126_93 hcardT126_93
      (fun i => conj_mem_of_fixedPoints _ _ (T126_93 i) (hfix126_93 i) _)
      ⟨126, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 20 hp) Q2.T126_93_2 Q2.hfix126_93_2 Q2.hinj126_93_2
      Q2.hcardT126_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_93_2 i) (Q2.hfix126_93_2 i) _)
      ?_).symm
  rw [show colData1 (⟨126, by decide⟩ : Fin 148)
        ((colE1 ⟨93, by decide⟩ 20 (transLenTr ⟨93, by decide⟩ 20 hp) : ↥(reps ⟨93, by decide⟩)) : Coordinate 1)
        T126_93 = colFn colCertDiv_126_93_20.D1 (m := 5) from colCertDiv_126_93_20.bind1,
    show colData2 (⟨126, by decide⟩ : Fin 148)
        ((colE2 ⟨93, by decide⟩ 20 hp : ↥(Q2.reps ⟨93, by decide⟩)) : Coordinate 2)
        Q2.T126_93_2 = colFn colCertDiv_126_93_20.D2 (m := 5) from colCertDiv_126_93_20.bind2]
  rw [alnId_126 j hj]
  exact fastcode_of_div ⟨126, by decide⟩ _ _ _
    ((alnId_126 j hj) ▸ Q2.listedAt (⟨126, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨126, by decide⟩ : Fin 148) hj hq).1) colCertDiv_126_93_20_match


theorem leaf_126_99_0 (hp : 0 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 0 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 0 (transLenTr ⟨99, by decide⟩ 0 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 0 (transLenTr ⟨99, by decide⟩ 0 hp)) T126_99
      hfix126_99 hinj126_99 hcardT126_99
      (fun i => conj_mem_of_fixedPoints _ _ (T126_99 i) (hfix126_99 i) _)
      ⟨126, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 0 hp) Q2.T126_99_2 Q2.hfix126_99_2 Q2.hinj126_99_2
      Q2.hcardT126_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_99_2 i) (Q2.hfix126_99_2 i) _)
      colCert_126_99_0.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_99_1 (hp : 1 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 1 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 1 (transLenTr ⟨99, by decide⟩ 1 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 1 (transLenTr ⟨99, by decide⟩ 1 hp)) T126_99
      hfix126_99 hinj126_99 hcardT126_99
      (fun i => conj_mem_of_fixedPoints _ _ (T126_99 i) (hfix126_99 i) _)
      ⟨126, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 1 hp) Q2.T126_99_2 Q2.hfix126_99_2 Q2.hinj126_99_2
      Q2.hcardT126_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_99_2 i) (Q2.hfix126_99_2 i) _)
      colCert_126_99_1.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_99_2 (hp : 2 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 2 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 2 (transLenTr ⟨99, by decide⟩ 2 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 2 (transLenTr ⟨99, by decide⟩ 2 hp)) T126_99
      hfix126_99 hinj126_99 hcardT126_99
      (fun i => conj_mem_of_fixedPoints _ _ (T126_99 i) (hfix126_99 i) _)
      ⟨126, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 2 hp) Q2.T126_99_2 Q2.hfix126_99_2 Q2.hinj126_99_2
      Q2.hcardT126_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_99_2 i) (Q2.hfix126_99_2 i) _)
      colCert_126_99_2.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_99_3 (hp : 3 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 3 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 3 (transLenTr ⟨99, by decide⟩ 3 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 3 (transLenTr ⟨99, by decide⟩ 3 hp)) T126_99
      hfix126_99 hinj126_99 hcardT126_99
      (fun i => conj_mem_of_fixedPoints _ _ (T126_99 i) (hfix126_99 i) _)
      ⟨126, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 3 hp) Q2.T126_99_2 Q2.hfix126_99_2 Q2.hinj126_99_2
      Q2.hcardT126_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_99_2 i) (Q2.hfix126_99_2 i) _)
      colCert_126_99_3.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_99_4 (hp : 4 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 4 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 4 (transLenTr ⟨99, by decide⟩ 4 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 4 (transLenTr ⟨99, by decide⟩ 4 hp)) T126_99
      hfix126_99 hinj126_99 hcardT126_99
      (fun i => conj_mem_of_fixedPoints _ _ (T126_99 i) (hfix126_99 i) _)
      ⟨126, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 4 hp) Q2.T126_99_2 Q2.hfix126_99_2 Q2.hinj126_99_2
      Q2.hcardT126_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_99_2 i) (Q2.hfix126_99_2 i) _)
      colCert_126_99_4.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_99_5 (hp : 5 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 5 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 5 (transLenTr ⟨99, by decide⟩ 5 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 5 (transLenTr ⟨99, by decide⟩ 5 hp)) T126_99
      hfix126_99 hinj126_99 hcardT126_99
      (fun i => conj_mem_of_fixedPoints _ _ (T126_99 i) (hfix126_99 i) _)
      ⟨126, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 5 hp) Q2.T126_99_2 Q2.hfix126_99_2 Q2.hinj126_99_2
      Q2.hcardT126_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_99_2 i) (Q2.hfix126_99_2 i) _)
      colCert_126_99_5.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_99_10 (hp : 10 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 10 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 10 (transLenTr ⟨99, by decide⟩ 10 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 10 (transLenTr ⟨99, by decide⟩ 10 hp)) T126_99
      hfix126_99 hinj126_99 hcardT126_99
      (fun i => conj_mem_of_fixedPoints _ _ (T126_99 i) (hfix126_99 i) _)
      ⟨126, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 10 hp) Q2.T126_99_2 Q2.hfix126_99_2 Q2.hinj126_99_2
      Q2.hcardT126_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_99_2 i) (Q2.hfix126_99_2 i) _)
      colCert_126_99_10.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_99_15 (hp : 15 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 15 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 15 (transLenTr ⟨99, by decide⟩ 15 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 15 (transLenTr ⟨99, by decide⟩ 15 hp)) T126_99
      hfix126_99 hinj126_99 hcardT126_99
      (fun i => conj_mem_of_fixedPoints _ _ (T126_99 i) (hfix126_99 i) _)
      ⟨126, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 15 hp) Q2.T126_99_2 Q2.hfix126_99_2 Q2.hinj126_99_2
      Q2.hcardT126_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_99_2 i) (Q2.hfix126_99_2 i) _)
      colCert_126_99_15.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_99_20 (hp : 20 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 20 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 20 (transLenTr ⟨99, by decide⟩ 20 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 20 (transLenTr ⟨99, by decide⟩ 20 hp)) T126_99
      hfix126_99 hinj126_99 hcardT126_99
      (fun i => conj_mem_of_fixedPoints _ _ (T126_99 i) (hfix126_99 i) _)
      ⟨126, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 20 hp) Q2.T126_99_2 Q2.hfix126_99_2 Q2.hinj126_99_2
      Q2.hcardT126_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_99_2 i) (Q2.hfix126_99_2 i) _)
      colCert_126_99_20.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_101_0 (hp : 0 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 0 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 0 (transLenTr ⟨101, by decide⟩ 0 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 0 (transLenTr ⟨101, by decide⟩ 0 hp)) T126_101
      hfix126_101 hinj126_101 hcardT126_101
      (fun i => conj_mem_of_fixedPoints _ _ (T126_101 i) (hfix126_101 i) _)
      ⟨126, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 0 hp) Q2.T126_101_2 Q2.hfix126_101_2 Q2.hinj126_101_2
      Q2.hcardT126_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_101_2 i) (Q2.hfix126_101_2 i) _)
      colCert_126_101_0.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_101_1 (hp : 1 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 1 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 1 (transLenTr ⟨101, by decide⟩ 1 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 1 (transLenTr ⟨101, by decide⟩ 1 hp)) T126_101
      hfix126_101 hinj126_101 hcardT126_101
      (fun i => conj_mem_of_fixedPoints _ _ (T126_101 i) (hfix126_101 i) _)
      ⟨126, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 1 hp) Q2.T126_101_2 Q2.hfix126_101_2 Q2.hinj126_101_2
      Q2.hcardT126_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_101_2 i) (Q2.hfix126_101_2 i) _)
      colCert_126_101_1.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_101_2 (hp : 2 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 2 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 2 (transLenTr ⟨101, by decide⟩ 2 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 2 (transLenTr ⟨101, by decide⟩ 2 hp)) T126_101
      hfix126_101 hinj126_101 hcardT126_101
      (fun i => conj_mem_of_fixedPoints _ _ (T126_101 i) (hfix126_101 i) _)
      ⟨126, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 2 hp) Q2.T126_101_2 Q2.hfix126_101_2 Q2.hinj126_101_2
      Q2.hcardT126_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_101_2 i) (Q2.hfix126_101_2 i) _)
      colCert_126_101_2.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_101_3 (hp : 3 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 3 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 3 (transLenTr ⟨101, by decide⟩ 3 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 3 (transLenTr ⟨101, by decide⟩ 3 hp)) T126_101
      hfix126_101 hinj126_101 hcardT126_101
      (fun i => conj_mem_of_fixedPoints _ _ (T126_101 i) (hfix126_101 i) _)
      ⟨126, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 3 hp) Q2.T126_101_2 Q2.hfix126_101_2 Q2.hinj126_101_2
      Q2.hcardT126_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_101_2 i) (Q2.hfix126_101_2 i) _)
      colCert_126_101_3.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_101_4 (hp : 4 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 4 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 4 (transLenTr ⟨101, by decide⟩ 4 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 4 (transLenTr ⟨101, by decide⟩ 4 hp)) T126_101
      hfix126_101 hinj126_101 hcardT126_101
      (fun i => conj_mem_of_fixedPoints _ _ (T126_101 i) (hfix126_101 i) _)
      ⟨126, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 4 hp) Q2.T126_101_2 Q2.hfix126_101_2 Q2.hinj126_101_2
      Q2.hcardT126_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_101_2 i) (Q2.hfix126_101_2 i) _)
      colCert_126_101_4.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_101_5 (hp : 5 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 5 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 5 (transLenTr ⟨101, by decide⟩ 5 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 5 (transLenTr ⟨101, by decide⟩ 5 hp)) T126_101
      hfix126_101 hinj126_101 hcardT126_101
      (fun i => conj_mem_of_fixedPoints _ _ (T126_101 i) (hfix126_101 i) _)
      ⟨126, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 5 hp) Q2.T126_101_2 Q2.hfix126_101_2 Q2.hinj126_101_2
      Q2.hcardT126_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_101_2 i) (Q2.hfix126_101_2 i) _)
      colCert_126_101_5.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_101_10 (hp : 10 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 10 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 10 (transLenTr ⟨101, by decide⟩ 10 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨126, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 10 (transLenTr ⟨101, by decide⟩ 10 hp)) T126_101
      hfix126_101 hinj126_101 hcardT126_101
      (fun i => conj_mem_of_fixedPoints _ _ (T126_101 i) (hfix126_101 i) _)
      ⟨126, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 10 hp) Q2.T126_101_2 Q2.hfix126_101_2 Q2.hinj126_101_2
      Q2.hcardT126_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_101_2 i) (Q2.hfix126_101_2 i) _)
      ?_).symm
  rw [show colData1 (⟨126, by decide⟩ : Fin 148)
        ((colE1 ⟨101, by decide⟩ 10 (transLenTr ⟨101, by decide⟩ 10 hp) : ↥(reps ⟨101, by decide⟩)) : Coordinate 1)
        T126_101 = colFn colCertDiv_126_101_10.D1 (m := 5) from colCertDiv_126_101_10.bind1,
    show colData2 (⟨126, by decide⟩ : Fin 148)
        ((colE2 ⟨101, by decide⟩ 10 hp : ↥(Q2.reps ⟨101, by decide⟩)) : Coordinate 2)
        Q2.T126_101_2 = colFn colCertDiv_126_101_10.D2 (m := 5) from colCertDiv_126_101_10.bind2]
  rw [alnId_126 j hj]
  exact fastcode_of_div ⟨126, by decide⟩ _ _ _
    ((alnId_126 j hj) ▸ Q2.listedAt (⟨126, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨126, by decide⟩ : Fin 148) hj hq).1) colCertDiv_126_101_10_match


theorem leaf_126_101_15 (hp : 15 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 15 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 15 (transLenTr ⟨101, by decide⟩ 15 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨126, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 15 (transLenTr ⟨101, by decide⟩ 15 hp)) T126_101
      hfix126_101 hinj126_101 hcardT126_101
      (fun i => conj_mem_of_fixedPoints _ _ (T126_101 i) (hfix126_101 i) _)
      ⟨126, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 15 hp) Q2.T126_101_2 Q2.hfix126_101_2 Q2.hinj126_101_2
      Q2.hcardT126_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_101_2 i) (Q2.hfix126_101_2 i) _)
      ?_).symm
  rw [show colData1 (⟨126, by decide⟩ : Fin 148)
        ((colE1 ⟨101, by decide⟩ 15 (transLenTr ⟨101, by decide⟩ 15 hp) : ↥(reps ⟨101, by decide⟩)) : Coordinate 1)
        T126_101 = colFn colCertDiv_126_101_15.D1 (m := 5) from colCertDiv_126_101_15.bind1,
    show colData2 (⟨126, by decide⟩ : Fin 148)
        ((colE2 ⟨101, by decide⟩ 15 hp : ↥(Q2.reps ⟨101, by decide⟩)) : Coordinate 2)
        Q2.T126_101_2 = colFn colCertDiv_126_101_15.D2 (m := 5) from colCertDiv_126_101_15.bind2]
  rw [alnId_126 j hj]
  exact fastcode_of_div ⟨126, by decide⟩ _ _ _
    ((alnId_126 j hj) ▸ Q2.listedAt (⟨126, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨126, by decide⟩ : Fin 148) hj hq).1) colCertDiv_126_101_15_match


theorem leaf_126_101_20 (hp : 20 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 20 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 20 (transLenTr ⟨101, by decide⟩ 20 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨126, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 20 (transLenTr ⟨101, by decide⟩ 20 hp)) T126_101
      hfix126_101 hinj126_101 hcardT126_101
      (fun i => conj_mem_of_fixedPoints _ _ (T126_101 i) (hfix126_101 i) _)
      ⟨126, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 20 hp) Q2.T126_101_2 Q2.hfix126_101_2 Q2.hinj126_101_2
      Q2.hcardT126_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_101_2 i) (Q2.hfix126_101_2 i) _)
      ?_).symm
  rw [show colData1 (⟨126, by decide⟩ : Fin 148)
        ((colE1 ⟨101, by decide⟩ 20 (transLenTr ⟨101, by decide⟩ 20 hp) : ↥(reps ⟨101, by decide⟩)) : Coordinate 1)
        T126_101 = colFn colCertDiv_126_101_20.D1 (m := 5) from colCertDiv_126_101_20.bind1,
    show colData2 (⟨126, by decide⟩ : Fin 148)
        ((colE2 ⟨101, by decide⟩ 20 hp : ↥(Q2.reps ⟨101, by decide⟩)) : Coordinate 2)
        Q2.T126_101_2 = colFn colCertDiv_126_101_20.D2 (m := 5) from colCertDiv_126_101_20.bind2]
  rw [alnId_126 j hj]
  exact fastcode_of_div ⟨126, by decide⟩ _ _ _
    ((alnId_126 j hj) ▸ Q2.listedAt (⟨126, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨126, by decide⟩ : Fin 148) hj hq).1) colCertDiv_126_101_20_match


theorem leaf_126_107_0 (hp : 0 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 0 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 0 (transLenTr ⟨107, by decide⟩ 0 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 0 (transLenTr ⟨107, by decide⟩ 0 hp)) T126_107
      hfix126_107 hinj126_107 hcardT126_107
      (fun i => conj_mem_of_fixedPoints _ _ (T126_107 i) (hfix126_107 i) _)
      ⟨126, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 0 hp) Q2.T126_107_2 Q2.hfix126_107_2 Q2.hinj126_107_2
      Q2.hcardT126_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_107_2 i) (Q2.hfix126_107_2 i) _)
      colCert_126_107_0.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_107_1 (hp : 1 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 1 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 1 (transLenTr ⟨107, by decide⟩ 1 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 1 (transLenTr ⟨107, by decide⟩ 1 hp)) T126_107
      hfix126_107 hinj126_107 hcardT126_107
      (fun i => conj_mem_of_fixedPoints _ _ (T126_107 i) (hfix126_107 i) _)
      ⟨126, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 1 hp) Q2.T126_107_2 Q2.hfix126_107_2 Q2.hinj126_107_2
      Q2.hcardT126_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_107_2 i) (Q2.hfix126_107_2 i) _)
      colCert_126_107_1.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_107_2 (hp : 2 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 2 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 2 (transLenTr ⟨107, by decide⟩ 2 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 2 (transLenTr ⟨107, by decide⟩ 2 hp)) T126_107
      hfix126_107 hinj126_107 hcardT126_107
      (fun i => conj_mem_of_fixedPoints _ _ (T126_107 i) (hfix126_107 i) _)
      ⟨126, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 2 hp) Q2.T126_107_2 Q2.hfix126_107_2 Q2.hinj126_107_2
      Q2.hcardT126_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_107_2 i) (Q2.hfix126_107_2 i) _)
      colCert_126_107_2.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_107_3 (hp : 3 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 3 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 3 (transLenTr ⟨107, by decide⟩ 3 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 3 (transLenTr ⟨107, by decide⟩ 3 hp)) T126_107
      hfix126_107 hinj126_107 hcardT126_107
      (fun i => conj_mem_of_fixedPoints _ _ (T126_107 i) (hfix126_107 i) _)
      ⟨126, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 3 hp) Q2.T126_107_2 Q2.hfix126_107_2 Q2.hinj126_107_2
      Q2.hcardT126_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_107_2 i) (Q2.hfix126_107_2 i) _)
      colCert_126_107_3.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_107_4 (hp : 4 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 4 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 4 (transLenTr ⟨107, by decide⟩ 4 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 4 (transLenTr ⟨107, by decide⟩ 4 hp)) T126_107
      hfix126_107 hinj126_107 hcardT126_107
      (fun i => conj_mem_of_fixedPoints _ _ (T126_107 i) (hfix126_107 i) _)
      ⟨126, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 4 hp) Q2.T126_107_2 Q2.hfix126_107_2 Q2.hinj126_107_2
      Q2.hcardT126_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_107_2 i) (Q2.hfix126_107_2 i) _)
      colCert_126_107_4.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_107_5 (hp : 5 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 5 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 5 (transLenTr ⟨107, by decide⟩ 5 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 5 (transLenTr ⟨107, by decide⟩ 5 hp)) T126_107
      hfix126_107 hinj126_107 hcardT126_107
      (fun i => conj_mem_of_fixedPoints _ _ (T126_107 i) (hfix126_107 i) _)
      ⟨126, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 5 hp) Q2.T126_107_2 Q2.hfix126_107_2 Q2.hinj126_107_2
      Q2.hcardT126_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_107_2 i) (Q2.hfix126_107_2 i) _)
      colCert_126_107_5.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_107_10 (hp : 10 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 10 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 10 (transLenTr ⟨107, by decide⟩ 10 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 10 (transLenTr ⟨107, by decide⟩ 10 hp)) T126_107
      hfix126_107 hinj126_107 hcardT126_107
      (fun i => conj_mem_of_fixedPoints _ _ (T126_107 i) (hfix126_107 i) _)
      ⟨126, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 10 hp) Q2.T126_107_2 Q2.hfix126_107_2 Q2.hinj126_107_2
      Q2.hcardT126_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_107_2 i) (Q2.hfix126_107_2 i) _)
      colCert_126_107_10.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_107_15 (hp : 15 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 15 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 15 (transLenTr ⟨107, by decide⟩ 15 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨126, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 15 (transLenTr ⟨107, by decide⟩ 15 hp)) T126_107
      hfix126_107 hinj126_107 hcardT126_107
      (fun i => conj_mem_of_fixedPoints _ _ (T126_107 i) (hfix126_107 i) _)
      ⟨126, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 15 hp) Q2.T126_107_2 Q2.hfix126_107_2 Q2.hinj126_107_2
      Q2.hcardT126_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_107_2 i) (Q2.hfix126_107_2 i) _)
      ?_).symm
  rw [show colData1 (⟨126, by decide⟩ : Fin 148)
        ((colE1 ⟨107, by decide⟩ 15 (transLenTr ⟨107, by decide⟩ 15 hp) : ↥(reps ⟨107, by decide⟩)) : Coordinate 1)
        T126_107 = colFn colCertDiv_126_107_15.D1 (m := 5) from colCertDiv_126_107_15.bind1,
    show colData2 (⟨126, by decide⟩ : Fin 148)
        ((colE2 ⟨107, by decide⟩ 15 hp : ↥(Q2.reps ⟨107, by decide⟩)) : Coordinate 2)
        Q2.T126_107_2 = colFn colCertDiv_126_107_15.D2 (m := 5) from colCertDiv_126_107_15.bind2]
  rw [alnId_126 j hj]
  exact fastcode_of_div ⟨126, by decide⟩ _ _ _
    ((alnId_126 j hj) ▸ Q2.listedAt (⟨126, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨126, by decide⟩ : Fin 148) hj hq).1) colCertDiv_126_107_15_match


theorem leaf_126_107_20 (hp : 20 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 20 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 20 (transLenTr ⟨107, by decide⟩ 20 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨126, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 20 (transLenTr ⟨107, by decide⟩ 20 hp)) T126_107
      hfix126_107 hinj126_107 hcardT126_107
      (fun i => conj_mem_of_fixedPoints _ _ (T126_107 i) (hfix126_107 i) _)
      ⟨126, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 20 hp) Q2.T126_107_2 Q2.hfix126_107_2 Q2.hinj126_107_2
      Q2.hcardT126_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_107_2 i) (Q2.hfix126_107_2 i) _)
      ?_).symm
  rw [show colData1 (⟨126, by decide⟩ : Fin 148)
        ((colE1 ⟨107, by decide⟩ 20 (transLenTr ⟨107, by decide⟩ 20 hp) : ↥(reps ⟨107, by decide⟩)) : Coordinate 1)
        T126_107 = colFn colCertDiv_126_107_20.D1 (m := 5) from colCertDiv_126_107_20.bind1,
    show colData2 (⟨126, by decide⟩ : Fin 148)
        ((colE2 ⟨107, by decide⟩ 20 hp : ↥(Q2.reps ⟨107, by decide⟩)) : Coordinate 2)
        Q2.T126_107_2 = colFn colCertDiv_126_107_20.D2 (m := 5) from colCertDiv_126_107_20.bind2]
  rw [alnId_126 j hj]
  exact fastcode_of_div ⟨126, by decide⟩ _ _ _
    ((alnId_126 j hj) ▸ Q2.listedAt (⟨126, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨126, by decide⟩ : Fin 148) hj hq).1) colCertDiv_126_107_20_match


theorem leaf_126_110_0 (hp : 0 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 0 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 0 (transLenTr ⟨110, by decide⟩ 0 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 0 (transLenTr ⟨110, by decide⟩ 0 hp)) T126_110
      hfix126_110 hinj126_110 hcardT126_110
      (fun i => conj_mem_of_fixedPoints _ _ (T126_110 i) (hfix126_110 i) _)
      ⟨126, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 0 hp) Q2.T126_110_2 Q2.hfix126_110_2 Q2.hinj126_110_2
      Q2.hcardT126_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_110_2 i) (Q2.hfix126_110_2 i) _)
      colCert_126_110_0.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_110_1 (hp : 1 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 1 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 1 (transLenTr ⟨110, by decide⟩ 1 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 1 (transLenTr ⟨110, by decide⟩ 1 hp)) T126_110
      hfix126_110 hinj126_110 hcardT126_110
      (fun i => conj_mem_of_fixedPoints _ _ (T126_110 i) (hfix126_110 i) _)
      ⟨126, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 1 hp) Q2.T126_110_2 Q2.hfix126_110_2 Q2.hinj126_110_2
      Q2.hcardT126_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_110_2 i) (Q2.hfix126_110_2 i) _)
      colCert_126_110_1.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_110_2 (hp : 2 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 2 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 2 (transLenTr ⟨110, by decide⟩ 2 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 2 (transLenTr ⟨110, by decide⟩ 2 hp)) T126_110
      hfix126_110 hinj126_110 hcardT126_110
      (fun i => conj_mem_of_fixedPoints _ _ (T126_110 i) (hfix126_110 i) _)
      ⟨126, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 2 hp) Q2.T126_110_2 Q2.hfix126_110_2 Q2.hinj126_110_2
      Q2.hcardT126_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_110_2 i) (Q2.hfix126_110_2 i) _)
      colCert_126_110_2.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_110_3 (hp : 3 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 3 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 3 (transLenTr ⟨110, by decide⟩ 3 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 3 (transLenTr ⟨110, by decide⟩ 3 hp)) T126_110
      hfix126_110 hinj126_110 hcardT126_110
      (fun i => conj_mem_of_fixedPoints _ _ (T126_110 i) (hfix126_110 i) _)
      ⟨126, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 3 hp) Q2.T126_110_2 Q2.hfix126_110_2 Q2.hinj126_110_2
      Q2.hcardT126_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_110_2 i) (Q2.hfix126_110_2 i) _)
      colCert_126_110_3.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_110_4 (hp : 4 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 4 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 4 (transLenTr ⟨110, by decide⟩ 4 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 4 (transLenTr ⟨110, by decide⟩ 4 hp)) T126_110
      hfix126_110 hinj126_110 hcardT126_110
      (fun i => conj_mem_of_fixedPoints _ _ (T126_110 i) (hfix126_110 i) _)
      ⟨126, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 4 hp) Q2.T126_110_2 Q2.hfix126_110_2 Q2.hinj126_110_2
      Q2.hcardT126_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_110_2 i) (Q2.hfix126_110_2 i) _)
      colCert_126_110_4.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_110_5 (hp : 5 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 5 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 5 (transLenTr ⟨110, by decide⟩ 5 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 5 (transLenTr ⟨110, by decide⟩ 5 hp)) T126_110
      hfix126_110 hinj126_110 hcardT126_110
      (fun i => conj_mem_of_fixedPoints _ _ (T126_110 i) (hfix126_110 i) _)
      ⟨126, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 5 hp) Q2.T126_110_2 Q2.hfix126_110_2 Q2.hinj126_110_2
      Q2.hcardT126_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_110_2 i) (Q2.hfix126_110_2 i) _)
      colCert_126_110_5.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_110_10 (hp : 10 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 10 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 10 (transLenTr ⟨110, by decide⟩ 10 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 10 (transLenTr ⟨110, by decide⟩ 10 hp)) T126_110
      hfix126_110 hinj126_110 hcardT126_110
      (fun i => conj_mem_of_fixedPoints _ _ (T126_110 i) (hfix126_110 i) _)
      ⟨126, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 10 hp) Q2.T126_110_2 Q2.hfix126_110_2 Q2.hinj126_110_2
      Q2.hcardT126_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_110_2 i) (Q2.hfix126_110_2 i) _)
      colCert_126_110_10.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_110_15 (hp : 15 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 15 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 15 (transLenTr ⟨110, by decide⟩ 15 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 15 (transLenTr ⟨110, by decide⟩ 15 hp)) T126_110
      hfix126_110 hinj126_110 hcardT126_110
      (fun i => conj_mem_of_fixedPoints _ _ (T126_110 i) (hfix126_110 i) _)
      ⟨126, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 15 hp) Q2.T126_110_2 Q2.hfix126_110_2 Q2.hinj126_110_2
      Q2.hcardT126_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_110_2 i) (Q2.hfix126_110_2 i) _)
      colCert_126_110_15.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_110_20 (hp : 20 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 20 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 20 (transLenTr ⟨110, by decide⟩ 20 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 20 (transLenTr ⟨110, by decide⟩ 20 hp)) T126_110
      hfix126_110 hinj126_110 hcardT126_110
      (fun i => conj_mem_of_fixedPoints _ _ (T126_110 i) (hfix126_110 i) _)
      ⟨126, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 20 hp) Q2.T126_110_2 Q2.hfix126_110_2 Q2.hinj126_110_2
      Q2.hcardT126_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_110_2 i) (Q2.hfix126_110_2 i) _)
      colCert_126_110_20.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_110_25 (hp : 25 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 25 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 25 (transLenTr ⟨110, by decide⟩ 25 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 25 (transLenTr ⟨110, by decide⟩ 25 hp)) T126_110
      hfix126_110 hinj126_110 hcardT126_110
      (fun i => conj_mem_of_fixedPoints _ _ (T126_110 i) (hfix126_110 i) _)
      ⟨126, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 25 hp) Q2.T126_110_2 Q2.hfix126_110_2 Q2.hinj126_110_2
      Q2.hcardT126_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_110_2 i) (Q2.hfix126_110_2 i) _)
      colCert_126_110_25.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_110_50 (hp : 50 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 50 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 50 (transLenTr ⟨110, by decide⟩ 50 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 50 (transLenTr ⟨110, by decide⟩ 50 hp)) T126_110
      hfix126_110 hinj126_110 hcardT126_110
      (fun i => conj_mem_of_fixedPoints _ _ (T126_110 i) (hfix126_110 i) _)
      ⟨126, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 50 hp) Q2.T126_110_2 Q2.hfix126_110_2 Q2.hinj126_110_2
      Q2.hcardT126_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_110_2 i) (Q2.hfix126_110_2 i) _)
      colCert_126_110_50.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_110_75 (hp : 75 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 75 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 75 (transLenTr ⟨110, by decide⟩ 75 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 75 (transLenTr ⟨110, by decide⟩ 75 hp)) T126_110
      hfix126_110 hinj126_110 hcardT126_110
      (fun i => conj_mem_of_fixedPoints _ _ (T126_110 i) (hfix126_110 i) _)
      ⟨126, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 75 hp) Q2.T126_110_2 Q2.hfix126_110_2 Q2.hinj126_110_2
      Q2.hcardT126_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_110_2 i) (Q2.hfix126_110_2 i) _)
      colCert_126_110_75.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_110_100 (hp : 100 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 100 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 100 (transLenTr ⟨110, by decide⟩ 100 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 100 (transLenTr ⟨110, by decide⟩ 100 hp)) T126_110
      hfix126_110 hinj126_110 hcardT126_110
      (fun i => conj_mem_of_fixedPoints _ _ (T126_110 i) (hfix126_110 i) _)
      ⟨126, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 100 hp) Q2.T126_110_2 Q2.hfix126_110_2 Q2.hinj126_110_2
      Q2.hcardT126_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_110_2 i) (Q2.hfix126_110_2 i) _)
      colCert_126_110_100.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_126_0 (hp : 0 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 0 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 0 (transLenTr ⟨126, by decide⟩ 0 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 0 (transLenTr ⟨126, by decide⟩ 0 hp)) T126_126
      hfix126_126 hinj126_126 hcardT126_126
      (fun i => conj_mem_of_fixedPoints _ _ (T126_126 i) (hfix126_126 i) _)
      ⟨126, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 0 hp) Q2.T126_126_2 Q2.hfix126_126_2 Q2.hinj126_126_2
      Q2.hcardT126_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_126_2 i) (Q2.hfix126_126_2 i) _)
      colCert_126_126_0.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_126_1 (hp : 1 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 1 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 1 (transLenTr ⟨126, by decide⟩ 1 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 1 (transLenTr ⟨126, by decide⟩ 1 hp)) T126_126
      hfix126_126 hinj126_126 hcardT126_126
      (fun i => conj_mem_of_fixedPoints _ _ (T126_126 i) (hfix126_126 i) _)
      ⟨126, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 1 hp) Q2.T126_126_2 Q2.hfix126_126_2 Q2.hinj126_126_2
      Q2.hcardT126_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_126_2 i) (Q2.hfix126_126_2 i) _)
      colCert_126_126_1.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_126_2 (hp : 2 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 2 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 2 (transLenTr ⟨126, by decide⟩ 2 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 2 (transLenTr ⟨126, by decide⟩ 2 hp)) T126_126
      hfix126_126 hinj126_126 hcardT126_126
      (fun i => conj_mem_of_fixedPoints _ _ (T126_126 i) (hfix126_126 i) _)
      ⟨126, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 2 hp) Q2.T126_126_2 Q2.hfix126_126_2 Q2.hinj126_126_2
      Q2.hcardT126_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_126_2 i) (Q2.hfix126_126_2 i) _)
      colCert_126_126_2.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_126_3 (hp : 3 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 3 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 3 (transLenTr ⟨126, by decide⟩ 3 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 3 (transLenTr ⟨126, by decide⟩ 3 hp)) T126_126
      hfix126_126 hinj126_126 hcardT126_126
      (fun i => conj_mem_of_fixedPoints _ _ (T126_126 i) (hfix126_126 i) _)
      ⟨126, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 3 hp) Q2.T126_126_2 Q2.hfix126_126_2 Q2.hinj126_126_2
      Q2.hcardT126_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_126_2 i) (Q2.hfix126_126_2 i) _)
      colCert_126_126_3.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_126_4 (hp : 4 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 4 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 4 (transLenTr ⟨126, by decide⟩ 4 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 4 (transLenTr ⟨126, by decide⟩ 4 hp)) T126_126
      hfix126_126 hinj126_126 hcardT126_126
      (fun i => conj_mem_of_fixedPoints _ _ (T126_126 i) (hfix126_126 i) _)
      ⟨126, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 4 hp) Q2.T126_126_2 Q2.hfix126_126_2 Q2.hinj126_126_2
      Q2.hcardT126_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_126_2 i) (Q2.hfix126_126_2 i) _)
      colCert_126_126_4.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_126_5 (hp : 5 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 5 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 5 (transLenTr ⟨126, by decide⟩ 5 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 5 (transLenTr ⟨126, by decide⟩ 5 hp)) T126_126
      hfix126_126 hinj126_126 hcardT126_126
      (fun i => conj_mem_of_fixedPoints _ _ (T126_126 i) (hfix126_126 i) _)
      ⟨126, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 5 hp) Q2.T126_126_2 Q2.hfix126_126_2 Q2.hinj126_126_2
      Q2.hcardT126_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_126_2 i) (Q2.hfix126_126_2 i) _)
      colCert_126_126_5.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_126_6 (hp : 6 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 6 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 6 (transLenTr ⟨126, by decide⟩ 6 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 6 (transLenTr ⟨126, by decide⟩ 6 hp)) T126_126
      hfix126_126 hinj126_126 hcardT126_126
      (fun i => conj_mem_of_fixedPoints _ _ (T126_126 i) (hfix126_126 i) _)
      ⟨126, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 6 hp) Q2.T126_126_2 Q2.hfix126_126_2 Q2.hinj126_126_2
      Q2.hcardT126_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_126_2 i) (Q2.hfix126_126_2 i) _)
      colCert_126_126_6.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_126_7 (hp : 7 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 7 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 7 (transLenTr ⟨126, by decide⟩ 7 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 7 (transLenTr ⟨126, by decide⟩ 7 hp)) T126_126
      hfix126_126 hinj126_126 hcardT126_126
      (fun i => conj_mem_of_fixedPoints _ _ (T126_126 i) (hfix126_126 i) _)
      ⟨126, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 7 hp) Q2.T126_126_2 Q2.hfix126_126_2 Q2.hinj126_126_2
      Q2.hcardT126_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_126_2 i) (Q2.hfix126_126_2 i) _)
      colCert_126_126_7.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_126_8 (hp : 8 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 8 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 8 (transLenTr ⟨126, by decide⟩ 8 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 8 (transLenTr ⟨126, by decide⟩ 8 hp)) T126_126
      hfix126_126 hinj126_126 hcardT126_126
      (fun i => conj_mem_of_fixedPoints _ _ (T126_126 i) (hfix126_126 i) _)
      ⟨126, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 8 hp) Q2.T126_126_2 Q2.hfix126_126_2 Q2.hinj126_126_2
      Q2.hcardT126_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_126_2 i) (Q2.hfix126_126_2 i) _)
      colCert_126_126_8.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_126_9 (hp : 9 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 9 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 9 (transLenTr ⟨126, by decide⟩ 9 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 9 (transLenTr ⟨126, by decide⟩ 9 hp)) T126_126
      hfix126_126 hinj126_126 hcardT126_126
      (fun i => conj_mem_of_fixedPoints _ _ (T126_126 i) (hfix126_126 i) _)
      ⟨126, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 9 hp) Q2.T126_126_2 Q2.hfix126_126_2 Q2.hinj126_126_2
      Q2.hcardT126_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_126_2 i) (Q2.hfix126_126_2 i) _)
      colCert_126_126_9.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_126_10 (hp : 10 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 10 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 10 (transLenTr ⟨126, by decide⟩ 10 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 10 (transLenTr ⟨126, by decide⟩ 10 hp)) T126_126
      hfix126_126 hinj126_126 hcardT126_126
      (fun i => conj_mem_of_fixedPoints _ _ (T126_126 i) (hfix126_126 i) _)
      ⟨126, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 10 hp) Q2.T126_126_2 Q2.hfix126_126_2 Q2.hinj126_126_2
      Q2.hcardT126_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_126_2 i) (Q2.hfix126_126_2 i) _)
      colCert_126_126_10.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_126_11 (hp : 11 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 11 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 11 (transLenTr ⟨126, by decide⟩ 11 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 11 (transLenTr ⟨126, by decide⟩ 11 hp)) T126_126
      hfix126_126 hinj126_126 hcardT126_126
      (fun i => conj_mem_of_fixedPoints _ _ (T126_126 i) (hfix126_126 i) _)
      ⟨126, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 11 hp) Q2.T126_126_2 Q2.hfix126_126_2 Q2.hinj126_126_2
      Q2.hcardT126_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_126_2 i) (Q2.hfix126_126_2 i) _)
      colCert_126_126_11.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_126_12 (hp : 12 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 12 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 12 (transLenTr ⟨126, by decide⟩ 12 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 12 (transLenTr ⟨126, by decide⟩ 12 hp)) T126_126
      hfix126_126 hinj126_126 hcardT126_126
      (fun i => conj_mem_of_fixedPoints _ _ (T126_126 i) (hfix126_126 i) _)
      ⟨126, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 12 hp) Q2.T126_126_2 Q2.hfix126_126_2 Q2.hinj126_126_2
      Q2.hcardT126_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_126_2 i) (Q2.hfix126_126_2 i) _)
      colCert_126_126_12.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_126_13 (hp : 13 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 13 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 13 (transLenTr ⟨126, by decide⟩ 13 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 13 (transLenTr ⟨126, by decide⟩ 13 hp)) T126_126
      hfix126_126 hinj126_126 hcardT126_126
      (fun i => conj_mem_of_fixedPoints _ _ (T126_126 i) (hfix126_126 i) _)
      ⟨126, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 13 hp) Q2.T126_126_2 Q2.hfix126_126_2 Q2.hinj126_126_2
      Q2.hcardT126_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_126_2 i) (Q2.hfix126_126_2 i) _)
      colCert_126_126_13.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_126_14 (hp : 14 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 14 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 14 (transLenTr ⟨126, by decide⟩ 14 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 14 (transLenTr ⟨126, by decide⟩ 14 hp)) T126_126
      hfix126_126 hinj126_126 hcardT126_126
      (fun i => conj_mem_of_fixedPoints _ _ (T126_126 i) (hfix126_126 i) _)
      ⟨126, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 14 hp) Q2.T126_126_2 Q2.hfix126_126_2 Q2.hinj126_126_2
      Q2.hcardT126_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_126_2 i) (Q2.hfix126_126_2 i) _)
      colCert_126_126_14.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_126_15 (hp : 15 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 15 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 15 (transLenTr ⟨126, by decide⟩ 15 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 15 (transLenTr ⟨126, by decide⟩ 15 hp)) T126_126
      hfix126_126 hinj126_126 hcardT126_126
      (fun i => conj_mem_of_fixedPoints _ _ (T126_126 i) (hfix126_126 i) _)
      ⟨126, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 15 hp) Q2.T126_126_2 Q2.hfix126_126_2 Q2.hinj126_126_2
      Q2.hcardT126_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_126_2 i) (Q2.hfix126_126_2 i) _)
      colCert_126_126_15.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_126_16 (hp : 16 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 16 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 16 (transLenTr ⟨126, by decide⟩ 16 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 16 (transLenTr ⟨126, by decide⟩ 16 hp)) T126_126
      hfix126_126 hinj126_126 hcardT126_126
      (fun i => conj_mem_of_fixedPoints _ _ (T126_126 i) (hfix126_126 i) _)
      ⟨126, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 16 hp) Q2.T126_126_2 Q2.hfix126_126_2 Q2.hinj126_126_2
      Q2.hcardT126_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_126_2 i) (Q2.hfix126_126_2 i) _)
      colCert_126_126_16.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_126_17 (hp : 17 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 17 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 17 (transLenTr ⟨126, by decide⟩ 17 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 17 (transLenTr ⟨126, by decide⟩ 17 hp)) T126_126
      hfix126_126 hinj126_126 hcardT126_126
      (fun i => conj_mem_of_fixedPoints _ _ (T126_126 i) (hfix126_126 i) _)
      ⟨126, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 17 hp) Q2.T126_126_2 Q2.hfix126_126_2 Q2.hinj126_126_2
      Q2.hcardT126_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_126_2 i) (Q2.hfix126_126_2 i) _)
      colCert_126_126_17.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_126_18 (hp : 18 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 18 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 18 (transLenTr ⟨126, by decide⟩ 18 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 18 (transLenTr ⟨126, by decide⟩ 18 hp)) T126_126
      hfix126_126 hinj126_126 hcardT126_126
      (fun i => conj_mem_of_fixedPoints _ _ (T126_126 i) (hfix126_126 i) _)
      ⟨126, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 18 hp) Q2.T126_126_2 Q2.hfix126_126_2 Q2.hinj126_126_2
      Q2.hcardT126_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_126_2 i) (Q2.hfix126_126_2 i) _)
      colCert_126_126_18.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_126_19 (hp : 19 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 19 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 19 (transLenTr ⟨126, by decide⟩ 19 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 19 (transLenTr ⟨126, by decide⟩ 19 hp)) T126_126
      hfix126_126 hinj126_126 hcardT126_126
      (fun i => conj_mem_of_fixedPoints _ _ (T126_126 i) (hfix126_126 i) _)
      ⟨126, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 19 hp) Q2.T126_126_2 Q2.hfix126_126_2 Q2.hinj126_126_2
      Q2.hcardT126_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_126_2 i) (Q2.hfix126_126_2 i) _)
      colCert_126_126_19.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_126_20 (hp : 20 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 20 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 20 (transLenTr ⟨126, by decide⟩ 20 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 20 (transLenTr ⟨126, by decide⟩ 20 hp)) T126_126
      hfix126_126 hinj126_126 hcardT126_126
      (fun i => conj_mem_of_fixedPoints _ _ (T126_126 i) (hfix126_126 i) _)
      ⟨126, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 20 hp) Q2.T126_126_2 Q2.hfix126_126_2 Q2.hinj126_126_2
      Q2.hcardT126_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_126_2 i) (Q2.hfix126_126_2 i) _)
      colCert_126_126_20.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_126_21 (hp : 21 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 21 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 21 (transLenTr ⟨126, by decide⟩ 21 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 21 (transLenTr ⟨126, by decide⟩ 21 hp)) T126_126
      hfix126_126 hinj126_126 hcardT126_126
      (fun i => conj_mem_of_fixedPoints _ _ (T126_126 i) (hfix126_126 i) _)
      ⟨126, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 21 hp) Q2.T126_126_2 Q2.hfix126_126_2 Q2.hinj126_126_2
      Q2.hcardT126_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_126_2 i) (Q2.hfix126_126_2 i) _)
      colCert_126_126_21.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_126_22 (hp : 22 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 22 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 22 (transLenTr ⟨126, by decide⟩ 22 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 22 (transLenTr ⟨126, by decide⟩ 22 hp)) T126_126
      hfix126_126 hinj126_126 hcardT126_126
      (fun i => conj_mem_of_fixedPoints _ _ (T126_126 i) (hfix126_126 i) _)
      ⟨126, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 22 hp) Q2.T126_126_2 Q2.hfix126_126_2 Q2.hinj126_126_2
      Q2.hcardT126_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_126_2 i) (Q2.hfix126_126_2 i) _)
      colCert_126_126_22.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_126_23 (hp : 23 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 23 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 23 (transLenTr ⟨126, by decide⟩ 23 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 23 (transLenTr ⟨126, by decide⟩ 23 hp)) T126_126
      hfix126_126 hinj126_126 hcardT126_126
      (fun i => conj_mem_of_fixedPoints _ _ (T126_126 i) (hfix126_126 i) _)
      ⟨126, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 23 hp) Q2.T126_126_2 Q2.hfix126_126_2 Q2.hinj126_126_2
      Q2.hcardT126_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_126_2 i) (Q2.hfix126_126_2 i) _)
      colCert_126_126_23.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_126_24 (hp : 24 < (Q2.transData.getD 126 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ 24 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ 24 (transLenTr ⟨126, by decide⟩ 24 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨126, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨126, by decide⟩ 24 (transLenTr ⟨126, by decide⟩ 24 hp)) T126_126
      hfix126_126 hinj126_126 hcardT126_126
      (fun i => conj_mem_of_fixedPoints _ _ (T126_126 i) (hfix126_126 i) _)
      ⟨126, by decide⟩ ⟨126, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨126, by decide⟩ 24 hp) Q2.T126_126_2 Q2.hfix126_126_2 Q2.hinj126_126_2
      Q2.hcardT126_126_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_126_2 i) (Q2.hfix126_126_2 i) _)
      colCert_126_126_24.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_127_3_0 (hp : 0 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 0 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp)) T127_3
      hfix127_3 hinj127_3 hcardT127_3
      (fun i => conj_mem_of_fixedPoints _ _ (T127_3 i) (hfix127_3 i) _)
      ⟨127, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 0 hp) Q2.T127_3_2 Q2.hfix127_3_2 Q2.hinj127_3_2
      Q2.hcardT127_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_3_2 i) (Q2.hfix127_3_2 i) _)
      colCert_127_3_0.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_3_1 (hp : 1 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 1 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp)) T127_3
      hfix127_3 hinj127_3 hcardT127_3
      (fun i => conj_mem_of_fixedPoints _ _ (T127_3 i) (hfix127_3 i) _)
      ⟨127, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 1 hp) Q2.T127_3_2 Q2.hfix127_3_2 Q2.hinj127_3_2
      Q2.hcardT127_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_3_2 i) (Q2.hfix127_3_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp) : ↥(reps ⟨3, by decide⟩)) : Coordinate 1)
        T127_3 = colFn colCertDiv_127_3_1.D1 (m := 5) from colCertDiv_127_3_1.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨3, by decide⟩ 1 hp : ↥(Q2.reps ⟨3, by decide⟩)) : Coordinate 2)
        Q2.T127_3_2 = colFn colCertDiv_127_3_1.D2 (m := 5) from colCertDiv_127_3_1.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_3_1_match


theorem leaf_127_3_2 (hp : 2 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 2 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp)) T127_3
      hfix127_3 hinj127_3 hcardT127_3
      (fun i => conj_mem_of_fixedPoints _ _ (T127_3 i) (hfix127_3 i) _)
      ⟨127, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 2 hp) Q2.T127_3_2 Q2.hfix127_3_2 Q2.hinj127_3_2
      Q2.hcardT127_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_3_2 i) (Q2.hfix127_3_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp) : ↥(reps ⟨3, by decide⟩)) : Coordinate 1)
        T127_3 = colFn colCertDiv_127_3_2.D1 (m := 5) from colCertDiv_127_3_2.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨3, by decide⟩ 2 hp : ↥(Q2.reps ⟨3, by decide⟩)) : Coordinate 2)
        Q2.T127_3_2 = colFn colCertDiv_127_3_2.D2 (m := 5) from colCertDiv_127_3_2.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_3_2_match


theorem leaf_127_3_3 (hp : 3 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 3 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp)) T127_3
      hfix127_3 hinj127_3 hcardT127_3
      (fun i => conj_mem_of_fixedPoints _ _ (T127_3 i) (hfix127_3 i) _)
      ⟨127, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 3 hp) Q2.T127_3_2 Q2.hfix127_3_2 Q2.hinj127_3_2
      Q2.hcardT127_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_3_2 i) (Q2.hfix127_3_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp) : ↥(reps ⟨3, by decide⟩)) : Coordinate 1)
        T127_3 = colFn colCertDiv_127_3_3.D1 (m := 5) from colCertDiv_127_3_3.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨3, by decide⟩ 3 hp : ↥(Q2.reps ⟨3, by decide⟩)) : Coordinate 2)
        Q2.T127_3_2 = colFn colCertDiv_127_3_3.D2 (m := 5) from colCertDiv_127_3_3.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_3_3_match


theorem leaf_127_3_4 (hp : 4 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 4 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp)) T127_3
      hfix127_3 hinj127_3 hcardT127_3
      (fun i => conj_mem_of_fixedPoints _ _ (T127_3 i) (hfix127_3 i) _)
      ⟨127, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 4 hp) Q2.T127_3_2 Q2.hfix127_3_2 Q2.hinj127_3_2
      Q2.hcardT127_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_3_2 i) (Q2.hfix127_3_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp) : ↥(reps ⟨3, by decide⟩)) : Coordinate 1)
        T127_3 = colFn colCertDiv_127_3_4.D1 (m := 5) from colCertDiv_127_3_4.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨3, by decide⟩ 4 hp : ↥(Q2.reps ⟨3, by decide⟩)) : Coordinate 2)
        Q2.T127_3_2 = colFn colCertDiv_127_3_4.D2 (m := 5) from colCertDiv_127_3_4.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_3_4_match


theorem leaf_127_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T127_10
      hfix127_10 hinj127_10 hcardT127_10
      (fun i => conj_mem_of_fixedPoints _ _ (T127_10 i) (hfix127_10 i) _)
      ⟨127, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T127_10_2 Q2.hfix127_10_2 Q2.hinj127_10_2
      Q2.hcardT127_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_10_2 i) (Q2.hfix127_10_2 i) _)
      colCert_127_10_0.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T127_10
      hfix127_10 hinj127_10 hcardT127_10
      (fun i => conj_mem_of_fixedPoints _ _ (T127_10 i) (hfix127_10 i) _)
      ⟨127, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T127_10_2 Q2.hfix127_10_2 Q2.hinj127_10_2
      Q2.hcardT127_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_10_2 i) (Q2.hfix127_10_2 i) _)
      colCert_127_10_1.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T127_10
      hfix127_10 hinj127_10 hcardT127_10
      (fun i => conj_mem_of_fixedPoints _ _ (T127_10 i) (hfix127_10 i) _)
      ⟨127, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T127_10_2 Q2.hfix127_10_2 Q2.hinj127_10_2
      Q2.hcardT127_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_10_2 i) (Q2.hfix127_10_2 i) _)
      colCert_127_10_2.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T127_10
      hfix127_10 hinj127_10 hcardT127_10
      (fun i => conj_mem_of_fixedPoints _ _ (T127_10 i) (hfix127_10 i) _)
      ⟨127, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T127_10_2 Q2.hfix127_10_2 Q2.hinj127_10_2
      Q2.hcardT127_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_10_2 i) (Q2.hfix127_10_2 i) _)
      colCert_127_10_3.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T127_10
      hfix127_10 hinj127_10 hcardT127_10
      (fun i => conj_mem_of_fixedPoints _ _ (T127_10 i) (hfix127_10 i) _)
      ⟨127, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T127_10_2 Q2.hfix127_10_2 Q2.hinj127_10_2
      Q2.hcardT127_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_10_2 i) (Q2.hfix127_10_2 i) _)
      colCert_127_10_4.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T127_12
      hfix127_12 hinj127_12 hcardT127_12
      (fun i => conj_mem_of_fixedPoints _ _ (T127_12 i) (hfix127_12 i) _)
      ⟨127, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T127_12_2 Q2.hfix127_12_2 Q2.hinj127_12_2
      Q2.hcardT127_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_12_2 i) (Q2.hfix127_12_2 i) _)
      colCert_127_12_0.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T127_12
      hfix127_12 hinj127_12 hcardT127_12
      (fun i => conj_mem_of_fixedPoints _ _ (T127_12 i) (hfix127_12 i) _)
      ⟨127, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T127_12_2 Q2.hfix127_12_2 Q2.hinj127_12_2
      Q2.hcardT127_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_12_2 i) (Q2.hfix127_12_2 i) _)
      colCert_127_12_1.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T127_12
      hfix127_12 hinj127_12 hcardT127_12
      (fun i => conj_mem_of_fixedPoints _ _ (T127_12 i) (hfix127_12 i) _)
      ⟨127, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T127_12_2 Q2.hfix127_12_2 Q2.hinj127_12_2
      Q2.hcardT127_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_12_2 i) (Q2.hfix127_12_2 i) _)
      colCert_127_12_2.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T127_12
      hfix127_12 hinj127_12 hcardT127_12
      (fun i => conj_mem_of_fixedPoints _ _ (T127_12 i) (hfix127_12 i) _)
      ⟨127, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T127_12_2 Q2.hfix127_12_2 Q2.hinj127_12_2
      Q2.hcardT127_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_12_2 i) (Q2.hfix127_12_2 i) _)
      colCert_127_12_3.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T127_12
      hfix127_12 hinj127_12 hcardT127_12
      (fun i => conj_mem_of_fixedPoints _ _ (T127_12 i) (hfix127_12 i) _)
      ⟨127, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T127_12_2 Q2.hfix127_12_2 Q2.hinj127_12_2
      Q2.hcardT127_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_12_2 i) (Q2.hfix127_12_2 i) _)
      colCert_127_12_4.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_21_0 (hp : 0 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 0 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 0 (transLenTr ⟨21, by decide⟩ 0 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 0 (transLenTr ⟨21, by decide⟩ 0 hp)) T127_21
      hfix127_21 hinj127_21 hcardT127_21
      (fun i => conj_mem_of_fixedPoints _ _ (T127_21 i) (hfix127_21 i) _)
      ⟨127, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 0 hp) Q2.T127_21_2 Q2.hfix127_21_2 Q2.hinj127_21_2
      Q2.hcardT127_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_21_2 i) (Q2.hfix127_21_2 i) _)
      colCert_127_21_0.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_21_1 (hp : 1 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 1 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 1 (transLenTr ⟨21, by decide⟩ 1 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 1 (transLenTr ⟨21, by decide⟩ 1 hp)) T127_21
      hfix127_21 hinj127_21 hcardT127_21
      (fun i => conj_mem_of_fixedPoints _ _ (T127_21 i) (hfix127_21 i) _)
      ⟨127, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 1 hp) Q2.T127_21_2 Q2.hfix127_21_2 Q2.hinj127_21_2
      Q2.hcardT127_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_21_2 i) (Q2.hfix127_21_2 i) _)
      colCert_127_21_1.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_21_2 (hp : 2 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 2 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 2 (transLenTr ⟨21, by decide⟩ 2 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 2 (transLenTr ⟨21, by decide⟩ 2 hp)) T127_21
      hfix127_21 hinj127_21 hcardT127_21
      (fun i => conj_mem_of_fixedPoints _ _ (T127_21 i) (hfix127_21 i) _)
      ⟨127, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 2 hp) Q2.T127_21_2 Q2.hfix127_21_2 Q2.hinj127_21_2
      Q2.hcardT127_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_21_2 i) (Q2.hfix127_21_2 i) _)
      colCert_127_21_2.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_21_3 (hp : 3 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 3 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 3 (transLenTr ⟨21, by decide⟩ 3 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 3 (transLenTr ⟨21, by decide⟩ 3 hp)) T127_21
      hfix127_21 hinj127_21 hcardT127_21
      (fun i => conj_mem_of_fixedPoints _ _ (T127_21 i) (hfix127_21 i) _)
      ⟨127, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 3 hp) Q2.T127_21_2 Q2.hfix127_21_2 Q2.hinj127_21_2
      Q2.hcardT127_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_21_2 i) (Q2.hfix127_21_2 i) _)
      colCert_127_21_3.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_21_4 (hp : 4 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 4 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 4 (transLenTr ⟨21, by decide⟩ 4 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 4 (transLenTr ⟨21, by decide⟩ 4 hp)) T127_21
      hfix127_21 hinj127_21 hcardT127_21
      (fun i => conj_mem_of_fixedPoints _ _ (T127_21 i) (hfix127_21 i) _)
      ⟨127, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 4 hp) Q2.T127_21_2 Q2.hfix127_21_2 Q2.hinj127_21_2
      Q2.hcardT127_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_21_2 i) (Q2.hfix127_21_2 i) _)
      colCert_127_21_4.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_21_5 (hp : 5 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 5 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp)) T127_21
      hfix127_21 hinj127_21 hcardT127_21
      (fun i => conj_mem_of_fixedPoints _ _ (T127_21 i) (hfix127_21 i) _)
      ⟨127, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 5 hp) Q2.T127_21_2 Q2.hfix127_21_2 Q2.hinj127_21_2
      Q2.hcardT127_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_21_2 i) (Q2.hfix127_21_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp) : ↥(reps ⟨21, by decide⟩)) : Coordinate 1)
        T127_21 = colFn colCertDiv_127_21_5.D1 (m := 5) from colCertDiv_127_21_5.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨21, by decide⟩ 5 hp : ↥(Q2.reps ⟨21, by decide⟩)) : Coordinate 2)
        Q2.T127_21_2 = colFn colCertDiv_127_21_5.D2 (m := 5) from colCertDiv_127_21_5.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_21_5_match


theorem leaf_127_21_10 (hp : 10 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 10 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp)) T127_21
      hfix127_21 hinj127_21 hcardT127_21
      (fun i => conj_mem_of_fixedPoints _ _ (T127_21 i) (hfix127_21 i) _)
      ⟨127, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 10 hp) Q2.T127_21_2 Q2.hfix127_21_2 Q2.hinj127_21_2
      Q2.hcardT127_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_21_2 i) (Q2.hfix127_21_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp) : ↥(reps ⟨21, by decide⟩)) : Coordinate 1)
        T127_21 = colFn colCertDiv_127_21_10.D1 (m := 5) from colCertDiv_127_21_10.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨21, by decide⟩ 10 hp : ↥(Q2.reps ⟨21, by decide⟩)) : Coordinate 2)
        Q2.T127_21_2 = colFn colCertDiv_127_21_10.D2 (m := 5) from colCertDiv_127_21_10.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_21_10_match


theorem leaf_127_21_15 (hp : 15 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 15 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp)) T127_21
      hfix127_21 hinj127_21 hcardT127_21
      (fun i => conj_mem_of_fixedPoints _ _ (T127_21 i) (hfix127_21 i) _)
      ⟨127, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 15 hp) Q2.T127_21_2 Q2.hfix127_21_2 Q2.hinj127_21_2
      Q2.hcardT127_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_21_2 i) (Q2.hfix127_21_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp) : ↥(reps ⟨21, by decide⟩)) : Coordinate 1)
        T127_21 = colFn colCertDiv_127_21_15.D1 (m := 5) from colCertDiv_127_21_15.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨21, by decide⟩ 15 hp : ↥(Q2.reps ⟨21, by decide⟩)) : Coordinate 2)
        Q2.T127_21_2 = colFn colCertDiv_127_21_15.D2 (m := 5) from colCertDiv_127_21_15.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_21_15_match


theorem leaf_127_21_20 (hp : 20 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 20 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp)) T127_21
      hfix127_21 hinj127_21 hcardT127_21
      (fun i => conj_mem_of_fixedPoints _ _ (T127_21 i) (hfix127_21 i) _)
      ⟨127, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 20 hp) Q2.T127_21_2 Q2.hfix127_21_2 Q2.hinj127_21_2
      Q2.hcardT127_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_21_2 i) (Q2.hfix127_21_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp) : ↥(reps ⟨21, by decide⟩)) : Coordinate 1)
        T127_21 = colFn colCertDiv_127_21_20.D1 (m := 5) from colCertDiv_127_21_20.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨21, by decide⟩ 20 hp : ↥(Q2.reps ⟨21, by decide⟩)) : Coordinate 2)
        Q2.T127_21_2 = colFn colCertDiv_127_21_20.D2 (m := 5) from colCertDiv_127_21_20.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_21_20_match


theorem leaf_127_32_0 (hp : 0 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 0 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp)) T127_32
      hfix127_32 hinj127_32 hcardT127_32
      (fun i => conj_mem_of_fixedPoints _ _ (T127_32 i) (hfix127_32 i) _)
      ⟨127, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 0 hp) Q2.T127_32_2 Q2.hfix127_32_2 Q2.hinj127_32_2
      Q2.hcardT127_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_32_2 i) (Q2.hfix127_32_2 i) _)
      colCert_127_32_0.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_32_1 (hp : 1 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 1 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp)) T127_32
      hfix127_32 hinj127_32 hcardT127_32
      (fun i => conj_mem_of_fixedPoints _ _ (T127_32 i) (hfix127_32 i) _)
      ⟨127, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 1 hp) Q2.T127_32_2 Q2.hfix127_32_2 Q2.hinj127_32_2
      Q2.hcardT127_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_32_2 i) (Q2.hfix127_32_2 i) _)
      colCert_127_32_1.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_32_2 (hp : 2 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 2 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp)) T127_32
      hfix127_32 hinj127_32 hcardT127_32
      (fun i => conj_mem_of_fixedPoints _ _ (T127_32 i) (hfix127_32 i) _)
      ⟨127, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 2 hp) Q2.T127_32_2 Q2.hfix127_32_2 Q2.hinj127_32_2
      Q2.hcardT127_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_32_2 i) (Q2.hfix127_32_2 i) _)
      colCert_127_32_2.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_32_3 (hp : 3 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 3 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp)) T127_32
      hfix127_32 hinj127_32 hcardT127_32
      (fun i => conj_mem_of_fixedPoints _ _ (T127_32 i) (hfix127_32 i) _)
      ⟨127, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 3 hp) Q2.T127_32_2 Q2.hfix127_32_2 Q2.hinj127_32_2
      Q2.hcardT127_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_32_2 i) (Q2.hfix127_32_2 i) _)
      colCert_127_32_3.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_32_4 (hp : 4 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 4 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp)) T127_32
      hfix127_32 hinj127_32 hcardT127_32
      (fun i => conj_mem_of_fixedPoints _ _ (T127_32 i) (hfix127_32 i) _)
      ⟨127, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 4 hp) Q2.T127_32_2 Q2.hfix127_32_2 Q2.hinj127_32_2
      Q2.hcardT127_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_32_2 i) (Q2.hfix127_32_2 i) _)
      colCert_127_32_4.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_32_5 (hp : 5 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 5 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp)) T127_32
      hfix127_32 hinj127_32 hcardT127_32
      (fun i => conj_mem_of_fixedPoints _ _ (T127_32 i) (hfix127_32 i) _)
      ⟨127, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 5 hp) Q2.T127_32_2 Q2.hfix127_32_2 Q2.hinj127_32_2
      Q2.hcardT127_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_32_2 i) (Q2.hfix127_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T127_32 = colFn colCertDiv_127_32_5.D1 (m := 5) from colCertDiv_127_32_5.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 5 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T127_32_2 = colFn colCertDiv_127_32_5.D2 (m := 5) from colCertDiv_127_32_5.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_32_5_match


theorem leaf_127_32_10 (hp : 10 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 10 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp)) T127_32
      hfix127_32 hinj127_32 hcardT127_32
      (fun i => conj_mem_of_fixedPoints _ _ (T127_32 i) (hfix127_32 i) _)
      ⟨127, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 10 hp) Q2.T127_32_2 Q2.hfix127_32_2 Q2.hinj127_32_2
      Q2.hcardT127_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_32_2 i) (Q2.hfix127_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T127_32 = colFn colCertDiv_127_32_10.D1 (m := 5) from colCertDiv_127_32_10.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 10 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T127_32_2 = colFn colCertDiv_127_32_10.D2 (m := 5) from colCertDiv_127_32_10.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_32_10_match


theorem leaf_127_32_15 (hp : 15 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 15 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp)) T127_32
      hfix127_32 hinj127_32 hcardT127_32
      (fun i => conj_mem_of_fixedPoints _ _ (T127_32 i) (hfix127_32 i) _)
      ⟨127, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 15 hp) Q2.T127_32_2 Q2.hfix127_32_2 Q2.hinj127_32_2
      Q2.hcardT127_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_32_2 i) (Q2.hfix127_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T127_32 = colFn colCertDiv_127_32_15.D1 (m := 5) from colCertDiv_127_32_15.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 15 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T127_32_2 = colFn colCertDiv_127_32_15.D2 (m := 5) from colCertDiv_127_32_15.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_32_15_match


theorem leaf_127_32_20 (hp : 20 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 20 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp)) T127_32
      hfix127_32 hinj127_32 hcardT127_32
      (fun i => conj_mem_of_fixedPoints _ _ (T127_32 i) (hfix127_32 i) _)
      ⟨127, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 20 hp) Q2.T127_32_2 Q2.hfix127_32_2 Q2.hinj127_32_2
      Q2.hcardT127_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_32_2 i) (Q2.hfix127_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T127_32 = colFn colCertDiv_127_32_20.D1 (m := 5) from colCertDiv_127_32_20.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 20 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T127_32_2 = colFn colCertDiv_127_32_20.D2 (m := 5) from colCertDiv_127_32_20.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_32_20_match


theorem leaf_127_33_0 (hp : 0 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 0 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp)) T127_33
      hfix127_33 hinj127_33 hcardT127_33
      (fun i => conj_mem_of_fixedPoints _ _ (T127_33 i) (hfix127_33 i) _)
      ⟨127, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 0 hp) Q2.T127_33_2 Q2.hfix127_33_2 Q2.hinj127_33_2
      Q2.hcardT127_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_33_2 i) (Q2.hfix127_33_2 i) _)
      colCert_127_33_0.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_33_1 (hp : 1 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 1 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp)) T127_33
      hfix127_33 hinj127_33 hcardT127_33
      (fun i => conj_mem_of_fixedPoints _ _ (T127_33 i) (hfix127_33 i) _)
      ⟨127, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 1 hp) Q2.T127_33_2 Q2.hfix127_33_2 Q2.hinj127_33_2
      Q2.hcardT127_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_33_2 i) (Q2.hfix127_33_2 i) _)
      colCert_127_33_1.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_33_2 (hp : 2 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 2 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp)) T127_33
      hfix127_33 hinj127_33 hcardT127_33
      (fun i => conj_mem_of_fixedPoints _ _ (T127_33 i) (hfix127_33 i) _)
      ⟨127, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 2 hp) Q2.T127_33_2 Q2.hfix127_33_2 Q2.hinj127_33_2
      Q2.hcardT127_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_33_2 i) (Q2.hfix127_33_2 i) _)
      colCert_127_33_2.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_33_3 (hp : 3 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 3 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp)) T127_33
      hfix127_33 hinj127_33 hcardT127_33
      (fun i => conj_mem_of_fixedPoints _ _ (T127_33 i) (hfix127_33 i) _)
      ⟨127, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 3 hp) Q2.T127_33_2 Q2.hfix127_33_2 Q2.hinj127_33_2
      Q2.hcardT127_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_33_2 i) (Q2.hfix127_33_2 i) _)
      colCert_127_33_3.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_33_4 (hp : 4 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 4 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp)) T127_33
      hfix127_33 hinj127_33 hcardT127_33
      (fun i => conj_mem_of_fixedPoints _ _ (T127_33 i) (hfix127_33 i) _)
      ⟨127, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 4 hp) Q2.T127_33_2 Q2.hfix127_33_2 Q2.hinj127_33_2
      Q2.hcardT127_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_33_2 i) (Q2.hfix127_33_2 i) _)
      colCert_127_33_4.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_33_5 (hp : 5 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 5 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp)) T127_33
      hfix127_33 hinj127_33 hcardT127_33
      (fun i => conj_mem_of_fixedPoints _ _ (T127_33 i) (hfix127_33 i) _)
      ⟨127, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 5 hp) Q2.T127_33_2 Q2.hfix127_33_2 Q2.hinj127_33_2
      Q2.hcardT127_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_33_2 i) (Q2.hfix127_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T127_33 = colFn colCertDiv_127_33_5.D1 (m := 5) from colCertDiv_127_33_5.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 5 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T127_33_2 = colFn colCertDiv_127_33_5.D2 (m := 5) from colCertDiv_127_33_5.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_33_5_match


theorem leaf_127_33_10 (hp : 10 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 10 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp)) T127_33
      hfix127_33 hinj127_33 hcardT127_33
      (fun i => conj_mem_of_fixedPoints _ _ (T127_33 i) (hfix127_33 i) _)
      ⟨127, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 10 hp) Q2.T127_33_2 Q2.hfix127_33_2 Q2.hinj127_33_2
      Q2.hcardT127_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_33_2 i) (Q2.hfix127_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T127_33 = colFn colCertDiv_127_33_10.D1 (m := 5) from colCertDiv_127_33_10.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 10 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T127_33_2 = colFn colCertDiv_127_33_10.D2 (m := 5) from colCertDiv_127_33_10.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_33_10_match


theorem leaf_127_33_15 (hp : 15 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 15 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp)) T127_33
      hfix127_33 hinj127_33 hcardT127_33
      (fun i => conj_mem_of_fixedPoints _ _ (T127_33 i) (hfix127_33 i) _)
      ⟨127, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 15 hp) Q2.T127_33_2 Q2.hfix127_33_2 Q2.hinj127_33_2
      Q2.hcardT127_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_33_2 i) (Q2.hfix127_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T127_33 = colFn colCertDiv_127_33_15.D1 (m := 5) from colCertDiv_127_33_15.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 15 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T127_33_2 = colFn colCertDiv_127_33_15.D2 (m := 5) from colCertDiv_127_33_15.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_33_15_match


theorem leaf_127_33_20 (hp : 20 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 20 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp)) T127_33
      hfix127_33 hinj127_33 hcardT127_33
      (fun i => conj_mem_of_fixedPoints _ _ (T127_33 i) (hfix127_33 i) _)
      ⟨127, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 20 hp) Q2.T127_33_2 Q2.hfix127_33_2 Q2.hinj127_33_2
      Q2.hcardT127_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_33_2 i) (Q2.hfix127_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T127_33 = colFn colCertDiv_127_33_20.D1 (m := 5) from colCertDiv_127_33_20.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 20 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T127_33_2 = colFn colCertDiv_127_33_20.D2 (m := 5) from colCertDiv_127_33_20.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_33_20_match


theorem leaf_127_40_0 (hp : 0 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 0 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp)) T127_40
      hfix127_40 hinj127_40 hcardT127_40
      (fun i => conj_mem_of_fixedPoints _ _ (T127_40 i) (hfix127_40 i) _)
      ⟨127, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 0 hp) Q2.T127_40_2 Q2.hfix127_40_2 Q2.hinj127_40_2
      Q2.hcardT127_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_40_2 i) (Q2.hfix127_40_2 i) _)
      colCert_127_40_0.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_40_1 (hp : 1 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 1 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp)) T127_40
      hfix127_40 hinj127_40 hcardT127_40
      (fun i => conj_mem_of_fixedPoints _ _ (T127_40 i) (hfix127_40 i) _)
      ⟨127, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 1 hp) Q2.T127_40_2 Q2.hfix127_40_2 Q2.hinj127_40_2
      Q2.hcardT127_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_40_2 i) (Q2.hfix127_40_2 i) _)
      colCert_127_40_1.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_40_2 (hp : 2 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 2 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp)) T127_40
      hfix127_40 hinj127_40 hcardT127_40
      (fun i => conj_mem_of_fixedPoints _ _ (T127_40 i) (hfix127_40 i) _)
      ⟨127, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 2 hp) Q2.T127_40_2 Q2.hfix127_40_2 Q2.hinj127_40_2
      Q2.hcardT127_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_40_2 i) (Q2.hfix127_40_2 i) _)
      colCert_127_40_2.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_40_3 (hp : 3 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 3 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp)) T127_40
      hfix127_40 hinj127_40 hcardT127_40
      (fun i => conj_mem_of_fixedPoints _ _ (T127_40 i) (hfix127_40 i) _)
      ⟨127, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 3 hp) Q2.T127_40_2 Q2.hfix127_40_2 Q2.hinj127_40_2
      Q2.hcardT127_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_40_2 i) (Q2.hfix127_40_2 i) _)
      colCert_127_40_3.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_40_4 (hp : 4 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 4 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp)) T127_40
      hfix127_40 hinj127_40 hcardT127_40
      (fun i => conj_mem_of_fixedPoints _ _ (T127_40 i) (hfix127_40 i) _)
      ⟨127, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 4 hp) Q2.T127_40_2 Q2.hfix127_40_2 Q2.hinj127_40_2
      Q2.hcardT127_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_40_2 i) (Q2.hfix127_40_2 i) _)
      colCert_127_40_4.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_40_5 (hp : 5 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 5 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp)) T127_40
      hfix127_40 hinj127_40 hcardT127_40
      (fun i => conj_mem_of_fixedPoints _ _ (T127_40 i) (hfix127_40 i) _)
      ⟨127, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 5 hp) Q2.T127_40_2 Q2.hfix127_40_2 Q2.hinj127_40_2
      Q2.hcardT127_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_40_2 i) (Q2.hfix127_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T127_40 = colFn colCertDiv_127_40_5.D1 (m := 5) from colCertDiv_127_40_5.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 5 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T127_40_2 = colFn colCertDiv_127_40_5.D2 (m := 5) from colCertDiv_127_40_5.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_40_5_match


theorem leaf_127_40_10 (hp : 10 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 10 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp)) T127_40
      hfix127_40 hinj127_40 hcardT127_40
      (fun i => conj_mem_of_fixedPoints _ _ (T127_40 i) (hfix127_40 i) _)
      ⟨127, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 10 hp) Q2.T127_40_2 Q2.hfix127_40_2 Q2.hinj127_40_2
      Q2.hcardT127_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_40_2 i) (Q2.hfix127_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T127_40 = colFn colCertDiv_127_40_10.D1 (m := 5) from colCertDiv_127_40_10.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 10 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T127_40_2 = colFn colCertDiv_127_40_10.D2 (m := 5) from colCertDiv_127_40_10.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_40_10_match


theorem leaf_127_40_15 (hp : 15 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 15 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp)) T127_40
      hfix127_40 hinj127_40 hcardT127_40
      (fun i => conj_mem_of_fixedPoints _ _ (T127_40 i) (hfix127_40 i) _)
      ⟨127, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 15 hp) Q2.T127_40_2 Q2.hfix127_40_2 Q2.hinj127_40_2
      Q2.hcardT127_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_40_2 i) (Q2.hfix127_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T127_40 = colFn colCertDiv_127_40_15.D1 (m := 5) from colCertDiv_127_40_15.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 15 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T127_40_2 = colFn colCertDiv_127_40_15.D2 (m := 5) from colCertDiv_127_40_15.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_40_15_match


theorem leaf_127_40_20 (hp : 20 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 20 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp)) T127_40
      hfix127_40 hinj127_40 hcardT127_40
      (fun i => conj_mem_of_fixedPoints _ _ (T127_40 i) (hfix127_40 i) _)
      ⟨127, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 20 hp) Q2.T127_40_2 Q2.hfix127_40_2 Q2.hinj127_40_2
      Q2.hcardT127_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_40_2 i) (Q2.hfix127_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T127_40 = colFn colCertDiv_127_40_20.D1 (m := 5) from colCertDiv_127_40_20.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 20 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T127_40_2 = colFn colCertDiv_127_40_20.D2 (m := 5) from colCertDiv_127_40_20.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_40_20_match


theorem leaf_127_46_0 (hp : 0 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 0 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp)) T127_46
      hfix127_46 hinj127_46 hcardT127_46
      (fun i => conj_mem_of_fixedPoints _ _ (T127_46 i) (hfix127_46 i) _)
      ⟨127, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 0 hp) Q2.T127_46_2 Q2.hfix127_46_2 Q2.hinj127_46_2
      Q2.hcardT127_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_46_2 i) (Q2.hfix127_46_2 i) _)
      colCert_127_46_0.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_46_1 (hp : 1 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 1 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp)) T127_46
      hfix127_46 hinj127_46 hcardT127_46
      (fun i => conj_mem_of_fixedPoints _ _ (T127_46 i) (hfix127_46 i) _)
      ⟨127, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 1 hp) Q2.T127_46_2 Q2.hfix127_46_2 Q2.hinj127_46_2
      Q2.hcardT127_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_46_2 i) (Q2.hfix127_46_2 i) _)
      colCert_127_46_1.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_46_2 (hp : 2 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 2 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp)) T127_46
      hfix127_46 hinj127_46 hcardT127_46
      (fun i => conj_mem_of_fixedPoints _ _ (T127_46 i) (hfix127_46 i) _)
      ⟨127, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 2 hp) Q2.T127_46_2 Q2.hfix127_46_2 Q2.hinj127_46_2
      Q2.hcardT127_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_46_2 i) (Q2.hfix127_46_2 i) _)
      colCert_127_46_2.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_46_3 (hp : 3 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 3 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp)) T127_46
      hfix127_46 hinj127_46 hcardT127_46
      (fun i => conj_mem_of_fixedPoints _ _ (T127_46 i) (hfix127_46 i) _)
      ⟨127, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 3 hp) Q2.T127_46_2 Q2.hfix127_46_2 Q2.hinj127_46_2
      Q2.hcardT127_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_46_2 i) (Q2.hfix127_46_2 i) _)
      colCert_127_46_3.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_46_4 (hp : 4 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 4 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp)) T127_46
      hfix127_46 hinj127_46 hcardT127_46
      (fun i => conj_mem_of_fixedPoints _ _ (T127_46 i) (hfix127_46 i) _)
      ⟨127, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 4 hp) Q2.T127_46_2 Q2.hfix127_46_2 Q2.hinj127_46_2
      Q2.hcardT127_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_46_2 i) (Q2.hfix127_46_2 i) _)
      colCert_127_46_4.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_46_5 (hp : 5 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 5 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp)) T127_46
      hfix127_46 hinj127_46 hcardT127_46
      (fun i => conj_mem_of_fixedPoints _ _ (T127_46 i) (hfix127_46 i) _)
      ⟨127, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 5 hp) Q2.T127_46_2 Q2.hfix127_46_2 Q2.hinj127_46_2
      Q2.hcardT127_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_46_2 i) (Q2.hfix127_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T127_46 = colFn colCertDiv_127_46_5.D1 (m := 5) from colCertDiv_127_46_5.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 5 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T127_46_2 = colFn colCertDiv_127_46_5.D2 (m := 5) from colCertDiv_127_46_5.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_46_5_match


theorem leaf_127_46_10 (hp : 10 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 10 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp)) T127_46
      hfix127_46 hinj127_46 hcardT127_46
      (fun i => conj_mem_of_fixedPoints _ _ (T127_46 i) (hfix127_46 i) _)
      ⟨127, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 10 hp) Q2.T127_46_2 Q2.hfix127_46_2 Q2.hinj127_46_2
      Q2.hcardT127_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_46_2 i) (Q2.hfix127_46_2 i) _)
      colCert_127_46_10.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_46_15 (hp : 15 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 15 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp)) T127_46
      hfix127_46 hinj127_46 hcardT127_46
      (fun i => conj_mem_of_fixedPoints _ _ (T127_46 i) (hfix127_46 i) _)
      ⟨127, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 15 hp) Q2.T127_46_2 Q2.hfix127_46_2 Q2.hinj127_46_2
      Q2.hcardT127_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_46_2 i) (Q2.hfix127_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T127_46 = colFn colCertDiv_127_46_15.D1 (m := 5) from colCertDiv_127_46_15.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 15 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T127_46_2 = colFn colCertDiv_127_46_15.D2 (m := 5) from colCertDiv_127_46_15.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_46_15_match


theorem leaf_127_46_20 (hp : 20 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 20 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp)) T127_46
      hfix127_46 hinj127_46 hcardT127_46
      (fun i => conj_mem_of_fixedPoints _ _ (T127_46 i) (hfix127_46 i) _)
      ⟨127, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 20 hp) Q2.T127_46_2 Q2.hfix127_46_2 Q2.hinj127_46_2
      Q2.hcardT127_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_46_2 i) (Q2.hfix127_46_2 i) _)
      colCert_127_46_20.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_49_0 (hp : 0 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 0 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp)) T127_49
      hfix127_49 hinj127_49 hcardT127_49
      (fun i => conj_mem_of_fixedPoints _ _ (T127_49 i) (hfix127_49 i) _)
      ⟨127, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 0 hp) Q2.T127_49_2 Q2.hfix127_49_2 Q2.hinj127_49_2
      Q2.hcardT127_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_49_2 i) (Q2.hfix127_49_2 i) _)
      colCert_127_49_0.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_49_1 (hp : 1 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 1 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp)) T127_49
      hfix127_49 hinj127_49 hcardT127_49
      (fun i => conj_mem_of_fixedPoints _ _ (T127_49 i) (hfix127_49 i) _)
      ⟨127, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 1 hp) Q2.T127_49_2 Q2.hfix127_49_2 Q2.hinj127_49_2
      Q2.hcardT127_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_49_2 i) (Q2.hfix127_49_2 i) _)
      colCert_127_49_1.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_49_2 (hp : 2 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 2 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp)) T127_49
      hfix127_49 hinj127_49 hcardT127_49
      (fun i => conj_mem_of_fixedPoints _ _ (T127_49 i) (hfix127_49 i) _)
      ⟨127, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 2 hp) Q2.T127_49_2 Q2.hfix127_49_2 Q2.hinj127_49_2
      Q2.hcardT127_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_49_2 i) (Q2.hfix127_49_2 i) _)
      colCert_127_49_2.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_49_3 (hp : 3 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 3 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp)) T127_49
      hfix127_49 hinj127_49 hcardT127_49
      (fun i => conj_mem_of_fixedPoints _ _ (T127_49 i) (hfix127_49 i) _)
      ⟨127, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 3 hp) Q2.T127_49_2 Q2.hfix127_49_2 Q2.hinj127_49_2
      Q2.hcardT127_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_49_2 i) (Q2.hfix127_49_2 i) _)
      colCert_127_49_3.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_49_4 (hp : 4 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 4 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp)) T127_49
      hfix127_49 hinj127_49 hcardT127_49
      (fun i => conj_mem_of_fixedPoints _ _ (T127_49 i) (hfix127_49 i) _)
      ⟨127, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 4 hp) Q2.T127_49_2 Q2.hfix127_49_2 Q2.hinj127_49_2
      Q2.hcardT127_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_49_2 i) (Q2.hfix127_49_2 i) _)
      colCert_127_49_4.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_49_5 (hp : 5 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 5 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp)) T127_49
      hfix127_49 hinj127_49 hcardT127_49
      (fun i => conj_mem_of_fixedPoints _ _ (T127_49 i) (hfix127_49 i) _)
      ⟨127, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 5 hp) Q2.T127_49_2 Q2.hfix127_49_2 Q2.hinj127_49_2
      Q2.hcardT127_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_49_2 i) (Q2.hfix127_49_2 i) _)
      colCert_127_49_5.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_49_10 (hp : 10 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 10 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp)) T127_49
      hfix127_49 hinj127_49 hcardT127_49
      (fun i => conj_mem_of_fixedPoints _ _ (T127_49 i) (hfix127_49 i) _)
      ⟨127, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 10 hp) Q2.T127_49_2 Q2.hfix127_49_2 Q2.hinj127_49_2
      Q2.hcardT127_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_49_2 i) (Q2.hfix127_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T127_49 = colFn colCertDiv_127_49_10.D1 (m := 5) from colCertDiv_127_49_10.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 10 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T127_49_2 = colFn colCertDiv_127_49_10.D2 (m := 5) from colCertDiv_127_49_10.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_49_10_match


theorem leaf_127_49_15 (hp : 15 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 15 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp)) T127_49
      hfix127_49 hinj127_49 hcardT127_49
      (fun i => conj_mem_of_fixedPoints _ _ (T127_49 i) (hfix127_49 i) _)
      ⟨127, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 15 hp) Q2.T127_49_2 Q2.hfix127_49_2 Q2.hinj127_49_2
      Q2.hcardT127_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_49_2 i) (Q2.hfix127_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T127_49 = colFn colCertDiv_127_49_15.D1 (m := 5) from colCertDiv_127_49_15.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 15 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T127_49_2 = colFn colCertDiv_127_49_15.D2 (m := 5) from colCertDiv_127_49_15.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_49_15_match


theorem leaf_127_49_20 (hp : 20 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 20 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp)) T127_49
      hfix127_49 hinj127_49 hcardT127_49
      (fun i => conj_mem_of_fixedPoints _ _ (T127_49 i) (hfix127_49 i) _)
      ⟨127, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 20 hp) Q2.T127_49_2 Q2.hfix127_49_2 Q2.hinj127_49_2
      Q2.hcardT127_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_49_2 i) (Q2.hfix127_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T127_49 = colFn colCertDiv_127_49_20.D1 (m := 5) from colCertDiv_127_49_20.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 20 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T127_49_2 = colFn colCertDiv_127_49_20.D2 (m := 5) from colCertDiv_127_49_20.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_49_20_match


theorem leaf_127_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T127_53
      hfix127_53 hinj127_53 hcardT127_53
      (fun i => conj_mem_of_fixedPoints _ _ (T127_53 i) (hfix127_53 i) _)
      ⟨127, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T127_53_2 Q2.hfix127_53_2 Q2.hinj127_53_2
      Q2.hcardT127_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_53_2 i) (Q2.hfix127_53_2 i) _)
      colCert_127_53_0.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T127_53
      hfix127_53 hinj127_53 hcardT127_53
      (fun i => conj_mem_of_fixedPoints _ _ (T127_53 i) (hfix127_53 i) _)
      ⟨127, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T127_53_2 Q2.hfix127_53_2 Q2.hinj127_53_2
      Q2.hcardT127_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_53_2 i) (Q2.hfix127_53_2 i) _)
      colCert_127_53_1.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T127_53
      hfix127_53 hinj127_53 hcardT127_53
      (fun i => conj_mem_of_fixedPoints _ _ (T127_53 i) (hfix127_53 i) _)
      ⟨127, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T127_53_2 Q2.hfix127_53_2 Q2.hinj127_53_2
      Q2.hcardT127_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_53_2 i) (Q2.hfix127_53_2 i) _)
      colCert_127_53_2.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T127_53
      hfix127_53 hinj127_53 hcardT127_53
      (fun i => conj_mem_of_fixedPoints _ _ (T127_53 i) (hfix127_53 i) _)
      ⟨127, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T127_53_2 Q2.hfix127_53_2 Q2.hinj127_53_2
      Q2.hcardT127_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_53_2 i) (Q2.hfix127_53_2 i) _)
      colCert_127_53_3.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T127_53
      hfix127_53 hinj127_53 hcardT127_53
      (fun i => conj_mem_of_fixedPoints _ _ (T127_53 i) (hfix127_53 i) _)
      ⟨127, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T127_53_2 Q2.hfix127_53_2 Q2.hinj127_53_2
      Q2.hcardT127_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_53_2 i) (Q2.hfix127_53_2 i) _)
      colCert_127_53_4.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T127_53
      hfix127_53 hinj127_53 hcardT127_53
      (fun i => conj_mem_of_fixedPoints _ _ (T127_53 i) (hfix127_53 i) _)
      ⟨127, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T127_53_2 Q2.hfix127_53_2 Q2.hinj127_53_2
      Q2.hcardT127_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_53_2 i) (Q2.hfix127_53_2 i) _)
      colCert_127_53_5.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T127_53
      hfix127_53 hinj127_53 hcardT127_53
      (fun i => conj_mem_of_fixedPoints _ _ (T127_53 i) (hfix127_53 i) _)
      ⟨127, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T127_53_2 Q2.hfix127_53_2 Q2.hinj127_53_2
      Q2.hcardT127_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_53_2 i) (Q2.hfix127_53_2 i) _)
      colCert_127_53_10.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T127_53
      hfix127_53 hinj127_53 hcardT127_53
      (fun i => conj_mem_of_fixedPoints _ _ (T127_53 i) (hfix127_53 i) _)
      ⟨127, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T127_53_2 Q2.hfix127_53_2 Q2.hinj127_53_2
      Q2.hcardT127_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_53_2 i) (Q2.hfix127_53_2 i) _)
      colCert_127_53_15.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T127_53
      hfix127_53 hinj127_53 hcardT127_53
      (fun i => conj_mem_of_fixedPoints _ _ (T127_53 i) (hfix127_53 i) _)
      ⟨127, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T127_53_2 Q2.hfix127_53_2 Q2.hinj127_53_2
      Q2.hcardT127_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_53_2 i) (Q2.hfix127_53_2 i) _)
      colCert_127_53_20.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_82_0 (hp : 0 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 0 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 0 (transLenTr ⟨82, by decide⟩ 0 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 0 (transLenTr ⟨82, by decide⟩ 0 hp)) T127_82
      hfix127_82 hinj127_82 hcardT127_82
      (fun i => conj_mem_of_fixedPoints _ _ (T127_82 i) (hfix127_82 i) _)
      ⟨127, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 0 hp) Q2.T127_82_2 Q2.hfix127_82_2 Q2.hinj127_82_2
      Q2.hcardT127_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_82_2 i) (Q2.hfix127_82_2 i) _)
      colCert_127_82_0.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_82_1 (hp : 1 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 1 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 1 (transLenTr ⟨82, by decide⟩ 1 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 1 (transLenTr ⟨82, by decide⟩ 1 hp)) T127_82
      hfix127_82 hinj127_82 hcardT127_82
      (fun i => conj_mem_of_fixedPoints _ _ (T127_82 i) (hfix127_82 i) _)
      ⟨127, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 1 hp) Q2.T127_82_2 Q2.hfix127_82_2 Q2.hinj127_82_2
      Q2.hcardT127_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_82_2 i) (Q2.hfix127_82_2 i) _)
      colCert_127_82_1.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_82_2 (hp : 2 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 2 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 2 (transLenTr ⟨82, by decide⟩ 2 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 2 (transLenTr ⟨82, by decide⟩ 2 hp)) T127_82
      hfix127_82 hinj127_82 hcardT127_82
      (fun i => conj_mem_of_fixedPoints _ _ (T127_82 i) (hfix127_82 i) _)
      ⟨127, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 2 hp) Q2.T127_82_2 Q2.hfix127_82_2 Q2.hinj127_82_2
      Q2.hcardT127_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_82_2 i) (Q2.hfix127_82_2 i) _)
      colCert_127_82_2.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_82_3 (hp : 3 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 3 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 3 (transLenTr ⟨82, by decide⟩ 3 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 3 (transLenTr ⟨82, by decide⟩ 3 hp)) T127_82
      hfix127_82 hinj127_82 hcardT127_82
      (fun i => conj_mem_of_fixedPoints _ _ (T127_82 i) (hfix127_82 i) _)
      ⟨127, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 3 hp) Q2.T127_82_2 Q2.hfix127_82_2 Q2.hinj127_82_2
      Q2.hcardT127_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_82_2 i) (Q2.hfix127_82_2 i) _)
      colCert_127_82_3.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_82_4 (hp : 4 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 4 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 4 (transLenTr ⟨82, by decide⟩ 4 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 4 (transLenTr ⟨82, by decide⟩ 4 hp)) T127_82
      hfix127_82 hinj127_82 hcardT127_82
      (fun i => conj_mem_of_fixedPoints _ _ (T127_82 i) (hfix127_82 i) _)
      ⟨127, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 4 hp) Q2.T127_82_2 Q2.hfix127_82_2 Q2.hinj127_82_2
      Q2.hcardT127_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_82_2 i) (Q2.hfix127_82_2 i) _)
      colCert_127_82_4.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_82_5 (hp : 5 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 5 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 5 (transLenTr ⟨82, by decide⟩ 5 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 5 (transLenTr ⟨82, by decide⟩ 5 hp)) T127_82
      hfix127_82 hinj127_82 hcardT127_82
      (fun i => conj_mem_of_fixedPoints _ _ (T127_82 i) (hfix127_82 i) _)
      ⟨127, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 5 hp) Q2.T127_82_2 Q2.hfix127_82_2 Q2.hinj127_82_2
      Q2.hcardT127_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_82_2 i) (Q2.hfix127_82_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨82, by decide⟩ 5 (transLenTr ⟨82, by decide⟩ 5 hp) : ↥(reps ⟨82, by decide⟩)) : Coordinate 1)
        T127_82 = colFn colCertDiv_127_82_5.D1 (m := 5) from colCertDiv_127_82_5.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨82, by decide⟩ 5 hp : ↥(Q2.reps ⟨82, by decide⟩)) : Coordinate 2)
        Q2.T127_82_2 = colFn colCertDiv_127_82_5.D2 (m := 5) from colCertDiv_127_82_5.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_82_5_match


theorem leaf_127_82_10 (hp : 10 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 10 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 10 (transLenTr ⟨82, by decide⟩ 10 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 10 (transLenTr ⟨82, by decide⟩ 10 hp)) T127_82
      hfix127_82 hinj127_82 hcardT127_82
      (fun i => conj_mem_of_fixedPoints _ _ (T127_82 i) (hfix127_82 i) _)
      ⟨127, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 10 hp) Q2.T127_82_2 Q2.hfix127_82_2 Q2.hinj127_82_2
      Q2.hcardT127_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_82_2 i) (Q2.hfix127_82_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨82, by decide⟩ 10 (transLenTr ⟨82, by decide⟩ 10 hp) : ↥(reps ⟨82, by decide⟩)) : Coordinate 1)
        T127_82 = colFn colCertDiv_127_82_10.D1 (m := 5) from colCertDiv_127_82_10.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨82, by decide⟩ 10 hp : ↥(Q2.reps ⟨82, by decide⟩)) : Coordinate 2)
        Q2.T127_82_2 = colFn colCertDiv_127_82_10.D2 (m := 5) from colCertDiv_127_82_10.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_82_10_match


theorem leaf_127_82_15 (hp : 15 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 15 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 15 (transLenTr ⟨82, by decide⟩ 15 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 15 (transLenTr ⟨82, by decide⟩ 15 hp)) T127_82
      hfix127_82 hinj127_82 hcardT127_82
      (fun i => conj_mem_of_fixedPoints _ _ (T127_82 i) (hfix127_82 i) _)
      ⟨127, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 15 hp) Q2.T127_82_2 Q2.hfix127_82_2 Q2.hinj127_82_2
      Q2.hcardT127_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_82_2 i) (Q2.hfix127_82_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨82, by decide⟩ 15 (transLenTr ⟨82, by decide⟩ 15 hp) : ↥(reps ⟨82, by decide⟩)) : Coordinate 1)
        T127_82 = colFn colCertDiv_127_82_15.D1 (m := 5) from colCertDiv_127_82_15.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨82, by decide⟩ 15 hp : ↥(Q2.reps ⟨82, by decide⟩)) : Coordinate 2)
        Q2.T127_82_2 = colFn colCertDiv_127_82_15.D2 (m := 5) from colCertDiv_127_82_15.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_82_15_match


theorem leaf_127_82_20 (hp : 20 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 20 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 20 (transLenTr ⟨82, by decide⟩ 20 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 20 (transLenTr ⟨82, by decide⟩ 20 hp)) T127_82
      hfix127_82 hinj127_82 hcardT127_82
      (fun i => conj_mem_of_fixedPoints _ _ (T127_82 i) (hfix127_82 i) _)
      ⟨127, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 20 hp) Q2.T127_82_2 Q2.hfix127_82_2 Q2.hinj127_82_2
      Q2.hcardT127_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_82_2 i) (Q2.hfix127_82_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨82, by decide⟩ 20 (transLenTr ⟨82, by decide⟩ 20 hp) : ↥(reps ⟨82, by decide⟩)) : Coordinate 1)
        T127_82 = colFn colCertDiv_127_82_20.D1 (m := 5) from colCertDiv_127_82_20.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨82, by decide⟩ 20 hp : ↥(Q2.reps ⟨82, by decide⟩)) : Coordinate 2)
        Q2.T127_82_2 = colFn colCertDiv_127_82_20.D2 (m := 5) from colCertDiv_127_82_20.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_82_20_match


theorem leaf_127_94_0 (hp : 0 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 0 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 0 (transLenTr ⟨94, by decide⟩ 0 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 0 (transLenTr ⟨94, by decide⟩ 0 hp)) T127_94
      hfix127_94 hinj127_94 hcardT127_94
      (fun i => conj_mem_of_fixedPoints _ _ (T127_94 i) (hfix127_94 i) _)
      ⟨127, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 0 hp) Q2.T127_94_2 Q2.hfix127_94_2 Q2.hinj127_94_2
      Q2.hcardT127_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_94_2 i) (Q2.hfix127_94_2 i) _)
      colCert_127_94_0.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_94_1 (hp : 1 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 1 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 1 (transLenTr ⟨94, by decide⟩ 1 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 1 (transLenTr ⟨94, by decide⟩ 1 hp)) T127_94
      hfix127_94 hinj127_94 hcardT127_94
      (fun i => conj_mem_of_fixedPoints _ _ (T127_94 i) (hfix127_94 i) _)
      ⟨127, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 1 hp) Q2.T127_94_2 Q2.hfix127_94_2 Q2.hinj127_94_2
      Q2.hcardT127_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_94_2 i) (Q2.hfix127_94_2 i) _)
      colCert_127_94_1.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_94_2 (hp : 2 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 2 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 2 (transLenTr ⟨94, by decide⟩ 2 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 2 (transLenTr ⟨94, by decide⟩ 2 hp)) T127_94
      hfix127_94 hinj127_94 hcardT127_94
      (fun i => conj_mem_of_fixedPoints _ _ (T127_94 i) (hfix127_94 i) _)
      ⟨127, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 2 hp) Q2.T127_94_2 Q2.hfix127_94_2 Q2.hinj127_94_2
      Q2.hcardT127_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_94_2 i) (Q2.hfix127_94_2 i) _)
      colCert_127_94_2.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_94_3 (hp : 3 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 3 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 3 (transLenTr ⟨94, by decide⟩ 3 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 3 (transLenTr ⟨94, by decide⟩ 3 hp)) T127_94
      hfix127_94 hinj127_94 hcardT127_94
      (fun i => conj_mem_of_fixedPoints _ _ (T127_94 i) (hfix127_94 i) _)
      ⟨127, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 3 hp) Q2.T127_94_2 Q2.hfix127_94_2 Q2.hinj127_94_2
      Q2.hcardT127_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_94_2 i) (Q2.hfix127_94_2 i) _)
      colCert_127_94_3.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_94_4 (hp : 4 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 4 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 4 (transLenTr ⟨94, by decide⟩ 4 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 4 (transLenTr ⟨94, by decide⟩ 4 hp)) T127_94
      hfix127_94 hinj127_94 hcardT127_94
      (fun i => conj_mem_of_fixedPoints _ _ (T127_94 i) (hfix127_94 i) _)
      ⟨127, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 4 hp) Q2.T127_94_2 Q2.hfix127_94_2 Q2.hinj127_94_2
      Q2.hcardT127_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_94_2 i) (Q2.hfix127_94_2 i) _)
      colCert_127_94_4.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_94_5 (hp : 5 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 5 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 5 (transLenTr ⟨94, by decide⟩ 5 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 5 (transLenTr ⟨94, by decide⟩ 5 hp)) T127_94
      hfix127_94 hinj127_94 hcardT127_94
      (fun i => conj_mem_of_fixedPoints _ _ (T127_94 i) (hfix127_94 i) _)
      ⟨127, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 5 hp) Q2.T127_94_2 Q2.hfix127_94_2 Q2.hinj127_94_2
      Q2.hcardT127_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_94_2 i) (Q2.hfix127_94_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨94, by decide⟩ 5 (transLenTr ⟨94, by decide⟩ 5 hp) : ↥(reps ⟨94, by decide⟩)) : Coordinate 1)
        T127_94 = colFn colCertDiv_127_94_5.D1 (m := 5) from colCertDiv_127_94_5.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨94, by decide⟩ 5 hp : ↥(Q2.reps ⟨94, by decide⟩)) : Coordinate 2)
        Q2.T127_94_2 = colFn colCertDiv_127_94_5.D2 (m := 5) from colCertDiv_127_94_5.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_94_5_match


theorem leaf_127_94_10 (hp : 10 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 10 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 10 (transLenTr ⟨94, by decide⟩ 10 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 10 (transLenTr ⟨94, by decide⟩ 10 hp)) T127_94
      hfix127_94 hinj127_94 hcardT127_94
      (fun i => conj_mem_of_fixedPoints _ _ (T127_94 i) (hfix127_94 i) _)
      ⟨127, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 10 hp) Q2.T127_94_2 Q2.hfix127_94_2 Q2.hinj127_94_2
      Q2.hcardT127_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_94_2 i) (Q2.hfix127_94_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨94, by decide⟩ 10 (transLenTr ⟨94, by decide⟩ 10 hp) : ↥(reps ⟨94, by decide⟩)) : Coordinate 1)
        T127_94 = colFn colCertDiv_127_94_10.D1 (m := 5) from colCertDiv_127_94_10.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨94, by decide⟩ 10 hp : ↥(Q2.reps ⟨94, by decide⟩)) : Coordinate 2)
        Q2.T127_94_2 = colFn colCertDiv_127_94_10.D2 (m := 5) from colCertDiv_127_94_10.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_94_10_match


theorem leaf_127_94_15 (hp : 15 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 15 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 15 (transLenTr ⟨94, by decide⟩ 15 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 15 (transLenTr ⟨94, by decide⟩ 15 hp)) T127_94
      hfix127_94 hinj127_94 hcardT127_94
      (fun i => conj_mem_of_fixedPoints _ _ (T127_94 i) (hfix127_94 i) _)
      ⟨127, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 15 hp) Q2.T127_94_2 Q2.hfix127_94_2 Q2.hinj127_94_2
      Q2.hcardT127_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_94_2 i) (Q2.hfix127_94_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨94, by decide⟩ 15 (transLenTr ⟨94, by decide⟩ 15 hp) : ↥(reps ⟨94, by decide⟩)) : Coordinate 1)
        T127_94 = colFn colCertDiv_127_94_15.D1 (m := 5) from colCertDiv_127_94_15.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨94, by decide⟩ 15 hp : ↥(Q2.reps ⟨94, by decide⟩)) : Coordinate 2)
        Q2.T127_94_2 = colFn colCertDiv_127_94_15.D2 (m := 5) from colCertDiv_127_94_15.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_94_15_match


theorem leaf_127_94_20 (hp : 20 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 20 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 20 (transLenTr ⟨94, by decide⟩ 20 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 20 (transLenTr ⟨94, by decide⟩ 20 hp)) T127_94
      hfix127_94 hinj127_94 hcardT127_94
      (fun i => conj_mem_of_fixedPoints _ _ (T127_94 i) (hfix127_94 i) _)
      ⟨127, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 20 hp) Q2.T127_94_2 Q2.hfix127_94_2 Q2.hinj127_94_2
      Q2.hcardT127_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_94_2 i) (Q2.hfix127_94_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨94, by decide⟩ 20 (transLenTr ⟨94, by decide⟩ 20 hp) : ↥(reps ⟨94, by decide⟩)) : Coordinate 1)
        T127_94 = colFn colCertDiv_127_94_20.D1 (m := 5) from colCertDiv_127_94_20.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨94, by decide⟩ 20 hp : ↥(Q2.reps ⟨94, by decide⟩)) : Coordinate 2)
        Q2.T127_94_2 = colFn colCertDiv_127_94_20.D2 (m := 5) from colCertDiv_127_94_20.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_94_20_match


theorem leaf_127_95_0 (hp : 0 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 0 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 0 (transLenTr ⟨95, by decide⟩ 0 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 0 (transLenTr ⟨95, by decide⟩ 0 hp)) T127_95
      hfix127_95 hinj127_95 hcardT127_95
      (fun i => conj_mem_of_fixedPoints _ _ (T127_95 i) (hfix127_95 i) _)
      ⟨127, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 0 hp) Q2.T127_95_2 Q2.hfix127_95_2 Q2.hinj127_95_2
      Q2.hcardT127_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_95_2 i) (Q2.hfix127_95_2 i) _)
      colCert_127_95_0.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_95_1 (hp : 1 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 1 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 1 (transLenTr ⟨95, by decide⟩ 1 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 1 (transLenTr ⟨95, by decide⟩ 1 hp)) T127_95
      hfix127_95 hinj127_95 hcardT127_95
      (fun i => conj_mem_of_fixedPoints _ _ (T127_95 i) (hfix127_95 i) _)
      ⟨127, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 1 hp) Q2.T127_95_2 Q2.hfix127_95_2 Q2.hinj127_95_2
      Q2.hcardT127_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_95_2 i) (Q2.hfix127_95_2 i) _)
      colCert_127_95_1.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_95_2 (hp : 2 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 2 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 2 (transLenTr ⟨95, by decide⟩ 2 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 2 (transLenTr ⟨95, by decide⟩ 2 hp)) T127_95
      hfix127_95 hinj127_95 hcardT127_95
      (fun i => conj_mem_of_fixedPoints _ _ (T127_95 i) (hfix127_95 i) _)
      ⟨127, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 2 hp) Q2.T127_95_2 Q2.hfix127_95_2 Q2.hinj127_95_2
      Q2.hcardT127_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_95_2 i) (Q2.hfix127_95_2 i) _)
      colCert_127_95_2.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_95_3 (hp : 3 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 3 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 3 (transLenTr ⟨95, by decide⟩ 3 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 3 (transLenTr ⟨95, by decide⟩ 3 hp)) T127_95
      hfix127_95 hinj127_95 hcardT127_95
      (fun i => conj_mem_of_fixedPoints _ _ (T127_95 i) (hfix127_95 i) _)
      ⟨127, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 3 hp) Q2.T127_95_2 Q2.hfix127_95_2 Q2.hinj127_95_2
      Q2.hcardT127_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_95_2 i) (Q2.hfix127_95_2 i) _)
      colCert_127_95_3.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_95_4 (hp : 4 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 4 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 4 (transLenTr ⟨95, by decide⟩ 4 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 4 (transLenTr ⟨95, by decide⟩ 4 hp)) T127_95
      hfix127_95 hinj127_95 hcardT127_95
      (fun i => conj_mem_of_fixedPoints _ _ (T127_95 i) (hfix127_95 i) _)
      ⟨127, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 4 hp) Q2.T127_95_2 Q2.hfix127_95_2 Q2.hinj127_95_2
      Q2.hcardT127_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_95_2 i) (Q2.hfix127_95_2 i) _)
      colCert_127_95_4.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_95_5 (hp : 5 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 5 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 5 (transLenTr ⟨95, by decide⟩ 5 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 5 (transLenTr ⟨95, by decide⟩ 5 hp)) T127_95
      hfix127_95 hinj127_95 hcardT127_95
      (fun i => conj_mem_of_fixedPoints _ _ (T127_95 i) (hfix127_95 i) _)
      ⟨127, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 5 hp) Q2.T127_95_2 Q2.hfix127_95_2 Q2.hinj127_95_2
      Q2.hcardT127_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_95_2 i) (Q2.hfix127_95_2 i) _)
      colCert_127_95_5.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_95_10 (hp : 10 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 10 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 10 (transLenTr ⟨95, by decide⟩ 10 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 10 (transLenTr ⟨95, by decide⟩ 10 hp)) T127_95
      hfix127_95 hinj127_95 hcardT127_95
      (fun i => conj_mem_of_fixedPoints _ _ (T127_95 i) (hfix127_95 i) _)
      ⟨127, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 10 hp) Q2.T127_95_2 Q2.hfix127_95_2 Q2.hinj127_95_2
      Q2.hcardT127_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_95_2 i) (Q2.hfix127_95_2 i) _)
      colCert_127_95_10.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_95_15 (hp : 15 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 15 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 15 (transLenTr ⟨95, by decide⟩ 15 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 15 (transLenTr ⟨95, by decide⟩ 15 hp)) T127_95
      hfix127_95 hinj127_95 hcardT127_95
      (fun i => conj_mem_of_fixedPoints _ _ (T127_95 i) (hfix127_95 i) _)
      ⟨127, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 15 hp) Q2.T127_95_2 Q2.hfix127_95_2 Q2.hinj127_95_2
      Q2.hcardT127_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_95_2 i) (Q2.hfix127_95_2 i) _)
      colCert_127_95_15.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_95_20 (hp : 20 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 20 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 20 (transLenTr ⟨95, by decide⟩ 20 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 20 (transLenTr ⟨95, by decide⟩ 20 hp)) T127_95
      hfix127_95 hinj127_95 hcardT127_95
      (fun i => conj_mem_of_fixedPoints _ _ (T127_95 i) (hfix127_95 i) _)
      ⟨127, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 20 hp) Q2.T127_95_2 Q2.hfix127_95_2 Q2.hinj127_95_2
      Q2.hcardT127_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_95_2 i) (Q2.hfix127_95_2 i) _)
      colCert_127_95_20.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_95_25 (hp : 25 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 25 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 25 (transLenTr ⟨95, by decide⟩ 25 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 25 (transLenTr ⟨95, by decide⟩ 25 hp)) T127_95
      hfix127_95 hinj127_95 hcardT127_95
      (fun i => conj_mem_of_fixedPoints _ _ (T127_95 i) (hfix127_95 i) _)
      ⟨127, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 25 hp) Q2.T127_95_2 Q2.hfix127_95_2 Q2.hinj127_95_2
      Q2.hcardT127_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_95_2 i) (Q2.hfix127_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 25 (transLenTr ⟨95, by decide⟩ 25 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T127_95 = colFn colCertDiv_127_95_25.D1 (m := 5) from colCertDiv_127_95_25.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 25 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T127_95_2 = colFn colCertDiv_127_95_25.D2 (m := 5) from colCertDiv_127_95_25.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_95_25_match


theorem leaf_127_95_50 (hp : 50 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 50 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 50 (transLenTr ⟨95, by decide⟩ 50 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 50 (transLenTr ⟨95, by decide⟩ 50 hp)) T127_95
      hfix127_95 hinj127_95 hcardT127_95
      (fun i => conj_mem_of_fixedPoints _ _ (T127_95 i) (hfix127_95 i) _)
      ⟨127, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 50 hp) Q2.T127_95_2 Q2.hfix127_95_2 Q2.hinj127_95_2
      Q2.hcardT127_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_95_2 i) (Q2.hfix127_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 50 (transLenTr ⟨95, by decide⟩ 50 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T127_95 = colFn colCertDiv_127_95_50.D1 (m := 5) from colCertDiv_127_95_50.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 50 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T127_95_2 = colFn colCertDiv_127_95_50.D2 (m := 5) from colCertDiv_127_95_50.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_95_50_match


theorem leaf_127_95_75 (hp : 75 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 75 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 75 (transLenTr ⟨95, by decide⟩ 75 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 75 (transLenTr ⟨95, by decide⟩ 75 hp)) T127_95
      hfix127_95 hinj127_95 hcardT127_95
      (fun i => conj_mem_of_fixedPoints _ _ (T127_95 i) (hfix127_95 i) _)
      ⟨127, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 75 hp) Q2.T127_95_2 Q2.hfix127_95_2 Q2.hinj127_95_2
      Q2.hcardT127_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_95_2 i) (Q2.hfix127_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 75 (transLenTr ⟨95, by decide⟩ 75 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T127_95 = colFn colCertDiv_127_95_75.D1 (m := 5) from colCertDiv_127_95_75.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 75 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T127_95_2 = colFn colCertDiv_127_95_75.D2 (m := 5) from colCertDiv_127_95_75.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_95_75_match


theorem leaf_127_95_100 (hp : 100 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 100 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 100 (transLenTr ⟨95, by decide⟩ 100 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 100 (transLenTr ⟨95, by decide⟩ 100 hp)) T127_95
      hfix127_95 hinj127_95 hcardT127_95
      (fun i => conj_mem_of_fixedPoints _ _ (T127_95 i) (hfix127_95 i) _)
      ⟨127, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 100 hp) Q2.T127_95_2 Q2.hfix127_95_2 Q2.hinj127_95_2
      Q2.hcardT127_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_95_2 i) (Q2.hfix127_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 100 (transLenTr ⟨95, by decide⟩ 100 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T127_95 = colFn colCertDiv_127_95_100.D1 (m := 5) from colCertDiv_127_95_100.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 100 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T127_95_2 = colFn colCertDiv_127_95_100.D2 (m := 5) from colCertDiv_127_95_100.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_95_100_match


theorem leaf_127_102_0 (hp : 0 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 0 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 0 (transLenTr ⟨102, by decide⟩ 0 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 0 (transLenTr ⟨102, by decide⟩ 0 hp)) T127_102
      hfix127_102 hinj127_102 hcardT127_102
      (fun i => conj_mem_of_fixedPoints _ _ (T127_102 i) (hfix127_102 i) _)
      ⟨127, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 0 hp) Q2.T127_102_2 Q2.hfix127_102_2 Q2.hinj127_102_2
      Q2.hcardT127_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_102_2 i) (Q2.hfix127_102_2 i) _)
      colCert_127_102_0.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_102_1 (hp : 1 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 1 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 1 (transLenTr ⟨102, by decide⟩ 1 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 1 (transLenTr ⟨102, by decide⟩ 1 hp)) T127_102
      hfix127_102 hinj127_102 hcardT127_102
      (fun i => conj_mem_of_fixedPoints _ _ (T127_102 i) (hfix127_102 i) _)
      ⟨127, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 1 hp) Q2.T127_102_2 Q2.hfix127_102_2 Q2.hinj127_102_2
      Q2.hcardT127_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_102_2 i) (Q2.hfix127_102_2 i) _)
      colCert_127_102_1.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_102_2 (hp : 2 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 2 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 2 (transLenTr ⟨102, by decide⟩ 2 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 2 (transLenTr ⟨102, by decide⟩ 2 hp)) T127_102
      hfix127_102 hinj127_102 hcardT127_102
      (fun i => conj_mem_of_fixedPoints _ _ (T127_102 i) (hfix127_102 i) _)
      ⟨127, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 2 hp) Q2.T127_102_2 Q2.hfix127_102_2 Q2.hinj127_102_2
      Q2.hcardT127_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_102_2 i) (Q2.hfix127_102_2 i) _)
      colCert_127_102_2.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_102_3 (hp : 3 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 3 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 3 (transLenTr ⟨102, by decide⟩ 3 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 3 (transLenTr ⟨102, by decide⟩ 3 hp)) T127_102
      hfix127_102 hinj127_102 hcardT127_102
      (fun i => conj_mem_of_fixedPoints _ _ (T127_102 i) (hfix127_102 i) _)
      ⟨127, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 3 hp) Q2.T127_102_2 Q2.hfix127_102_2 Q2.hinj127_102_2
      Q2.hcardT127_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_102_2 i) (Q2.hfix127_102_2 i) _)
      colCert_127_102_3.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_102_4 (hp : 4 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 4 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 4 (transLenTr ⟨102, by decide⟩ 4 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 4 (transLenTr ⟨102, by decide⟩ 4 hp)) T127_102
      hfix127_102 hinj127_102 hcardT127_102
      (fun i => conj_mem_of_fixedPoints _ _ (T127_102 i) (hfix127_102 i) _)
      ⟨127, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 4 hp) Q2.T127_102_2 Q2.hfix127_102_2 Q2.hinj127_102_2
      Q2.hcardT127_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_102_2 i) (Q2.hfix127_102_2 i) _)
      colCert_127_102_4.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_102_5 (hp : 5 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 5 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 5 (transLenTr ⟨102, by decide⟩ 5 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 5 (transLenTr ⟨102, by decide⟩ 5 hp)) T127_102
      hfix127_102 hinj127_102 hcardT127_102
      (fun i => conj_mem_of_fixedPoints _ _ (T127_102 i) (hfix127_102 i) _)
      ⟨127, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 5 hp) Q2.T127_102_2 Q2.hfix127_102_2 Q2.hinj127_102_2
      Q2.hcardT127_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_102_2 i) (Q2.hfix127_102_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨102, by decide⟩ 5 (transLenTr ⟨102, by decide⟩ 5 hp) : ↥(reps ⟨102, by decide⟩)) : Coordinate 1)
        T127_102 = colFn colCertDiv_127_102_5.D1 (m := 5) from colCertDiv_127_102_5.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨102, by decide⟩ 5 hp : ↥(Q2.reps ⟨102, by decide⟩)) : Coordinate 2)
        Q2.T127_102_2 = colFn colCertDiv_127_102_5.D2 (m := 5) from colCertDiv_127_102_5.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_102_5_match


theorem leaf_127_102_10 (hp : 10 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 10 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 10 (transLenTr ⟨102, by decide⟩ 10 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 10 (transLenTr ⟨102, by decide⟩ 10 hp)) T127_102
      hfix127_102 hinj127_102 hcardT127_102
      (fun i => conj_mem_of_fixedPoints _ _ (T127_102 i) (hfix127_102 i) _)
      ⟨127, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 10 hp) Q2.T127_102_2 Q2.hfix127_102_2 Q2.hinj127_102_2
      Q2.hcardT127_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_102_2 i) (Q2.hfix127_102_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨102, by decide⟩ 10 (transLenTr ⟨102, by decide⟩ 10 hp) : ↥(reps ⟨102, by decide⟩)) : Coordinate 1)
        T127_102 = colFn colCertDiv_127_102_10.D1 (m := 5) from colCertDiv_127_102_10.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨102, by decide⟩ 10 hp : ↥(Q2.reps ⟨102, by decide⟩)) : Coordinate 2)
        Q2.T127_102_2 = colFn colCertDiv_127_102_10.D2 (m := 5) from colCertDiv_127_102_10.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_102_10_match


theorem leaf_127_102_15 (hp : 15 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 15 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 15 (transLenTr ⟨102, by decide⟩ 15 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 15 (transLenTr ⟨102, by decide⟩ 15 hp)) T127_102
      hfix127_102 hinj127_102 hcardT127_102
      (fun i => conj_mem_of_fixedPoints _ _ (T127_102 i) (hfix127_102 i) _)
      ⟨127, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 15 hp) Q2.T127_102_2 Q2.hfix127_102_2 Q2.hinj127_102_2
      Q2.hcardT127_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_102_2 i) (Q2.hfix127_102_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨102, by decide⟩ 15 (transLenTr ⟨102, by decide⟩ 15 hp) : ↥(reps ⟨102, by decide⟩)) : Coordinate 1)
        T127_102 = colFn colCertDiv_127_102_15.D1 (m := 5) from colCertDiv_127_102_15.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨102, by decide⟩ 15 hp : ↥(Q2.reps ⟨102, by decide⟩)) : Coordinate 2)
        Q2.T127_102_2 = colFn colCertDiv_127_102_15.D2 (m := 5) from colCertDiv_127_102_15.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_102_15_match


theorem leaf_127_102_20 (hp : 20 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 20 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 20 (transLenTr ⟨102, by decide⟩ 20 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 20 (transLenTr ⟨102, by decide⟩ 20 hp)) T127_102
      hfix127_102 hinj127_102 hcardT127_102
      (fun i => conj_mem_of_fixedPoints _ _ (T127_102 i) (hfix127_102 i) _)
      ⟨127, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 20 hp) Q2.T127_102_2 Q2.hfix127_102_2 Q2.hinj127_102_2
      Q2.hcardT127_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_102_2 i) (Q2.hfix127_102_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨102, by decide⟩ 20 (transLenTr ⟨102, by decide⟩ 20 hp) : ↥(reps ⟨102, by decide⟩)) : Coordinate 1)
        T127_102 = colFn colCertDiv_127_102_20.D1 (m := 5) from colCertDiv_127_102_20.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨102, by decide⟩ 20 hp : ↥(Q2.reps ⟨102, by decide⟩)) : Coordinate 2)
        Q2.T127_102_2 = colFn colCertDiv_127_102_20.D2 (m := 5) from colCertDiv_127_102_20.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_102_20_match


theorem leaf_127_108_0 (hp : 0 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 0 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 0 (transLenTr ⟨108, by decide⟩ 0 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 0 (transLenTr ⟨108, by decide⟩ 0 hp)) T127_108
      hfix127_108 hinj127_108 hcardT127_108
      (fun i => conj_mem_of_fixedPoints _ _ (T127_108 i) (hfix127_108 i) _)
      ⟨127, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 0 hp) Q2.T127_108_2 Q2.hfix127_108_2 Q2.hinj127_108_2
      Q2.hcardT127_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_108_2 i) (Q2.hfix127_108_2 i) _)
      colCert_127_108_0.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_108_1 (hp : 1 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 1 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 1 (transLenTr ⟨108, by decide⟩ 1 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 1 (transLenTr ⟨108, by decide⟩ 1 hp)) T127_108
      hfix127_108 hinj127_108 hcardT127_108
      (fun i => conj_mem_of_fixedPoints _ _ (T127_108 i) (hfix127_108 i) _)
      ⟨127, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 1 hp) Q2.T127_108_2 Q2.hfix127_108_2 Q2.hinj127_108_2
      Q2.hcardT127_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_108_2 i) (Q2.hfix127_108_2 i) _)
      colCert_127_108_1.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_108_2 (hp : 2 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 2 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 2 (transLenTr ⟨108, by decide⟩ 2 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 2 (transLenTr ⟨108, by decide⟩ 2 hp)) T127_108
      hfix127_108 hinj127_108 hcardT127_108
      (fun i => conj_mem_of_fixedPoints _ _ (T127_108 i) (hfix127_108 i) _)
      ⟨127, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 2 hp) Q2.T127_108_2 Q2.hfix127_108_2 Q2.hinj127_108_2
      Q2.hcardT127_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_108_2 i) (Q2.hfix127_108_2 i) _)
      colCert_127_108_2.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_108_3 (hp : 3 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 3 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 3 (transLenTr ⟨108, by decide⟩ 3 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 3 (transLenTr ⟨108, by decide⟩ 3 hp)) T127_108
      hfix127_108 hinj127_108 hcardT127_108
      (fun i => conj_mem_of_fixedPoints _ _ (T127_108 i) (hfix127_108 i) _)
      ⟨127, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 3 hp) Q2.T127_108_2 Q2.hfix127_108_2 Q2.hinj127_108_2
      Q2.hcardT127_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_108_2 i) (Q2.hfix127_108_2 i) _)
      colCert_127_108_3.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_108_4 (hp : 4 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 4 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 4 (transLenTr ⟨108, by decide⟩ 4 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 4 (transLenTr ⟨108, by decide⟩ 4 hp)) T127_108
      hfix127_108 hinj127_108 hcardT127_108
      (fun i => conj_mem_of_fixedPoints _ _ (T127_108 i) (hfix127_108 i) _)
      ⟨127, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 4 hp) Q2.T127_108_2 Q2.hfix127_108_2 Q2.hinj127_108_2
      Q2.hcardT127_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_108_2 i) (Q2.hfix127_108_2 i) _)
      colCert_127_108_4.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_108_5 (hp : 5 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 5 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 5 (transLenTr ⟨108, by decide⟩ 5 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 5 (transLenTr ⟨108, by decide⟩ 5 hp)) T127_108
      hfix127_108 hinj127_108 hcardT127_108
      (fun i => conj_mem_of_fixedPoints _ _ (T127_108 i) (hfix127_108 i) _)
      ⟨127, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 5 hp) Q2.T127_108_2 Q2.hfix127_108_2 Q2.hinj127_108_2
      Q2.hcardT127_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_108_2 i) (Q2.hfix127_108_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨108, by decide⟩ 5 (transLenTr ⟨108, by decide⟩ 5 hp) : ↥(reps ⟨108, by decide⟩)) : Coordinate 1)
        T127_108 = colFn colCertDiv_127_108_5.D1 (m := 5) from colCertDiv_127_108_5.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨108, by decide⟩ 5 hp : ↥(Q2.reps ⟨108, by decide⟩)) : Coordinate 2)
        Q2.T127_108_2 = colFn colCertDiv_127_108_5.D2 (m := 5) from colCertDiv_127_108_5.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_108_5_match


theorem leaf_127_108_10 (hp : 10 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 10 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 10 (transLenTr ⟨108, by decide⟩ 10 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 10 (transLenTr ⟨108, by decide⟩ 10 hp)) T127_108
      hfix127_108 hinj127_108 hcardT127_108
      (fun i => conj_mem_of_fixedPoints _ _ (T127_108 i) (hfix127_108 i) _)
      ⟨127, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 10 hp) Q2.T127_108_2 Q2.hfix127_108_2 Q2.hinj127_108_2
      Q2.hcardT127_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_108_2 i) (Q2.hfix127_108_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨108, by decide⟩ 10 (transLenTr ⟨108, by decide⟩ 10 hp) : ↥(reps ⟨108, by decide⟩)) : Coordinate 1)
        T127_108 = colFn colCertDiv_127_108_10.D1 (m := 5) from colCertDiv_127_108_10.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨108, by decide⟩ 10 hp : ↥(Q2.reps ⟨108, by decide⟩)) : Coordinate 2)
        Q2.T127_108_2 = colFn colCertDiv_127_108_10.D2 (m := 5) from colCertDiv_127_108_10.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_108_10_match


theorem leaf_127_108_15 (hp : 15 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 15 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 15 (transLenTr ⟨108, by decide⟩ 15 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 15 (transLenTr ⟨108, by decide⟩ 15 hp)) T127_108
      hfix127_108 hinj127_108 hcardT127_108
      (fun i => conj_mem_of_fixedPoints _ _ (T127_108 i) (hfix127_108 i) _)
      ⟨127, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 15 hp) Q2.T127_108_2 Q2.hfix127_108_2 Q2.hinj127_108_2
      Q2.hcardT127_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_108_2 i) (Q2.hfix127_108_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨108, by decide⟩ 15 (transLenTr ⟨108, by decide⟩ 15 hp) : ↥(reps ⟨108, by decide⟩)) : Coordinate 1)
        T127_108 = colFn colCertDiv_127_108_15.D1 (m := 5) from colCertDiv_127_108_15.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨108, by decide⟩ 15 hp : ↥(Q2.reps ⟨108, by decide⟩)) : Coordinate 2)
        Q2.T127_108_2 = colFn colCertDiv_127_108_15.D2 (m := 5) from colCertDiv_127_108_15.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_108_15_match


theorem leaf_127_108_20 (hp : 20 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 20 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 20 (transLenTr ⟨108, by decide⟩ 20 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 20 (transLenTr ⟨108, by decide⟩ 20 hp)) T127_108
      hfix127_108 hinj127_108 hcardT127_108
      (fun i => conj_mem_of_fixedPoints _ _ (T127_108 i) (hfix127_108 i) _)
      ⟨127, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 20 hp) Q2.T127_108_2 Q2.hfix127_108_2 Q2.hinj127_108_2
      Q2.hcardT127_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_108_2 i) (Q2.hfix127_108_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨108, by decide⟩ 20 (transLenTr ⟨108, by decide⟩ 20 hp) : ↥(reps ⟨108, by decide⟩)) : Coordinate 1)
        T127_108 = colFn colCertDiv_127_108_20.D1 (m := 5) from colCertDiv_127_108_20.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨108, by decide⟩ 20 hp : ↥(Q2.reps ⟨108, by decide⟩)) : Coordinate 2)
        Q2.T127_108_2 = colFn colCertDiv_127_108_20.D2 (m := 5) from colCertDiv_127_108_20.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_108_20_match


theorem leaf_127_111_0 (hp : 0 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 0 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 0 (transLenTr ⟨111, by decide⟩ 0 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 0 (transLenTr ⟨111, by decide⟩ 0 hp)) T127_111
      hfix127_111 hinj127_111 hcardT127_111
      (fun i => conj_mem_of_fixedPoints _ _ (T127_111 i) (hfix127_111 i) _)
      ⟨127, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 0 hp) Q2.T127_111_2 Q2.hfix127_111_2 Q2.hinj127_111_2
      Q2.hcardT127_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_111_2 i) (Q2.hfix127_111_2 i) _)
      colCert_127_111_0.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_111_1 (hp : 1 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 1 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 1 (transLenTr ⟨111, by decide⟩ 1 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 1 (transLenTr ⟨111, by decide⟩ 1 hp)) T127_111
      hfix127_111 hinj127_111 hcardT127_111
      (fun i => conj_mem_of_fixedPoints _ _ (T127_111 i) (hfix127_111 i) _)
      ⟨127, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 1 hp) Q2.T127_111_2 Q2.hfix127_111_2 Q2.hinj127_111_2
      Q2.hcardT127_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_111_2 i) (Q2.hfix127_111_2 i) _)
      colCert_127_111_1.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_111_2 (hp : 2 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 2 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 2 (transLenTr ⟨111, by decide⟩ 2 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 2 (transLenTr ⟨111, by decide⟩ 2 hp)) T127_111
      hfix127_111 hinj127_111 hcardT127_111
      (fun i => conj_mem_of_fixedPoints _ _ (T127_111 i) (hfix127_111 i) _)
      ⟨127, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 2 hp) Q2.T127_111_2 Q2.hfix127_111_2 Q2.hinj127_111_2
      Q2.hcardT127_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_111_2 i) (Q2.hfix127_111_2 i) _)
      colCert_127_111_2.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_111_3 (hp : 3 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 3 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 3 (transLenTr ⟨111, by decide⟩ 3 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 3 (transLenTr ⟨111, by decide⟩ 3 hp)) T127_111
      hfix127_111 hinj127_111 hcardT127_111
      (fun i => conj_mem_of_fixedPoints _ _ (T127_111 i) (hfix127_111 i) _)
      ⟨127, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 3 hp) Q2.T127_111_2 Q2.hfix127_111_2 Q2.hinj127_111_2
      Q2.hcardT127_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_111_2 i) (Q2.hfix127_111_2 i) _)
      colCert_127_111_3.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_111_4 (hp : 4 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 4 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 4 (transLenTr ⟨111, by decide⟩ 4 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 4 (transLenTr ⟨111, by decide⟩ 4 hp)) T127_111
      hfix127_111 hinj127_111 hcardT127_111
      (fun i => conj_mem_of_fixedPoints _ _ (T127_111 i) (hfix127_111 i) _)
      ⟨127, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 4 hp) Q2.T127_111_2 Q2.hfix127_111_2 Q2.hinj127_111_2
      Q2.hcardT127_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_111_2 i) (Q2.hfix127_111_2 i) _)
      colCert_127_111_4.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_111_5 (hp : 5 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 5 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 5 (transLenTr ⟨111, by decide⟩ 5 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 5 (transLenTr ⟨111, by decide⟩ 5 hp)) T127_111
      hfix127_111 hinj127_111 hcardT127_111
      (fun i => conj_mem_of_fixedPoints _ _ (T127_111 i) (hfix127_111 i) _)
      ⟨127, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 5 hp) Q2.T127_111_2 Q2.hfix127_111_2 Q2.hinj127_111_2
      Q2.hcardT127_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_111_2 i) (Q2.hfix127_111_2 i) _)
      colCert_127_111_5.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_111_10 (hp : 10 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 10 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 10 (transLenTr ⟨111, by decide⟩ 10 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 10 (transLenTr ⟨111, by decide⟩ 10 hp)) T127_111
      hfix127_111 hinj127_111 hcardT127_111
      (fun i => conj_mem_of_fixedPoints _ _ (T127_111 i) (hfix127_111 i) _)
      ⟨127, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 10 hp) Q2.T127_111_2 Q2.hfix127_111_2 Q2.hinj127_111_2
      Q2.hcardT127_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_111_2 i) (Q2.hfix127_111_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨111, by decide⟩ 10 (transLenTr ⟨111, by decide⟩ 10 hp) : ↥(reps ⟨111, by decide⟩)) : Coordinate 1)
        T127_111 = colFn colCertDiv_127_111_10.D1 (m := 5) from colCertDiv_127_111_10.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨111, by decide⟩ 10 hp : ↥(Q2.reps ⟨111, by decide⟩)) : Coordinate 2)
        Q2.T127_111_2 = colFn colCertDiv_127_111_10.D2 (m := 5) from colCertDiv_127_111_10.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_111_10_match


theorem leaf_127_111_15 (hp : 15 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 15 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 15 (transLenTr ⟨111, by decide⟩ 15 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 15 (transLenTr ⟨111, by decide⟩ 15 hp)) T127_111
      hfix127_111 hinj127_111 hcardT127_111
      (fun i => conj_mem_of_fixedPoints _ _ (T127_111 i) (hfix127_111 i) _)
      ⟨127, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 15 hp) Q2.T127_111_2 Q2.hfix127_111_2 Q2.hinj127_111_2
      Q2.hcardT127_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_111_2 i) (Q2.hfix127_111_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨111, by decide⟩ 15 (transLenTr ⟨111, by decide⟩ 15 hp) : ↥(reps ⟨111, by decide⟩)) : Coordinate 1)
        T127_111 = colFn colCertDiv_127_111_15.D1 (m := 5) from colCertDiv_127_111_15.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨111, by decide⟩ 15 hp : ↥(Q2.reps ⟨111, by decide⟩)) : Coordinate 2)
        Q2.T127_111_2 = colFn colCertDiv_127_111_15.D2 (m := 5) from colCertDiv_127_111_15.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_111_15_match


theorem leaf_127_111_20 (hp : 20 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 20 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 20 (transLenTr ⟨111, by decide⟩ 20 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨127, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 20 (transLenTr ⟨111, by decide⟩ 20 hp)) T127_111
      hfix127_111 hinj127_111 hcardT127_111
      (fun i => conj_mem_of_fixedPoints _ _ (T127_111 i) (hfix127_111 i) _)
      ⟨127, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 20 hp) Q2.T127_111_2 Q2.hfix127_111_2 Q2.hinj127_111_2
      Q2.hcardT127_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_111_2 i) (Q2.hfix127_111_2 i) _)
      ?_).symm
  rw [show colData1 (⟨127, by decide⟩ : Fin 148)
        ((colE1 ⟨111, by decide⟩ 20 (transLenTr ⟨111, by decide⟩ 20 hp) : ↥(reps ⟨111, by decide⟩)) : Coordinate 1)
        T127_111 = colFn colCertDiv_127_111_20.D1 (m := 5) from colCertDiv_127_111_20.bind1,
    show colData2 (⟨127, by decide⟩ : Fin 148)
        ((colE2 ⟨111, by decide⟩ 20 hp : ↥(Q2.reps ⟨111, by decide⟩)) : Coordinate 2)
        Q2.T127_111_2 = colFn colCertDiv_127_111_20.D2 (m := 5) from colCertDiv_127_111_20.bind2]
  rw [alnId_127 j hj]
  exact fastcode_of_div ⟨127, by decide⟩ _ _ _
    ((alnId_127 j hj) ▸ Q2.listedAt (⟨127, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨127, by decide⟩ : Fin 148) hj hq).1) colCertDiv_127_111_20_match


theorem leaf_127_127_0 (hp : 0 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 0 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 0 (transLenTr ⟨127, by decide⟩ 0 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 0 (transLenTr ⟨127, by decide⟩ 0 hp)) T127_127
      hfix127_127 hinj127_127 hcardT127_127
      (fun i => conj_mem_of_fixedPoints _ _ (T127_127 i) (hfix127_127 i) _)
      ⟨127, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 0 hp) Q2.T127_127_2 Q2.hfix127_127_2 Q2.hinj127_127_2
      Q2.hcardT127_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_127_2 i) (Q2.hfix127_127_2 i) _)
      colCert_127_127_0.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_127_1 (hp : 1 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 1 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 1 (transLenTr ⟨127, by decide⟩ 1 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 1 (transLenTr ⟨127, by decide⟩ 1 hp)) T127_127
      hfix127_127 hinj127_127 hcardT127_127
      (fun i => conj_mem_of_fixedPoints _ _ (T127_127 i) (hfix127_127 i) _)
      ⟨127, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 1 hp) Q2.T127_127_2 Q2.hfix127_127_2 Q2.hinj127_127_2
      Q2.hcardT127_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_127_2 i) (Q2.hfix127_127_2 i) _)
      colCert_127_127_1.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_127_2 (hp : 2 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 2 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 2 (transLenTr ⟨127, by decide⟩ 2 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 2 (transLenTr ⟨127, by decide⟩ 2 hp)) T127_127
      hfix127_127 hinj127_127 hcardT127_127
      (fun i => conj_mem_of_fixedPoints _ _ (T127_127 i) (hfix127_127 i) _)
      ⟨127, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 2 hp) Q2.T127_127_2 Q2.hfix127_127_2 Q2.hinj127_127_2
      Q2.hcardT127_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_127_2 i) (Q2.hfix127_127_2 i) _)
      colCert_127_127_2.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_127_3 (hp : 3 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 3 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 3 (transLenTr ⟨127, by decide⟩ 3 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 3 (transLenTr ⟨127, by decide⟩ 3 hp)) T127_127
      hfix127_127 hinj127_127 hcardT127_127
      (fun i => conj_mem_of_fixedPoints _ _ (T127_127 i) (hfix127_127 i) _)
      ⟨127, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 3 hp) Q2.T127_127_2 Q2.hfix127_127_2 Q2.hinj127_127_2
      Q2.hcardT127_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_127_2 i) (Q2.hfix127_127_2 i) _)
      colCert_127_127_3.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_127_4 (hp : 4 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 4 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 4 (transLenTr ⟨127, by decide⟩ 4 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 4 (transLenTr ⟨127, by decide⟩ 4 hp)) T127_127
      hfix127_127 hinj127_127 hcardT127_127
      (fun i => conj_mem_of_fixedPoints _ _ (T127_127 i) (hfix127_127 i) _)
      ⟨127, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 4 hp) Q2.T127_127_2 Q2.hfix127_127_2 Q2.hinj127_127_2
      Q2.hcardT127_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_127_2 i) (Q2.hfix127_127_2 i) _)
      colCert_127_127_4.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_127_5 (hp : 5 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 5 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 5 (transLenTr ⟨127, by decide⟩ 5 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 5 (transLenTr ⟨127, by decide⟩ 5 hp)) T127_127
      hfix127_127 hinj127_127 hcardT127_127
      (fun i => conj_mem_of_fixedPoints _ _ (T127_127 i) (hfix127_127 i) _)
      ⟨127, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 5 hp) Q2.T127_127_2 Q2.hfix127_127_2 Q2.hinj127_127_2
      Q2.hcardT127_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_127_2 i) (Q2.hfix127_127_2 i) _)
      colCert_127_127_5.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_127_6 (hp : 6 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 6 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 6 (transLenTr ⟨127, by decide⟩ 6 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 6 (transLenTr ⟨127, by decide⟩ 6 hp)) T127_127
      hfix127_127 hinj127_127 hcardT127_127
      (fun i => conj_mem_of_fixedPoints _ _ (T127_127 i) (hfix127_127 i) _)
      ⟨127, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 6 hp) Q2.T127_127_2 Q2.hfix127_127_2 Q2.hinj127_127_2
      Q2.hcardT127_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_127_2 i) (Q2.hfix127_127_2 i) _)
      colCert_127_127_6.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_127_7 (hp : 7 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 7 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 7 (transLenTr ⟨127, by decide⟩ 7 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 7 (transLenTr ⟨127, by decide⟩ 7 hp)) T127_127
      hfix127_127 hinj127_127 hcardT127_127
      (fun i => conj_mem_of_fixedPoints _ _ (T127_127 i) (hfix127_127 i) _)
      ⟨127, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 7 hp) Q2.T127_127_2 Q2.hfix127_127_2 Q2.hinj127_127_2
      Q2.hcardT127_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_127_2 i) (Q2.hfix127_127_2 i) _)
      colCert_127_127_7.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_127_8 (hp : 8 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 8 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 8 (transLenTr ⟨127, by decide⟩ 8 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 8 (transLenTr ⟨127, by decide⟩ 8 hp)) T127_127
      hfix127_127 hinj127_127 hcardT127_127
      (fun i => conj_mem_of_fixedPoints _ _ (T127_127 i) (hfix127_127 i) _)
      ⟨127, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 8 hp) Q2.T127_127_2 Q2.hfix127_127_2 Q2.hinj127_127_2
      Q2.hcardT127_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_127_2 i) (Q2.hfix127_127_2 i) _)
      colCert_127_127_8.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_127_9 (hp : 9 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 9 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 9 (transLenTr ⟨127, by decide⟩ 9 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 9 (transLenTr ⟨127, by decide⟩ 9 hp)) T127_127
      hfix127_127 hinj127_127 hcardT127_127
      (fun i => conj_mem_of_fixedPoints _ _ (T127_127 i) (hfix127_127 i) _)
      ⟨127, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 9 hp) Q2.T127_127_2 Q2.hfix127_127_2 Q2.hinj127_127_2
      Q2.hcardT127_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_127_2 i) (Q2.hfix127_127_2 i) _)
      colCert_127_127_9.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_127_10 (hp : 10 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 10 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 10 (transLenTr ⟨127, by decide⟩ 10 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 10 (transLenTr ⟨127, by decide⟩ 10 hp)) T127_127
      hfix127_127 hinj127_127 hcardT127_127
      (fun i => conj_mem_of_fixedPoints _ _ (T127_127 i) (hfix127_127 i) _)
      ⟨127, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 10 hp) Q2.T127_127_2 Q2.hfix127_127_2 Q2.hinj127_127_2
      Q2.hcardT127_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_127_2 i) (Q2.hfix127_127_2 i) _)
      colCert_127_127_10.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_127_11 (hp : 11 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 11 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 11 (transLenTr ⟨127, by decide⟩ 11 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 11 (transLenTr ⟨127, by decide⟩ 11 hp)) T127_127
      hfix127_127 hinj127_127 hcardT127_127
      (fun i => conj_mem_of_fixedPoints _ _ (T127_127 i) (hfix127_127 i) _)
      ⟨127, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 11 hp) Q2.T127_127_2 Q2.hfix127_127_2 Q2.hinj127_127_2
      Q2.hcardT127_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_127_2 i) (Q2.hfix127_127_2 i) _)
      colCert_127_127_11.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_127_12 (hp : 12 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 12 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 12 (transLenTr ⟨127, by decide⟩ 12 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 12 (transLenTr ⟨127, by decide⟩ 12 hp)) T127_127
      hfix127_127 hinj127_127 hcardT127_127
      (fun i => conj_mem_of_fixedPoints _ _ (T127_127 i) (hfix127_127 i) _)
      ⟨127, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 12 hp) Q2.T127_127_2 Q2.hfix127_127_2 Q2.hinj127_127_2
      Q2.hcardT127_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_127_2 i) (Q2.hfix127_127_2 i) _)
      colCert_127_127_12.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_127_13 (hp : 13 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 13 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 13 (transLenTr ⟨127, by decide⟩ 13 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 13 (transLenTr ⟨127, by decide⟩ 13 hp)) T127_127
      hfix127_127 hinj127_127 hcardT127_127
      (fun i => conj_mem_of_fixedPoints _ _ (T127_127 i) (hfix127_127 i) _)
      ⟨127, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 13 hp) Q2.T127_127_2 Q2.hfix127_127_2 Q2.hinj127_127_2
      Q2.hcardT127_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_127_2 i) (Q2.hfix127_127_2 i) _)
      colCert_127_127_13.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_127_14 (hp : 14 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 14 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 14 (transLenTr ⟨127, by decide⟩ 14 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 14 (transLenTr ⟨127, by decide⟩ 14 hp)) T127_127
      hfix127_127 hinj127_127 hcardT127_127
      (fun i => conj_mem_of_fixedPoints _ _ (T127_127 i) (hfix127_127 i) _)
      ⟨127, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 14 hp) Q2.T127_127_2 Q2.hfix127_127_2 Q2.hinj127_127_2
      Q2.hcardT127_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_127_2 i) (Q2.hfix127_127_2 i) _)
      colCert_127_127_14.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_127_15 (hp : 15 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 15 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 15 (transLenTr ⟨127, by decide⟩ 15 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 15 (transLenTr ⟨127, by decide⟩ 15 hp)) T127_127
      hfix127_127 hinj127_127 hcardT127_127
      (fun i => conj_mem_of_fixedPoints _ _ (T127_127 i) (hfix127_127 i) _)
      ⟨127, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 15 hp) Q2.T127_127_2 Q2.hfix127_127_2 Q2.hinj127_127_2
      Q2.hcardT127_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_127_2 i) (Q2.hfix127_127_2 i) _)
      colCert_127_127_15.hD ?_).symm
  rw [alnId_127 j hj]


end LeanDring.P5Presentation
