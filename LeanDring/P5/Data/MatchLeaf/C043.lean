/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C020
import LeanDring.P5.Data.ColRestCheap.C086
import LeanDring.P5.Data.ColRestCheap.C087
import LeanDring.P5.Data.ColRestCheap.C088
import LeanDring.P5.Data.ColRestCheap.C089
import LeanDring.P5.Data.ColRestCheap.C090
import LeanDring.P5.Data.ColTau.C002
import LeanDring.P5.Data.EntryK.C039
import LeanDring.P5.Data.EntryK.C040
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C029
import LeanDring.P5.Data.SpeciesDiv.C030
import LeanDring.P5.Certificate.SpeciesTable.Twin2.SpeciesTau.Chunk03

/-! # Stage-5 leaves, chunk 42 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_140_46_20 (hp : 20 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 20 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp)) T140_46
      hfix140_46 hinj140_46 hcardT140_46
      (fun i => conj_mem_of_fixedPoints _ _ (T140_46 i) (hfix140_46 i) _)
      ⟨140, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 20 hp) Q2.T140_46_2 Q2.hfix140_46_2 Q2.hinj140_46_2
      Q2.hcardT140_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_46_2 i) (Q2.hfix140_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T140_46 = colFn colCertDiv_140_46_20.D1 (m := 5) from colCertDiv_140_46_20.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 20 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T140_46_2 = colFn colCertDiv_140_46_20.D2 (m := 5) from colCertDiv_140_46_20.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_46_20_match


theorem leaf_140_52_0 (hp : 0 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 0 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp)) T140_52
      hfix140_52 hinj140_52 hcardT140_52
      (fun i => conj_mem_of_fixedPoints _ _ (T140_52 i) (hfix140_52 i) _)
      ⟨140, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 0 hp) Q2.T140_52_2 Q2.hfix140_52_2 Q2.hinj140_52_2
      Q2.hcardT140_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_52_2 i) (Q2.hfix140_52_2 i) _)
      colCert_140_52_0.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_52_1 (hp : 1 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 1 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp)) T140_52
      hfix140_52 hinj140_52 hcardT140_52
      (fun i => conj_mem_of_fixedPoints _ _ (T140_52 i) (hfix140_52 i) _)
      ⟨140, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 1 hp) Q2.T140_52_2 Q2.hfix140_52_2 Q2.hinj140_52_2
      Q2.hcardT140_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_52_2 i) (Q2.hfix140_52_2 i) _)
      colCert_140_52_1.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_52_2 (hp : 2 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 2 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp)) T140_52
      hfix140_52 hinj140_52 hcardT140_52
      (fun i => conj_mem_of_fixedPoints _ _ (T140_52 i) (hfix140_52 i) _)
      ⟨140, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 2 hp) Q2.T140_52_2 Q2.hfix140_52_2 Q2.hinj140_52_2
      Q2.hcardT140_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_52_2 i) (Q2.hfix140_52_2 i) _)
      colCert_140_52_2.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_52_3 (hp : 3 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 3 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp)) T140_52
      hfix140_52 hinj140_52 hcardT140_52
      (fun i => conj_mem_of_fixedPoints _ _ (T140_52 i) (hfix140_52 i) _)
      ⟨140, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 3 hp) Q2.T140_52_2 Q2.hfix140_52_2 Q2.hinj140_52_2
      Q2.hcardT140_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_52_2 i) (Q2.hfix140_52_2 i) _)
      colCert_140_52_3.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_52_4 (hp : 4 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 4 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp)) T140_52
      hfix140_52 hinj140_52 hcardT140_52
      (fun i => conj_mem_of_fixedPoints _ _ (T140_52 i) (hfix140_52 i) _)
      ⟨140, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 4 hp) Q2.T140_52_2 Q2.hfix140_52_2 Q2.hinj140_52_2
      Q2.hcardT140_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_52_2 i) (Q2.hfix140_52_2 i) _)
      colCert_140_52_4.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_52_5 (hp : 5 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 5 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp)) T140_52
      hfix140_52 hinj140_52 hcardT140_52
      (fun i => conj_mem_of_fixedPoints _ _ (T140_52 i) (hfix140_52 i) _)
      ⟨140, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 5 hp) Q2.T140_52_2 Q2.hfix140_52_2 Q2.hinj140_52_2
      Q2.hcardT140_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_52_2 i) (Q2.hfix140_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T140_52 = colFn colCertDiv_140_52_5.D1 (m := 5) from colCertDiv_140_52_5.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 5 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T140_52_2 = colFn colCertDiv_140_52_5.D2 (m := 5) from colCertDiv_140_52_5.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_52_5_match


theorem leaf_140_52_10 (hp : 10 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 10 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp)) T140_52
      hfix140_52 hinj140_52 hcardT140_52
      (fun i => conj_mem_of_fixedPoints _ _ (T140_52 i) (hfix140_52 i) _)
      ⟨140, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 10 hp) Q2.T140_52_2 Q2.hfix140_52_2 Q2.hinj140_52_2
      Q2.hcardT140_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_52_2 i) (Q2.hfix140_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T140_52 = colFn colCertDiv_140_52_10.D1 (m := 5) from colCertDiv_140_52_10.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 10 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T140_52_2 = colFn colCertDiv_140_52_10.D2 (m := 5) from colCertDiv_140_52_10.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_52_10_match


theorem leaf_140_52_15 (hp : 15 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 15 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp)) T140_52
      hfix140_52 hinj140_52 hcardT140_52
      (fun i => conj_mem_of_fixedPoints _ _ (T140_52 i) (hfix140_52 i) _)
      ⟨140, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 15 hp) Q2.T140_52_2 Q2.hfix140_52_2 Q2.hinj140_52_2
      Q2.hcardT140_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_52_2 i) (Q2.hfix140_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T140_52 = colFn colCertDiv_140_52_15.D1 (m := 5) from colCertDiv_140_52_15.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 15 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T140_52_2 = colFn colCertDiv_140_52_15.D2 (m := 5) from colCertDiv_140_52_15.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_52_15_match


theorem leaf_140_52_20 (hp : 20 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 20 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp)) T140_52
      hfix140_52 hinj140_52 hcardT140_52
      (fun i => conj_mem_of_fixedPoints _ _ (T140_52 i) (hfix140_52 i) _)
      ⟨140, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 20 hp) Q2.T140_52_2 Q2.hfix140_52_2 Q2.hinj140_52_2
      Q2.hcardT140_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_52_2 i) (Q2.hfix140_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T140_52 = colFn colCertDiv_140_52_20.D1 (m := 5) from colCertDiv_140_52_20.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 20 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T140_52_2 = colFn colCertDiv_140_52_20.D2 (m := 5) from colCertDiv_140_52_20.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_52_20_match


theorem leaf_140_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T140_53
      hfix140_53 hinj140_53 hcardT140_53
      (fun i => conj_mem_of_fixedPoints _ _ (T140_53 i) (hfix140_53 i) _)
      ⟨140, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T140_53_2 Q2.hfix140_53_2 Q2.hinj140_53_2
      Q2.hcardT140_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_53_2 i) (Q2.hfix140_53_2 i) _)
      colCert_140_53_0.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T140_53
      hfix140_53 hinj140_53 hcardT140_53
      (fun i => conj_mem_of_fixedPoints _ _ (T140_53 i) (hfix140_53 i) _)
      ⟨140, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T140_53_2 Q2.hfix140_53_2 Q2.hinj140_53_2
      Q2.hcardT140_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_53_2 i) (Q2.hfix140_53_2 i) _)
      colCert_140_53_1.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T140_53
      hfix140_53 hinj140_53 hcardT140_53
      (fun i => conj_mem_of_fixedPoints _ _ (T140_53 i) (hfix140_53 i) _)
      ⟨140, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T140_53_2 Q2.hfix140_53_2 Q2.hinj140_53_2
      Q2.hcardT140_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_53_2 i) (Q2.hfix140_53_2 i) _)
      colCert_140_53_2.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T140_53
      hfix140_53 hinj140_53 hcardT140_53
      (fun i => conj_mem_of_fixedPoints _ _ (T140_53 i) (hfix140_53 i) _)
      ⟨140, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T140_53_2 Q2.hfix140_53_2 Q2.hinj140_53_2
      Q2.hcardT140_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_53_2 i) (Q2.hfix140_53_2 i) _)
      colCert_140_53_3.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T140_53
      hfix140_53 hinj140_53 hcardT140_53
      (fun i => conj_mem_of_fixedPoints _ _ (T140_53 i) (hfix140_53 i) _)
      ⟨140, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T140_53_2 Q2.hfix140_53_2 Q2.hinj140_53_2
      Q2.hcardT140_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_53_2 i) (Q2.hfix140_53_2 i) _)
      colCert_140_53_4.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T140_53
      hfix140_53 hinj140_53 hcardT140_53
      (fun i => conj_mem_of_fixedPoints _ _ (T140_53 i) (hfix140_53 i) _)
      ⟨140, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T140_53_2 Q2.hfix140_53_2 Q2.hinj140_53_2
      Q2.hcardT140_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_53_2 i) (Q2.hfix140_53_2 i) _)
      colCert_140_53_5.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T140_53
      hfix140_53 hinj140_53 hcardT140_53
      (fun i => conj_mem_of_fixedPoints _ _ (T140_53 i) (hfix140_53 i) _)
      ⟨140, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T140_53_2 Q2.hfix140_53_2 Q2.hinj140_53_2
      Q2.hcardT140_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_53_2 i) (Q2.hfix140_53_2 i) _)
      colCert_140_53_10.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T140_53
      hfix140_53 hinj140_53 hcardT140_53
      (fun i => conj_mem_of_fixedPoints _ _ (T140_53 i) (hfix140_53 i) _)
      ⟨140, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T140_53_2 Q2.hfix140_53_2 Q2.hinj140_53_2
      Q2.hcardT140_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_53_2 i) (Q2.hfix140_53_2 i) _)
      colCert_140_53_15.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T140_53
      hfix140_53 hinj140_53 hcardT140_53
      (fun i => conj_mem_of_fixedPoints _ _ (T140_53 i) (hfix140_53 i) _)
      ⟨140, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T140_53_2 Q2.hfix140_53_2 Q2.hinj140_53_2
      Q2.hcardT140_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_53_2 i) (Q2.hfix140_53_2 i) _)
      colCert_140_53_20.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_84_0 (hp : 0 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 0 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 0 (transLenTr ⟨84, by decide⟩ 0 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 0 (transLenTr ⟨84, by decide⟩ 0 hp)) T140_84
      hfix140_84 hinj140_84 hcardT140_84
      (fun i => conj_mem_of_fixedPoints _ _ (T140_84 i) (hfix140_84 i) _)
      ⟨140, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 0 hp) Q2.T140_84_2 Q2.hfix140_84_2 Q2.hinj140_84_2
      Q2.hcardT140_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_84_2 i) (Q2.hfix140_84_2 i) _)
      colCert_140_84_0.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_84_1 (hp : 1 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 1 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 1 (transLenTr ⟨84, by decide⟩ 1 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 1 (transLenTr ⟨84, by decide⟩ 1 hp)) T140_84
      hfix140_84 hinj140_84 hcardT140_84
      (fun i => conj_mem_of_fixedPoints _ _ (T140_84 i) (hfix140_84 i) _)
      ⟨140, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 1 hp) Q2.T140_84_2 Q2.hfix140_84_2 Q2.hinj140_84_2
      Q2.hcardT140_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_84_2 i) (Q2.hfix140_84_2 i) _)
      colCert_140_84_1.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_84_2 (hp : 2 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 2 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 2 (transLenTr ⟨84, by decide⟩ 2 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 2 (transLenTr ⟨84, by decide⟩ 2 hp)) T140_84
      hfix140_84 hinj140_84 hcardT140_84
      (fun i => conj_mem_of_fixedPoints _ _ (T140_84 i) (hfix140_84 i) _)
      ⟨140, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 2 hp) Q2.T140_84_2 Q2.hfix140_84_2 Q2.hinj140_84_2
      Q2.hcardT140_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_84_2 i) (Q2.hfix140_84_2 i) _)
      colCert_140_84_2.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_84_3 (hp : 3 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 3 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 3 (transLenTr ⟨84, by decide⟩ 3 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 3 (transLenTr ⟨84, by decide⟩ 3 hp)) T140_84
      hfix140_84 hinj140_84 hcardT140_84
      (fun i => conj_mem_of_fixedPoints _ _ (T140_84 i) (hfix140_84 i) _)
      ⟨140, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 3 hp) Q2.T140_84_2 Q2.hfix140_84_2 Q2.hinj140_84_2
      Q2.hcardT140_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_84_2 i) (Q2.hfix140_84_2 i) _)
      colCert_140_84_3.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_84_4 (hp : 4 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 4 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 4 (transLenTr ⟨84, by decide⟩ 4 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 4 (transLenTr ⟨84, by decide⟩ 4 hp)) T140_84
      hfix140_84 hinj140_84 hcardT140_84
      (fun i => conj_mem_of_fixedPoints _ _ (T140_84 i) (hfix140_84 i) _)
      ⟨140, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 4 hp) Q2.T140_84_2 Q2.hfix140_84_2 Q2.hinj140_84_2
      Q2.hcardT140_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_84_2 i) (Q2.hfix140_84_2 i) _)
      colCert_140_84_4.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_84_5 (hp : 5 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 5 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 5 (transLenTr ⟨84, by decide⟩ 5 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 5 (transLenTr ⟨84, by decide⟩ 5 hp)) T140_84
      hfix140_84 hinj140_84 hcardT140_84
      (fun i => conj_mem_of_fixedPoints _ _ (T140_84 i) (hfix140_84 i) _)
      ⟨140, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 5 hp) Q2.T140_84_2 Q2.hfix140_84_2 Q2.hinj140_84_2
      Q2.hcardT140_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_84_2 i) (Q2.hfix140_84_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨84, by decide⟩ 5 (transLenTr ⟨84, by decide⟩ 5 hp) : ↥(reps ⟨84, by decide⟩)) : Coordinate 1)
        T140_84 = colFn colCertDiv_140_84_5.D1 (m := 5) from colCertDiv_140_84_5.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨84, by decide⟩ 5 hp : ↥(Q2.reps ⟨84, by decide⟩)) : Coordinate 2)
        Q2.T140_84_2 = colFn colCertDiv_140_84_5.D2 (m := 5) from colCertDiv_140_84_5.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_84_5_match


theorem leaf_140_84_10 (hp : 10 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 10 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 10 (transLenTr ⟨84, by decide⟩ 10 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 10 (transLenTr ⟨84, by decide⟩ 10 hp)) T140_84
      hfix140_84 hinj140_84 hcardT140_84
      (fun i => conj_mem_of_fixedPoints _ _ (T140_84 i) (hfix140_84 i) _)
      ⟨140, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 10 hp) Q2.T140_84_2 Q2.hfix140_84_2 Q2.hinj140_84_2
      Q2.hcardT140_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_84_2 i) (Q2.hfix140_84_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨84, by decide⟩ 10 (transLenTr ⟨84, by decide⟩ 10 hp) : ↥(reps ⟨84, by decide⟩)) : Coordinate 1)
        T140_84 = colFn colCertDiv_140_84_10.D1 (m := 5) from colCertDiv_140_84_10.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨84, by decide⟩ 10 hp : ↥(Q2.reps ⟨84, by decide⟩)) : Coordinate 2)
        Q2.T140_84_2 = colFn colCertDiv_140_84_10.D2 (m := 5) from colCertDiv_140_84_10.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_84_10_match


theorem leaf_140_84_15 (hp : 15 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 15 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 15 (transLenTr ⟨84, by decide⟩ 15 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 15 (transLenTr ⟨84, by decide⟩ 15 hp)) T140_84
      hfix140_84 hinj140_84 hcardT140_84
      (fun i => conj_mem_of_fixedPoints _ _ (T140_84 i) (hfix140_84 i) _)
      ⟨140, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 15 hp) Q2.T140_84_2 Q2.hfix140_84_2 Q2.hinj140_84_2
      Q2.hcardT140_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_84_2 i) (Q2.hfix140_84_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨84, by decide⟩ 15 (transLenTr ⟨84, by decide⟩ 15 hp) : ↥(reps ⟨84, by decide⟩)) : Coordinate 1)
        T140_84 = colFn colCertDiv_140_84_15.D1 (m := 5) from colCertDiv_140_84_15.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨84, by decide⟩ 15 hp : ↥(Q2.reps ⟨84, by decide⟩)) : Coordinate 2)
        Q2.T140_84_2 = colFn colCertDiv_140_84_15.D2 (m := 5) from colCertDiv_140_84_15.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_84_15_match


theorem leaf_140_84_20 (hp : 20 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 20 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 20 (transLenTr ⟨84, by decide⟩ 20 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 20 (transLenTr ⟨84, by decide⟩ 20 hp)) T140_84
      hfix140_84 hinj140_84 hcardT140_84
      (fun i => conj_mem_of_fixedPoints _ _ (T140_84 i) (hfix140_84 i) _)
      ⟨140, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 20 hp) Q2.T140_84_2 Q2.hfix140_84_2 Q2.hinj140_84_2
      Q2.hcardT140_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_84_2 i) (Q2.hfix140_84_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨84, by decide⟩ 20 (transLenTr ⟨84, by decide⟩ 20 hp) : ↥(reps ⟨84, by decide⟩)) : Coordinate 1)
        T140_84 = colFn colCertDiv_140_84_20.D1 (m := 5) from colCertDiv_140_84_20.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨84, by decide⟩ 20 hp : ↥(Q2.reps ⟨84, by decide⟩)) : Coordinate 2)
        Q2.T140_84_2 = colFn colCertDiv_140_84_20.D2 (m := 5) from colCertDiv_140_84_20.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_84_20_match


theorem leaf_140_90_0 (hp : 0 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 0 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 0 (transLenTr ⟨90, by decide⟩ 0 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 0 (transLenTr ⟨90, by decide⟩ 0 hp)) T140_90
      hfix140_90 hinj140_90 hcardT140_90
      (fun i => conj_mem_of_fixedPoints _ _ (T140_90 i) (hfix140_90 i) _)
      ⟨140, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 0 hp) Q2.T140_90_2 Q2.hfix140_90_2 Q2.hinj140_90_2
      Q2.hcardT140_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_90_2 i) (Q2.hfix140_90_2 i) _)
      colCert_140_90_0.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_90_1 (hp : 1 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 1 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 1 (transLenTr ⟨90, by decide⟩ 1 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 1 (transLenTr ⟨90, by decide⟩ 1 hp)) T140_90
      hfix140_90 hinj140_90 hcardT140_90
      (fun i => conj_mem_of_fixedPoints _ _ (T140_90 i) (hfix140_90 i) _)
      ⟨140, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 1 hp) Q2.T140_90_2 Q2.hfix140_90_2 Q2.hinj140_90_2
      Q2.hcardT140_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_90_2 i) (Q2.hfix140_90_2 i) _)
      colCert_140_90_1.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_90_2 (hp : 2 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 2 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 2 (transLenTr ⟨90, by decide⟩ 2 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 2 (transLenTr ⟨90, by decide⟩ 2 hp)) T140_90
      hfix140_90 hinj140_90 hcardT140_90
      (fun i => conj_mem_of_fixedPoints _ _ (T140_90 i) (hfix140_90 i) _)
      ⟨140, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 2 hp) Q2.T140_90_2 Q2.hfix140_90_2 Q2.hinj140_90_2
      Q2.hcardT140_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_90_2 i) (Q2.hfix140_90_2 i) _)
      colCert_140_90_2.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_90_3 (hp : 3 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 3 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 3 (transLenTr ⟨90, by decide⟩ 3 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 3 (transLenTr ⟨90, by decide⟩ 3 hp)) T140_90
      hfix140_90 hinj140_90 hcardT140_90
      (fun i => conj_mem_of_fixedPoints _ _ (T140_90 i) (hfix140_90 i) _)
      ⟨140, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 3 hp) Q2.T140_90_2 Q2.hfix140_90_2 Q2.hinj140_90_2
      Q2.hcardT140_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_90_2 i) (Q2.hfix140_90_2 i) _)
      colCert_140_90_3.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_90_4 (hp : 4 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 4 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 4 (transLenTr ⟨90, by decide⟩ 4 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 4 (transLenTr ⟨90, by decide⟩ 4 hp)) T140_90
      hfix140_90 hinj140_90 hcardT140_90
      (fun i => conj_mem_of_fixedPoints _ _ (T140_90 i) (hfix140_90 i) _)
      ⟨140, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 4 hp) Q2.T140_90_2 Q2.hfix140_90_2 Q2.hinj140_90_2
      Q2.hcardT140_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_90_2 i) (Q2.hfix140_90_2 i) _)
      colCert_140_90_4.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_90_5 (hp : 5 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 5 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 5 (transLenTr ⟨90, by decide⟩ 5 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 5 (transLenTr ⟨90, by decide⟩ 5 hp)) T140_90
      hfix140_90 hinj140_90 hcardT140_90
      (fun i => conj_mem_of_fixedPoints _ _ (T140_90 i) (hfix140_90 i) _)
      ⟨140, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 5 hp) Q2.T140_90_2 Q2.hfix140_90_2 Q2.hinj140_90_2
      Q2.hcardT140_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_90_2 i) (Q2.hfix140_90_2 i) _)
      colCert_140_90_5.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_90_10 (hp : 10 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 10 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 10 (transLenTr ⟨90, by decide⟩ 10 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 10 (transLenTr ⟨90, by decide⟩ 10 hp)) T140_90
      hfix140_90 hinj140_90 hcardT140_90
      (fun i => conj_mem_of_fixedPoints _ _ (T140_90 i) (hfix140_90 i) _)
      ⟨140, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 10 hp) Q2.T140_90_2 Q2.hfix140_90_2 Q2.hinj140_90_2
      Q2.hcardT140_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_90_2 i) (Q2.hfix140_90_2 i) _)
      colCert_140_90_10.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_90_15 (hp : 15 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 15 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 15 (transLenTr ⟨90, by decide⟩ 15 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 15 (transLenTr ⟨90, by decide⟩ 15 hp)) T140_90
      hfix140_90 hinj140_90 hcardT140_90
      (fun i => conj_mem_of_fixedPoints _ _ (T140_90 i) (hfix140_90 i) _)
      ⟨140, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 15 hp) Q2.T140_90_2 Q2.hfix140_90_2 Q2.hinj140_90_2
      Q2.hcardT140_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_90_2 i) (Q2.hfix140_90_2 i) _)
      colCert_140_90_15.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_90_20 (hp : 20 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 20 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 20 (transLenTr ⟨90, by decide⟩ 20 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 20 (transLenTr ⟨90, by decide⟩ 20 hp)) T140_90
      hfix140_90 hinj140_90 hcardT140_90
      (fun i => conj_mem_of_fixedPoints _ _ (T140_90 i) (hfix140_90 i) _)
      ⟨140, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 20 hp) Q2.T140_90_2 Q2.hfix140_90_2 Q2.hinj140_90_2
      Q2.hcardT140_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_90_2 i) (Q2.hfix140_90_2 i) _)
      colCert_140_90_20.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_90_25 (hp : 25 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 25 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 25 (transLenTr ⟨90, by decide⟩ 25 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 25 (transLenTr ⟨90, by decide⟩ 25 hp)) T140_90
      hfix140_90 hinj140_90 hcardT140_90
      (fun i => conj_mem_of_fixedPoints _ _ (T140_90 i) (hfix140_90 i) _)
      ⟨140, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 25 hp) Q2.T140_90_2 Q2.hfix140_90_2 Q2.hinj140_90_2
      Q2.hcardT140_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_90_2 i) (Q2.hfix140_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 25 (transLenTr ⟨90, by decide⟩ 25 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T140_90 = colFn colCertDiv_140_90_25.D1 (m := 5) from colCertDiv_140_90_25.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 25 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T140_90_2 = colFn colCertDiv_140_90_25.D2 (m := 5) from colCertDiv_140_90_25.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_90_25_match


theorem leaf_140_90_50 (hp : 50 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 50 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 50 (transLenTr ⟨90, by decide⟩ 50 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 50 (transLenTr ⟨90, by decide⟩ 50 hp)) T140_90
      hfix140_90 hinj140_90 hcardT140_90
      (fun i => conj_mem_of_fixedPoints _ _ (T140_90 i) (hfix140_90 i) _)
      ⟨140, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 50 hp) Q2.T140_90_2 Q2.hfix140_90_2 Q2.hinj140_90_2
      Q2.hcardT140_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_90_2 i) (Q2.hfix140_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 50 (transLenTr ⟨90, by decide⟩ 50 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T140_90 = colFn colCertDiv_140_90_50.D1 (m := 5) from colCertDiv_140_90_50.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 50 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T140_90_2 = colFn colCertDiv_140_90_50.D2 (m := 5) from colCertDiv_140_90_50.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_90_50_match


theorem leaf_140_90_75 (hp : 75 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 75 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 75 (transLenTr ⟨90, by decide⟩ 75 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 75 (transLenTr ⟨90, by decide⟩ 75 hp)) T140_90
      hfix140_90 hinj140_90 hcardT140_90
      (fun i => conj_mem_of_fixedPoints _ _ (T140_90 i) (hfix140_90 i) _)
      ⟨140, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 75 hp) Q2.T140_90_2 Q2.hfix140_90_2 Q2.hinj140_90_2
      Q2.hcardT140_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_90_2 i) (Q2.hfix140_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 75 (transLenTr ⟨90, by decide⟩ 75 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T140_90 = colFn colCertDiv_140_90_75.D1 (m := 5) from colCertDiv_140_90_75.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 75 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T140_90_2 = colFn colCertDiv_140_90_75.D2 (m := 5) from colCertDiv_140_90_75.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_90_75_match


theorem leaf_140_90_100 (hp : 100 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 100 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 100 (transLenTr ⟨90, by decide⟩ 100 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 100 (transLenTr ⟨90, by decide⟩ 100 hp)) T140_90
      hfix140_90 hinj140_90 hcardT140_90
      (fun i => conj_mem_of_fixedPoints _ _ (T140_90 i) (hfix140_90 i) _)
      ⟨140, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 100 hp) Q2.T140_90_2 Q2.hfix140_90_2 Q2.hinj140_90_2
      Q2.hcardT140_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_90_2 i) (Q2.hfix140_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 100 (transLenTr ⟨90, by decide⟩ 100 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T140_90 = colFn colCertDiv_140_90_100.D1 (m := 5) from colCertDiv_140_90_100.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 100 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T140_90_2 = colFn colCertDiv_140_90_100.D2 (m := 5) from colCertDiv_140_90_100.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_90_100_match


theorem leaf_140_97_0 (hp : 0 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 0 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 0 (transLenTr ⟨97, by decide⟩ 0 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 0 (transLenTr ⟨97, by decide⟩ 0 hp)) T140_97
      hfix140_97 hinj140_97 hcardT140_97
      (fun i => conj_mem_of_fixedPoints _ _ (T140_97 i) (hfix140_97 i) _)
      ⟨140, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 0 hp) Q2.T140_97_2 Q2.hfix140_97_2 Q2.hinj140_97_2
      Q2.hcardT140_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_97_2 i) (Q2.hfix140_97_2 i) _)
      colCert_140_97_0.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_97_1 (hp : 1 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 1 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 1 (transLenTr ⟨97, by decide⟩ 1 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 1 (transLenTr ⟨97, by decide⟩ 1 hp)) T140_97
      hfix140_97 hinj140_97 hcardT140_97
      (fun i => conj_mem_of_fixedPoints _ _ (T140_97 i) (hfix140_97 i) _)
      ⟨140, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 1 hp) Q2.T140_97_2 Q2.hfix140_97_2 Q2.hinj140_97_2
      Q2.hcardT140_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_97_2 i) (Q2.hfix140_97_2 i) _)
      colCert_140_97_1.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_97_2 (hp : 2 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 2 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 2 (transLenTr ⟨97, by decide⟩ 2 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 2 (transLenTr ⟨97, by decide⟩ 2 hp)) T140_97
      hfix140_97 hinj140_97 hcardT140_97
      (fun i => conj_mem_of_fixedPoints _ _ (T140_97 i) (hfix140_97 i) _)
      ⟨140, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 2 hp) Q2.T140_97_2 Q2.hfix140_97_2 Q2.hinj140_97_2
      Q2.hcardT140_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_97_2 i) (Q2.hfix140_97_2 i) _)
      colCert_140_97_2.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_97_3 (hp : 3 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 3 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 3 (transLenTr ⟨97, by decide⟩ 3 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 3 (transLenTr ⟨97, by decide⟩ 3 hp)) T140_97
      hfix140_97 hinj140_97 hcardT140_97
      (fun i => conj_mem_of_fixedPoints _ _ (T140_97 i) (hfix140_97 i) _)
      ⟨140, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 3 hp) Q2.T140_97_2 Q2.hfix140_97_2 Q2.hinj140_97_2
      Q2.hcardT140_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_97_2 i) (Q2.hfix140_97_2 i) _)
      colCert_140_97_3.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_97_4 (hp : 4 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 4 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 4 (transLenTr ⟨97, by decide⟩ 4 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 4 (transLenTr ⟨97, by decide⟩ 4 hp)) T140_97
      hfix140_97 hinj140_97 hcardT140_97
      (fun i => conj_mem_of_fixedPoints _ _ (T140_97 i) (hfix140_97 i) _)
      ⟨140, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 4 hp) Q2.T140_97_2 Q2.hfix140_97_2 Q2.hinj140_97_2
      Q2.hcardT140_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_97_2 i) (Q2.hfix140_97_2 i) _)
      colCert_140_97_4.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_97_5 (hp : 5 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 5 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 5 (transLenTr ⟨97, by decide⟩ 5 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 5 (transLenTr ⟨97, by decide⟩ 5 hp)) T140_97
      hfix140_97 hinj140_97 hcardT140_97
      (fun i => conj_mem_of_fixedPoints _ _ (T140_97 i) (hfix140_97 i) _)
      ⟨140, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 5 hp) Q2.T140_97_2 Q2.hfix140_97_2 Q2.hinj140_97_2
      Q2.hcardT140_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_97_2 i) (Q2.hfix140_97_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨97, by decide⟩ 5 (transLenTr ⟨97, by decide⟩ 5 hp) : ↥(reps ⟨97, by decide⟩)) : Coordinate 1)
        T140_97 = colFn colCertDiv_140_97_5.D1 (m := 5) from colCertDiv_140_97_5.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨97, by decide⟩ 5 hp : ↥(Q2.reps ⟨97, by decide⟩)) : Coordinate 2)
        Q2.T140_97_2 = colFn colCertDiv_140_97_5.D2 (m := 5) from colCertDiv_140_97_5.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_97_5_match


theorem leaf_140_97_10 (hp : 10 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 10 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 10 (transLenTr ⟨97, by decide⟩ 10 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 10 (transLenTr ⟨97, by decide⟩ 10 hp)) T140_97
      hfix140_97 hinj140_97 hcardT140_97
      (fun i => conj_mem_of_fixedPoints _ _ (T140_97 i) (hfix140_97 i) _)
      ⟨140, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 10 hp) Q2.T140_97_2 Q2.hfix140_97_2 Q2.hinj140_97_2
      Q2.hcardT140_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_97_2 i) (Q2.hfix140_97_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨97, by decide⟩ 10 (transLenTr ⟨97, by decide⟩ 10 hp) : ↥(reps ⟨97, by decide⟩)) : Coordinate 1)
        T140_97 = colFn colCertDiv_140_97_10.D1 (m := 5) from colCertDiv_140_97_10.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨97, by decide⟩ 10 hp : ↥(Q2.reps ⟨97, by decide⟩)) : Coordinate 2)
        Q2.T140_97_2 = colFn colCertDiv_140_97_10.D2 (m := 5) from colCertDiv_140_97_10.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_97_10_match


theorem leaf_140_97_15 (hp : 15 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 15 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 15 (transLenTr ⟨97, by decide⟩ 15 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 15 (transLenTr ⟨97, by decide⟩ 15 hp)) T140_97
      hfix140_97 hinj140_97 hcardT140_97
      (fun i => conj_mem_of_fixedPoints _ _ (T140_97 i) (hfix140_97 i) _)
      ⟨140, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 15 hp) Q2.T140_97_2 Q2.hfix140_97_2 Q2.hinj140_97_2
      Q2.hcardT140_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_97_2 i) (Q2.hfix140_97_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨97, by decide⟩ 15 (transLenTr ⟨97, by decide⟩ 15 hp) : ↥(reps ⟨97, by decide⟩)) : Coordinate 1)
        T140_97 = colFn colCertDiv_140_97_15.D1 (m := 5) from colCertDiv_140_97_15.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨97, by decide⟩ 15 hp : ↥(Q2.reps ⟨97, by decide⟩)) : Coordinate 2)
        Q2.T140_97_2 = colFn colCertDiv_140_97_15.D2 (m := 5) from colCertDiv_140_97_15.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_97_15_match


theorem leaf_140_97_20 (hp : 20 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 20 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 20 (transLenTr ⟨97, by decide⟩ 20 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 20 (transLenTr ⟨97, by decide⟩ 20 hp)) T140_97
      hfix140_97 hinj140_97 hcardT140_97
      (fun i => conj_mem_of_fixedPoints _ _ (T140_97 i) (hfix140_97 i) _)
      ⟨140, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 20 hp) Q2.T140_97_2 Q2.hfix140_97_2 Q2.hinj140_97_2
      Q2.hcardT140_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_97_2 i) (Q2.hfix140_97_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨97, by decide⟩ 20 (transLenTr ⟨97, by decide⟩ 20 hp) : ↥(reps ⟨97, by decide⟩)) : Coordinate 1)
        T140_97 = colFn colCertDiv_140_97_20.D1 (m := 5) from colCertDiv_140_97_20.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨97, by decide⟩ 20 hp : ↥(Q2.reps ⟨97, by decide⟩)) : Coordinate 2)
        Q2.T140_97_2 = colFn colCertDiv_140_97_20.D2 (m := 5) from colCertDiv_140_97_20.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_97_20_match


theorem leaf_140_101_0 (hp : 0 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 0 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 0 (transLenTr ⟨101, by decide⟩ 0 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 0 (transLenTr ⟨101, by decide⟩ 0 hp)) T140_101
      hfix140_101 hinj140_101 hcardT140_101
      (fun i => conj_mem_of_fixedPoints _ _ (T140_101 i) (hfix140_101 i) _)
      ⟨140, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 0 hp) Q2.T140_101_2 Q2.hfix140_101_2 Q2.hinj140_101_2
      Q2.hcardT140_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_101_2 i) (Q2.hfix140_101_2 i) _)
      colCert_140_101_0.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_101_1 (hp : 1 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 1 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 1 (transLenTr ⟨101, by decide⟩ 1 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 1 (transLenTr ⟨101, by decide⟩ 1 hp)) T140_101
      hfix140_101 hinj140_101 hcardT140_101
      (fun i => conj_mem_of_fixedPoints _ _ (T140_101 i) (hfix140_101 i) _)
      ⟨140, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 1 hp) Q2.T140_101_2 Q2.hfix140_101_2 Q2.hinj140_101_2
      Q2.hcardT140_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_101_2 i) (Q2.hfix140_101_2 i) _)
      colCert_140_101_1.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_101_2 (hp : 2 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 2 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 2 (transLenTr ⟨101, by decide⟩ 2 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 2 (transLenTr ⟨101, by decide⟩ 2 hp)) T140_101
      hfix140_101 hinj140_101 hcardT140_101
      (fun i => conj_mem_of_fixedPoints _ _ (T140_101 i) (hfix140_101 i) _)
      ⟨140, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 2 hp) Q2.T140_101_2 Q2.hfix140_101_2 Q2.hinj140_101_2
      Q2.hcardT140_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_101_2 i) (Q2.hfix140_101_2 i) _)
      colCert_140_101_2.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_101_3 (hp : 3 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 3 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 3 (transLenTr ⟨101, by decide⟩ 3 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 3 (transLenTr ⟨101, by decide⟩ 3 hp)) T140_101
      hfix140_101 hinj140_101 hcardT140_101
      (fun i => conj_mem_of_fixedPoints _ _ (T140_101 i) (hfix140_101 i) _)
      ⟨140, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 3 hp) Q2.T140_101_2 Q2.hfix140_101_2 Q2.hinj140_101_2
      Q2.hcardT140_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_101_2 i) (Q2.hfix140_101_2 i) _)
      colCert_140_101_3.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_101_4 (hp : 4 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 4 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 4 (transLenTr ⟨101, by decide⟩ 4 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 4 (transLenTr ⟨101, by decide⟩ 4 hp)) T140_101
      hfix140_101 hinj140_101 hcardT140_101
      (fun i => conj_mem_of_fixedPoints _ _ (T140_101 i) (hfix140_101 i) _)
      ⟨140, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 4 hp) Q2.T140_101_2 Q2.hfix140_101_2 Q2.hinj140_101_2
      Q2.hcardT140_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_101_2 i) (Q2.hfix140_101_2 i) _)
      colCert_140_101_4.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_101_5 (hp : 5 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 5 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 5 (transLenTr ⟨101, by decide⟩ 5 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 5 (transLenTr ⟨101, by decide⟩ 5 hp)) T140_101
      hfix140_101 hinj140_101 hcardT140_101
      (fun i => conj_mem_of_fixedPoints _ _ (T140_101 i) (hfix140_101 i) _)
      ⟨140, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 5 hp) Q2.T140_101_2 Q2.hfix140_101_2 Q2.hinj140_101_2
      Q2.hcardT140_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_101_2 i) (Q2.hfix140_101_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨101, by decide⟩ 5 (transLenTr ⟨101, by decide⟩ 5 hp) : ↥(reps ⟨101, by decide⟩)) : Coordinate 1)
        T140_101 = colFn colCertDiv_140_101_5.D1 (m := 5) from colCertDiv_140_101_5.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨101, by decide⟩ 5 hp : ↥(Q2.reps ⟨101, by decide⟩)) : Coordinate 2)
        Q2.T140_101_2 = colFn colCertDiv_140_101_5.D2 (m := 5) from colCertDiv_140_101_5.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_101_5_match


theorem leaf_140_101_10 (hp : 10 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 10 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 10 (transLenTr ⟨101, by decide⟩ 10 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 10 (transLenTr ⟨101, by decide⟩ 10 hp)) T140_101
      hfix140_101 hinj140_101 hcardT140_101
      (fun i => conj_mem_of_fixedPoints _ _ (T140_101 i) (hfix140_101 i) _)
      ⟨140, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 10 hp) Q2.T140_101_2 Q2.hfix140_101_2 Q2.hinj140_101_2
      Q2.hcardT140_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_101_2 i) (Q2.hfix140_101_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨101, by decide⟩ 10 (transLenTr ⟨101, by decide⟩ 10 hp) : ↥(reps ⟨101, by decide⟩)) : Coordinate 1)
        T140_101 = colFn colCertDiv_140_101_10.D1 (m := 5) from colCertDiv_140_101_10.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨101, by decide⟩ 10 hp : ↥(Q2.reps ⟨101, by decide⟩)) : Coordinate 2)
        Q2.T140_101_2 = colFn colCertDiv_140_101_10.D2 (m := 5) from colCertDiv_140_101_10.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_101_10_match


theorem leaf_140_101_15 (hp : 15 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 15 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 15 (transLenTr ⟨101, by decide⟩ 15 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 15 (transLenTr ⟨101, by decide⟩ 15 hp)) T140_101
      hfix140_101 hinj140_101 hcardT140_101
      (fun i => conj_mem_of_fixedPoints _ _ (T140_101 i) (hfix140_101 i) _)
      ⟨140, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 15 hp) Q2.T140_101_2 Q2.hfix140_101_2 Q2.hinj140_101_2
      Q2.hcardT140_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_101_2 i) (Q2.hfix140_101_2 i) _)
      colCert_140_101_15.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_101_20 (hp : 20 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 20 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 20 (transLenTr ⟨101, by decide⟩ 20 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 20 (transLenTr ⟨101, by decide⟩ 20 hp)) T140_101
      hfix140_101 hinj140_101 hcardT140_101
      (fun i => conj_mem_of_fixedPoints _ _ (T140_101 i) (hfix140_101 i) _)
      ⟨140, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 20 hp) Q2.T140_101_2 Q2.hfix140_101_2 Q2.hinj140_101_2
      Q2.hcardT140_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_101_2 i) (Q2.hfix140_101_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨101, by decide⟩ 20 (transLenTr ⟨101, by decide⟩ 20 hp) : ↥(reps ⟨101, by decide⟩)) : Coordinate 1)
        T140_101 = colFn colCertDiv_140_101_20.D1 (m := 5) from colCertDiv_140_101_20.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨101, by decide⟩ 20 hp : ↥(Q2.reps ⟨101, by decide⟩)) : Coordinate 2)
        Q2.T140_101_2 = colFn colCertDiv_140_101_20.D2 (m := 5) from colCertDiv_140_101_20.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_101_20_match


theorem leaf_140_108_0 (hp : 0 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 0 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 0 (transLenTr ⟨108, by decide⟩ 0 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 0 (transLenTr ⟨108, by decide⟩ 0 hp)) T140_108
      hfix140_108 hinj140_108 hcardT140_108
      (fun i => conj_mem_of_fixedPoints _ _ (T140_108 i) (hfix140_108 i) _)
      ⟨140, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 0 hp) Q2.T140_108_2 Q2.hfix140_108_2 Q2.hinj140_108_2
      Q2.hcardT140_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_108_2 i) (Q2.hfix140_108_2 i) _)
      colCert_140_108_0.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_108_1 (hp : 1 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 1 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 1 (transLenTr ⟨108, by decide⟩ 1 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 1 (transLenTr ⟨108, by decide⟩ 1 hp)) T140_108
      hfix140_108 hinj140_108 hcardT140_108
      (fun i => conj_mem_of_fixedPoints _ _ (T140_108 i) (hfix140_108 i) _)
      ⟨140, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 1 hp) Q2.T140_108_2 Q2.hfix140_108_2 Q2.hinj140_108_2
      Q2.hcardT140_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_108_2 i) (Q2.hfix140_108_2 i) _)
      colCert_140_108_1.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_108_2 (hp : 2 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 2 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 2 (transLenTr ⟨108, by decide⟩ 2 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 2 (transLenTr ⟨108, by decide⟩ 2 hp)) T140_108
      hfix140_108 hinj140_108 hcardT140_108
      (fun i => conj_mem_of_fixedPoints _ _ (T140_108 i) (hfix140_108 i) _)
      ⟨140, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 2 hp) Q2.T140_108_2 Q2.hfix140_108_2 Q2.hinj140_108_2
      Q2.hcardT140_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_108_2 i) (Q2.hfix140_108_2 i) _)
      colCert_140_108_2.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_108_3 (hp : 3 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 3 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 3 (transLenTr ⟨108, by decide⟩ 3 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 3 (transLenTr ⟨108, by decide⟩ 3 hp)) T140_108
      hfix140_108 hinj140_108 hcardT140_108
      (fun i => conj_mem_of_fixedPoints _ _ (T140_108 i) (hfix140_108 i) _)
      ⟨140, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 3 hp) Q2.T140_108_2 Q2.hfix140_108_2 Q2.hinj140_108_2
      Q2.hcardT140_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_108_2 i) (Q2.hfix140_108_2 i) _)
      colCert_140_108_3.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_108_4 (hp : 4 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 4 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 4 (transLenTr ⟨108, by decide⟩ 4 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 4 (transLenTr ⟨108, by decide⟩ 4 hp)) T140_108
      hfix140_108 hinj140_108 hcardT140_108
      (fun i => conj_mem_of_fixedPoints _ _ (T140_108 i) (hfix140_108 i) _)
      ⟨140, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 4 hp) Q2.T140_108_2 Q2.hfix140_108_2 Q2.hinj140_108_2
      Q2.hcardT140_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_108_2 i) (Q2.hfix140_108_2 i) _)
      colCert_140_108_4.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_108_5 (hp : 5 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 5 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 5 (transLenTr ⟨108, by decide⟩ 5 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 5 (transLenTr ⟨108, by decide⟩ 5 hp)) T140_108
      hfix140_108 hinj140_108 hcardT140_108
      (fun i => conj_mem_of_fixedPoints _ _ (T140_108 i) (hfix140_108 i) _)
      ⟨140, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 5 hp) Q2.T140_108_2 Q2.hfix140_108_2 Q2.hinj140_108_2
      Q2.hcardT140_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_108_2 i) (Q2.hfix140_108_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨108, by decide⟩ 5 (transLenTr ⟨108, by decide⟩ 5 hp) : ↥(reps ⟨108, by decide⟩)) : Coordinate 1)
        T140_108 = colFn colCertDiv_140_108_5.D1 (m := 5) from colCertDiv_140_108_5.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨108, by decide⟩ 5 hp : ↥(Q2.reps ⟨108, by decide⟩)) : Coordinate 2)
        Q2.T140_108_2 = colFn colCertDiv_140_108_5.D2 (m := 5) from colCertDiv_140_108_5.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_108_5_match


theorem leaf_140_108_10 (hp : 10 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 10 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 10 (transLenTr ⟨108, by decide⟩ 10 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 10 (transLenTr ⟨108, by decide⟩ 10 hp)) T140_108
      hfix140_108 hinj140_108 hcardT140_108
      (fun i => conj_mem_of_fixedPoints _ _ (T140_108 i) (hfix140_108 i) _)
      ⟨140, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 10 hp) Q2.T140_108_2 Q2.hfix140_108_2 Q2.hinj140_108_2
      Q2.hcardT140_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_108_2 i) (Q2.hfix140_108_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨108, by decide⟩ 10 (transLenTr ⟨108, by decide⟩ 10 hp) : ↥(reps ⟨108, by decide⟩)) : Coordinate 1)
        T140_108 = colFn colCertDiv_140_108_10.D1 (m := 5) from colCertDiv_140_108_10.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨108, by decide⟩ 10 hp : ↥(Q2.reps ⟨108, by decide⟩)) : Coordinate 2)
        Q2.T140_108_2 = colFn colCertDiv_140_108_10.D2 (m := 5) from colCertDiv_140_108_10.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_108_10_match


theorem leaf_140_108_15 (hp : 15 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 15 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 15 (transLenTr ⟨108, by decide⟩ 15 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 15 (transLenTr ⟨108, by decide⟩ 15 hp)) T140_108
      hfix140_108 hinj140_108 hcardT140_108
      (fun i => conj_mem_of_fixedPoints _ _ (T140_108 i) (hfix140_108 i) _)
      ⟨140, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 15 hp) Q2.T140_108_2 Q2.hfix140_108_2 Q2.hinj140_108_2
      Q2.hcardT140_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_108_2 i) (Q2.hfix140_108_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨108, by decide⟩ 15 (transLenTr ⟨108, by decide⟩ 15 hp) : ↥(reps ⟨108, by decide⟩)) : Coordinate 1)
        T140_108 = colFn colCertDiv_140_108_15.D1 (m := 5) from colCertDiv_140_108_15.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨108, by decide⟩ 15 hp : ↥(Q2.reps ⟨108, by decide⟩)) : Coordinate 2)
        Q2.T140_108_2 = colFn colCertDiv_140_108_15.D2 (m := 5) from colCertDiv_140_108_15.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_108_15_match


theorem leaf_140_108_20 (hp : 20 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 20 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 20 (transLenTr ⟨108, by decide⟩ 20 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 20 (transLenTr ⟨108, by decide⟩ 20 hp)) T140_108
      hfix140_108 hinj140_108 hcardT140_108
      (fun i => conj_mem_of_fixedPoints _ _ (T140_108 i) (hfix140_108 i) _)
      ⟨140, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 20 hp) Q2.T140_108_2 Q2.hfix140_108_2 Q2.hinj140_108_2
      Q2.hcardT140_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_108_2 i) (Q2.hfix140_108_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨108, by decide⟩ 20 (transLenTr ⟨108, by decide⟩ 20 hp) : ↥(reps ⟨108, by decide⟩)) : Coordinate 1)
        T140_108 = colFn colCertDiv_140_108_20.D1 (m := 5) from colCertDiv_140_108_20.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨108, by decide⟩ 20 hp : ↥(Q2.reps ⟨108, by decide⟩)) : Coordinate 2)
        Q2.T140_108_2 = colFn colCertDiv_140_108_20.D2 (m := 5) from colCertDiv_140_108_20.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_108_20_match


theorem leaf_140_114_0 (hp : 0 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 0 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 0 (transLenTr ⟨114, by decide⟩ 0 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 0 (transLenTr ⟨114, by decide⟩ 0 hp)) T140_114
      hfix140_114 hinj140_114 hcardT140_114
      (fun i => conj_mem_of_fixedPoints _ _ (T140_114 i) (hfix140_114 i) _)
      ⟨140, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 0 hp) Q2.T140_114_2 Q2.hfix140_114_2 Q2.hinj140_114_2
      Q2.hcardT140_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_114_2 i) (Q2.hfix140_114_2 i) _)
      colCert_140_114_0.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_114_1 (hp : 1 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 1 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 1 (transLenTr ⟨114, by decide⟩ 1 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 1 (transLenTr ⟨114, by decide⟩ 1 hp)) T140_114
      hfix140_114 hinj140_114 hcardT140_114
      (fun i => conj_mem_of_fixedPoints _ _ (T140_114 i) (hfix140_114 i) _)
      ⟨140, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 1 hp) Q2.T140_114_2 Q2.hfix140_114_2 Q2.hinj140_114_2
      Q2.hcardT140_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_114_2 i) (Q2.hfix140_114_2 i) _)
      colCert_140_114_1.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_114_2 (hp : 2 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 2 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 2 (transLenTr ⟨114, by decide⟩ 2 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 2 (transLenTr ⟨114, by decide⟩ 2 hp)) T140_114
      hfix140_114 hinj140_114 hcardT140_114
      (fun i => conj_mem_of_fixedPoints _ _ (T140_114 i) (hfix140_114 i) _)
      ⟨140, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 2 hp) Q2.T140_114_2 Q2.hfix140_114_2 Q2.hinj140_114_2
      Q2.hcardT140_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_114_2 i) (Q2.hfix140_114_2 i) _)
      colCert_140_114_2.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_114_3 (hp : 3 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 3 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 3 (transLenTr ⟨114, by decide⟩ 3 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 3 (transLenTr ⟨114, by decide⟩ 3 hp)) T140_114
      hfix140_114 hinj140_114 hcardT140_114
      (fun i => conj_mem_of_fixedPoints _ _ (T140_114 i) (hfix140_114 i) _)
      ⟨140, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 3 hp) Q2.T140_114_2 Q2.hfix140_114_2 Q2.hinj140_114_2
      Q2.hcardT140_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_114_2 i) (Q2.hfix140_114_2 i) _)
      colCert_140_114_3.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_114_4 (hp : 4 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 4 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 4 (transLenTr ⟨114, by decide⟩ 4 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 4 (transLenTr ⟨114, by decide⟩ 4 hp)) T140_114
      hfix140_114 hinj140_114 hcardT140_114
      (fun i => conj_mem_of_fixedPoints _ _ (T140_114 i) (hfix140_114 i) _)
      ⟨140, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 4 hp) Q2.T140_114_2 Q2.hfix140_114_2 Q2.hinj140_114_2
      Q2.hcardT140_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_114_2 i) (Q2.hfix140_114_2 i) _)
      colCert_140_114_4.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_114_5 (hp : 5 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 5 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 5 (transLenTr ⟨114, by decide⟩ 5 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 5 (transLenTr ⟨114, by decide⟩ 5 hp)) T140_114
      hfix140_114 hinj140_114 hcardT140_114
      (fun i => conj_mem_of_fixedPoints _ _ (T140_114 i) (hfix140_114 i) _)
      ⟨140, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 5 hp) Q2.T140_114_2 Q2.hfix140_114_2 Q2.hinj140_114_2
      Q2.hcardT140_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_114_2 i) (Q2.hfix140_114_2 i) _)
      colCert_140_114_5.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_114_10 (hp : 10 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 10 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 10 (transLenTr ⟨114, by decide⟩ 10 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 10 (transLenTr ⟨114, by decide⟩ 10 hp)) T140_114
      hfix140_114 hinj140_114 hcardT140_114
      (fun i => conj_mem_of_fixedPoints _ _ (T140_114 i) (hfix140_114 i) _)
      ⟨140, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 10 hp) Q2.T140_114_2 Q2.hfix140_114_2 Q2.hinj140_114_2
      Q2.hcardT140_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_114_2 i) (Q2.hfix140_114_2 i) _)
      colCert_140_114_10.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_114_15 (hp : 15 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 15 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 15 (transLenTr ⟨114, by decide⟩ 15 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 15 (transLenTr ⟨114, by decide⟩ 15 hp)) T140_114
      hfix140_114 hinj140_114 hcardT140_114
      (fun i => conj_mem_of_fixedPoints _ _ (T140_114 i) (hfix140_114 i) _)
      ⟨140, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 15 hp) Q2.T140_114_2 Q2.hfix140_114_2 Q2.hinj140_114_2
      Q2.hcardT140_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_114_2 i) (Q2.hfix140_114_2 i) _)
      colCert_140_114_15.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_114_20 (hp : 20 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 20 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 20 (transLenTr ⟨114, by decide⟩ 20 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 20 (transLenTr ⟨114, by decide⟩ 20 hp)) T140_114
      hfix140_114 hinj140_114 hcardT140_114
      (fun i => conj_mem_of_fixedPoints _ _ (T140_114 i) (hfix140_114 i) _)
      ⟨140, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 20 hp) Q2.T140_114_2 Q2.hfix140_114_2 Q2.hinj140_114_2
      Q2.hcardT140_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_114_2 i) (Q2.hfix140_114_2 i) _)
      colCert_140_114_20.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_140_0 (hp : 0 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 0 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 0 (transLenTr ⟨140, by decide⟩ 0 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 0 (transLenTr ⟨140, by decide⟩ 0 hp)) T140_140
      hfix140_140 hinj140_140 hcardT140_140
      (fun i => conj_mem_of_fixedPoints _ _ (T140_140 i) (hfix140_140 i) _)
      ⟨140, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 0 hp) Q2.T140_140_2 Q2.hfix140_140_2 Q2.hinj140_140_2
      Q2.hcardT140_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_140_2 i) (Q2.hfix140_140_2 i) _)
      colCert_140_140_0.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_140_1 (hp : 1 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 1 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 1 (transLenTr ⟨140, by decide⟩ 1 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 1 (transLenTr ⟨140, by decide⟩ 1 hp)) T140_140
      hfix140_140 hinj140_140 hcardT140_140
      (fun i => conj_mem_of_fixedPoints _ _ (T140_140 i) (hfix140_140 i) _)
      ⟨140, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 1 hp) Q2.T140_140_2 Q2.hfix140_140_2 Q2.hinj140_140_2
      Q2.hcardT140_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_140_2 i) (Q2.hfix140_140_2 i) _)
      colCert_140_140_1.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_140_2 (hp : 2 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 2 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 2 (transLenTr ⟨140, by decide⟩ 2 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 2 (transLenTr ⟨140, by decide⟩ 2 hp)) T140_140
      hfix140_140 hinj140_140 hcardT140_140
      (fun i => conj_mem_of_fixedPoints _ _ (T140_140 i) (hfix140_140 i) _)
      ⟨140, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 2 hp) Q2.T140_140_2 Q2.hfix140_140_2 Q2.hinj140_140_2
      Q2.hcardT140_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_140_2 i) (Q2.hfix140_140_2 i) _)
      colCert_140_140_2.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_140_3 (hp : 3 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 3 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 3 (transLenTr ⟨140, by decide⟩ 3 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 3 (transLenTr ⟨140, by decide⟩ 3 hp)) T140_140
      hfix140_140 hinj140_140 hcardT140_140
      (fun i => conj_mem_of_fixedPoints _ _ (T140_140 i) (hfix140_140 i) _)
      ⟨140, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 3 hp) Q2.T140_140_2 Q2.hfix140_140_2 Q2.hinj140_140_2
      Q2.hcardT140_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_140_2 i) (Q2.hfix140_140_2 i) _)
      colCert_140_140_3.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_140_4 (hp : 4 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 4 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 4 (transLenTr ⟨140, by decide⟩ 4 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 4 (transLenTr ⟨140, by decide⟩ 4 hp)) T140_140
      hfix140_140 hinj140_140 hcardT140_140
      (fun i => conj_mem_of_fixedPoints _ _ (T140_140 i) (hfix140_140 i) _)
      ⟨140, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 4 hp) Q2.T140_140_2 Q2.hfix140_140_2 Q2.hinj140_140_2
      Q2.hcardT140_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_140_2 i) (Q2.hfix140_140_2 i) _)
      colCert_140_140_4.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_140_5 (hp : 5 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 5 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 5 (transLenTr ⟨140, by decide⟩ 5 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 5 (transLenTr ⟨140, by decide⟩ 5 hp)) T140_140
      hfix140_140 hinj140_140 hcardT140_140
      (fun i => conj_mem_of_fixedPoints _ _ (T140_140 i) (hfix140_140 i) _)
      ⟨140, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 5 hp) Q2.T140_140_2 Q2.hfix140_140_2 Q2.hinj140_140_2
      Q2.hcardT140_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_140_2 i) (Q2.hfix140_140_2 i) _)
      colCert_140_140_5.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_140_6 (hp : 6 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 6 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 6 (transLenTr ⟨140, by decide⟩ 6 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 6 (transLenTr ⟨140, by decide⟩ 6 hp)) T140_140
      hfix140_140 hinj140_140 hcardT140_140
      (fun i => conj_mem_of_fixedPoints _ _ (T140_140 i) (hfix140_140 i) _)
      ⟨140, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 6 hp) Q2.T140_140_2 Q2.hfix140_140_2 Q2.hinj140_140_2
      Q2.hcardT140_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_140_2 i) (Q2.hfix140_140_2 i) _)
      colCert_140_140_6.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_140_7 (hp : 7 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 7 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 7 (transLenTr ⟨140, by decide⟩ 7 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 7 (transLenTr ⟨140, by decide⟩ 7 hp)) T140_140
      hfix140_140 hinj140_140 hcardT140_140
      (fun i => conj_mem_of_fixedPoints _ _ (T140_140 i) (hfix140_140 i) _)
      ⟨140, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 7 hp) Q2.T140_140_2 Q2.hfix140_140_2 Q2.hinj140_140_2
      Q2.hcardT140_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_140_2 i) (Q2.hfix140_140_2 i) _)
      colCert_140_140_7.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_140_8 (hp : 8 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 8 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 8 (transLenTr ⟨140, by decide⟩ 8 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 8 (transLenTr ⟨140, by decide⟩ 8 hp)) T140_140
      hfix140_140 hinj140_140 hcardT140_140
      (fun i => conj_mem_of_fixedPoints _ _ (T140_140 i) (hfix140_140 i) _)
      ⟨140, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 8 hp) Q2.T140_140_2 Q2.hfix140_140_2 Q2.hinj140_140_2
      Q2.hcardT140_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_140_2 i) (Q2.hfix140_140_2 i) _)
      colCert_140_140_8.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_140_9 (hp : 9 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 9 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 9 (transLenTr ⟨140, by decide⟩ 9 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 9 (transLenTr ⟨140, by decide⟩ 9 hp)) T140_140
      hfix140_140 hinj140_140 hcardT140_140
      (fun i => conj_mem_of_fixedPoints _ _ (T140_140 i) (hfix140_140 i) _)
      ⟨140, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 9 hp) Q2.T140_140_2 Q2.hfix140_140_2 Q2.hinj140_140_2
      Q2.hcardT140_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_140_2 i) (Q2.hfix140_140_2 i) _)
      colCert_140_140_9.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_140_10 (hp : 10 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 10 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 10 (transLenTr ⟨140, by decide⟩ 10 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 10 (transLenTr ⟨140, by decide⟩ 10 hp)) T140_140
      hfix140_140 hinj140_140 hcardT140_140
      (fun i => conj_mem_of_fixedPoints _ _ (T140_140 i) (hfix140_140 i) _)
      ⟨140, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 10 hp) Q2.T140_140_2 Q2.hfix140_140_2 Q2.hinj140_140_2
      Q2.hcardT140_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_140_2 i) (Q2.hfix140_140_2 i) _)
      colCert_140_140_10.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_140_11 (hp : 11 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 11 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 11 (transLenTr ⟨140, by decide⟩ 11 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 11 (transLenTr ⟨140, by decide⟩ 11 hp)) T140_140
      hfix140_140 hinj140_140 hcardT140_140
      (fun i => conj_mem_of_fixedPoints _ _ (T140_140 i) (hfix140_140 i) _)
      ⟨140, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 11 hp) Q2.T140_140_2 Q2.hfix140_140_2 Q2.hinj140_140_2
      Q2.hcardT140_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_140_2 i) (Q2.hfix140_140_2 i) _)
      colCert_140_140_11.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_140_12 (hp : 12 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 12 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 12 (transLenTr ⟨140, by decide⟩ 12 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 12 (transLenTr ⟨140, by decide⟩ 12 hp)) T140_140
      hfix140_140 hinj140_140 hcardT140_140
      (fun i => conj_mem_of_fixedPoints _ _ (T140_140 i) (hfix140_140 i) _)
      ⟨140, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 12 hp) Q2.T140_140_2 Q2.hfix140_140_2 Q2.hinj140_140_2
      Q2.hcardT140_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_140_2 i) (Q2.hfix140_140_2 i) _)
      colCert_140_140_12.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_140_13 (hp : 13 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 13 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 13 (transLenTr ⟨140, by decide⟩ 13 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 13 (transLenTr ⟨140, by decide⟩ 13 hp)) T140_140
      hfix140_140 hinj140_140 hcardT140_140
      (fun i => conj_mem_of_fixedPoints _ _ (T140_140 i) (hfix140_140 i) _)
      ⟨140, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 13 hp) Q2.T140_140_2 Q2.hfix140_140_2 Q2.hinj140_140_2
      Q2.hcardT140_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_140_2 i) (Q2.hfix140_140_2 i) _)
      colCert_140_140_13.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_140_14 (hp : 14 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 14 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 14 (transLenTr ⟨140, by decide⟩ 14 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 14 (transLenTr ⟨140, by decide⟩ 14 hp)) T140_140
      hfix140_140 hinj140_140 hcardT140_140
      (fun i => conj_mem_of_fixedPoints _ _ (T140_140 i) (hfix140_140 i) _)
      ⟨140, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 14 hp) Q2.T140_140_2 Q2.hfix140_140_2 Q2.hinj140_140_2
      Q2.hcardT140_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_140_2 i) (Q2.hfix140_140_2 i) _)
      colCert_140_140_14.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_140_15 (hp : 15 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 15 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 15 (transLenTr ⟨140, by decide⟩ 15 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 15 (transLenTr ⟨140, by decide⟩ 15 hp)) T140_140
      hfix140_140 hinj140_140 hcardT140_140
      (fun i => conj_mem_of_fixedPoints _ _ (T140_140 i) (hfix140_140 i) _)
      ⟨140, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 15 hp) Q2.T140_140_2 Q2.hfix140_140_2 Q2.hinj140_140_2
      Q2.hcardT140_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_140_2 i) (Q2.hfix140_140_2 i) _)
      colCert_140_140_15.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_140_16 (hp : 16 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 16 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 16 (transLenTr ⟨140, by decide⟩ 16 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 16 (transLenTr ⟨140, by decide⟩ 16 hp)) T140_140
      hfix140_140 hinj140_140 hcardT140_140
      (fun i => conj_mem_of_fixedPoints _ _ (T140_140 i) (hfix140_140 i) _)
      ⟨140, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 16 hp) Q2.T140_140_2 Q2.hfix140_140_2 Q2.hinj140_140_2
      Q2.hcardT140_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_140_2 i) (Q2.hfix140_140_2 i) _)
      colCert_140_140_16.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_140_17 (hp : 17 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 17 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 17 (transLenTr ⟨140, by decide⟩ 17 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 17 (transLenTr ⟨140, by decide⟩ 17 hp)) T140_140
      hfix140_140 hinj140_140 hcardT140_140
      (fun i => conj_mem_of_fixedPoints _ _ (T140_140 i) (hfix140_140 i) _)
      ⟨140, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 17 hp) Q2.T140_140_2 Q2.hfix140_140_2 Q2.hinj140_140_2
      Q2.hcardT140_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_140_2 i) (Q2.hfix140_140_2 i) _)
      colCert_140_140_17.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_140_18 (hp : 18 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 18 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 18 (transLenTr ⟨140, by decide⟩ 18 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 18 (transLenTr ⟨140, by decide⟩ 18 hp)) T140_140
      hfix140_140 hinj140_140 hcardT140_140
      (fun i => conj_mem_of_fixedPoints _ _ (T140_140 i) (hfix140_140 i) _)
      ⟨140, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 18 hp) Q2.T140_140_2 Q2.hfix140_140_2 Q2.hinj140_140_2
      Q2.hcardT140_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_140_2 i) (Q2.hfix140_140_2 i) _)
      colCert_140_140_18.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_140_19 (hp : 19 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 19 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 19 (transLenTr ⟨140, by decide⟩ 19 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 19 (transLenTr ⟨140, by decide⟩ 19 hp)) T140_140
      hfix140_140 hinj140_140 hcardT140_140
      (fun i => conj_mem_of_fixedPoints _ _ (T140_140 i) (hfix140_140 i) _)
      ⟨140, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 19 hp) Q2.T140_140_2 Q2.hfix140_140_2 Q2.hinj140_140_2
      Q2.hcardT140_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_140_2 i) (Q2.hfix140_140_2 i) _)
      colCert_140_140_19.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_140_20 (hp : 20 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 20 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 20 (transLenTr ⟨140, by decide⟩ 20 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 20 (transLenTr ⟨140, by decide⟩ 20 hp)) T140_140
      hfix140_140 hinj140_140 hcardT140_140
      (fun i => conj_mem_of_fixedPoints _ _ (T140_140 i) (hfix140_140 i) _)
      ⟨140, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 20 hp) Q2.T140_140_2 Q2.hfix140_140_2 Q2.hinj140_140_2
      Q2.hcardT140_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_140_2 i) (Q2.hfix140_140_2 i) _)
      colCert_140_140_20.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_140_21 (hp : 21 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 21 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 21 (transLenTr ⟨140, by decide⟩ 21 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 21 (transLenTr ⟨140, by decide⟩ 21 hp)) T140_140
      hfix140_140 hinj140_140 hcardT140_140
      (fun i => conj_mem_of_fixedPoints _ _ (T140_140 i) (hfix140_140 i) _)
      ⟨140, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 21 hp) Q2.T140_140_2 Q2.hfix140_140_2 Q2.hinj140_140_2
      Q2.hcardT140_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_140_2 i) (Q2.hfix140_140_2 i) _)
      colCert_140_140_21.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_140_22 (hp : 22 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 22 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 22 (transLenTr ⟨140, by decide⟩ 22 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 22 (transLenTr ⟨140, by decide⟩ 22 hp)) T140_140
      hfix140_140 hinj140_140 hcardT140_140
      (fun i => conj_mem_of_fixedPoints _ _ (T140_140 i) (hfix140_140 i) _)
      ⟨140, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 22 hp) Q2.T140_140_2 Q2.hfix140_140_2 Q2.hinj140_140_2
      Q2.hcardT140_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_140_2 i) (Q2.hfix140_140_2 i) _)
      colCert_140_140_22.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_140_23 (hp : 23 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 23 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 23 (transLenTr ⟨140, by decide⟩ 23 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 23 (transLenTr ⟨140, by decide⟩ 23 hp)) T140_140
      hfix140_140 hinj140_140 hcardT140_140
      (fun i => conj_mem_of_fixedPoints _ _ (T140_140 i) (hfix140_140 i) _)
      ⟨140, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 23 hp) Q2.T140_140_2 Q2.hfix140_140_2 Q2.hinj140_140_2
      Q2.hcardT140_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_140_2 i) (Q2.hfix140_140_2 i) _)
      colCert_140_140_23.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_140_24 (hp : 24 < (Q2.transData.getD 140 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ 24 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ 24 (transLenTr ⟨140, by decide⟩ 24 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨140, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨140, by decide⟩ 24 (transLenTr ⟨140, by decide⟩ 24 hp)) T140_140
      hfix140_140 hinj140_140 hcardT140_140
      (fun i => conj_mem_of_fixedPoints _ _ (T140_140 i) (hfix140_140 i) _)
      ⟨140, by decide⟩ ⟨140, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨140, by decide⟩ 24 hp) Q2.T140_140_2 Q2.hfix140_140_2 Q2.hinj140_140_2
      Q2.hcardT140_140_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_140_2 i) (Q2.hfix140_140_2 i) _)
      colCert_140_140_24.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_141_1_0 (hp : 0 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp)) T141_1
      hfix141_1 hinj141_1 hcardT141_1
      (fun i => conj_mem_of_fixedPoints _ _ (T141_1 i) (hfix141_1 i) _)
      ⟨141, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 0 hp) Q2.T141_1_2 Q2.hfix141_1_2 Q2.hinj141_1_2
      Q2.hcardT141_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_1_2 i) (Q2.hfix141_1_2 i) _)
      colCert_141_1_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_1_1 (hp : 1 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp)) T141_1
      hfix141_1 hinj141_1 hcardT141_1
      (fun i => conj_mem_of_fixedPoints _ _ (T141_1 i) (hfix141_1 i) _)
      ⟨141, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 1 hp) Q2.T141_1_2 Q2.hfix141_1_2 Q2.hinj141_1_2
      Q2.hcardT141_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_1_2 i) (Q2.hfix141_1_2 i) _)
      colCert_141_1_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_1_2 (hp : 2 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp)) T141_1
      hfix141_1 hinj141_1 hcardT141_1
      (fun i => conj_mem_of_fixedPoints _ _ (T141_1 i) (hfix141_1 i) _)
      ⟨141, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 2 hp) Q2.T141_1_2 Q2.hfix141_1_2 Q2.hinj141_1_2
      Q2.hcardT141_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_1_2 i) (Q2.hfix141_1_2 i) _)
      colCert_141_1_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_1_3 (hp : 3 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp)) T141_1
      hfix141_1 hinj141_1 hcardT141_1
      (fun i => conj_mem_of_fixedPoints _ _ (T141_1 i) (hfix141_1 i) _)
      ⟨141, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 3 hp) Q2.T141_1_2 Q2.hfix141_1_2 Q2.hinj141_1_2
      Q2.hcardT141_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_1_2 i) (Q2.hfix141_1_2 i) _)
      colCert_141_1_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_1_4 (hp : 4 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp)) T141_1
      hfix141_1 hinj141_1 hcardT141_1
      (fun i => conj_mem_of_fixedPoints _ _ (T141_1 i) (hfix141_1 i) _)
      ⟨141, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 4 hp) Q2.T141_1_2 Q2.hfix141_1_2 Q2.hinj141_1_2
      Q2.hcardT141_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_1_2 i) (Q2.hfix141_1_2 i) _)
      colCert_141_1_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_2_0 (hp : 0 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp)) T141_2
      hfix141_2 hinj141_2 hcardT141_2
      (fun i => conj_mem_of_fixedPoints _ _ (T141_2 i) (hfix141_2 i) _)
      ⟨141, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 0 hp) Q2.T141_2_2 Q2.hfix141_2_2 Q2.hinj141_2_2
      Q2.hcardT141_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_2_2 i) (Q2.hfix141_2_2 i) _)
      colCert_141_2_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_2_1 (hp : 1 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp)) T141_2
      hfix141_2 hinj141_2 hcardT141_2
      (fun i => conj_mem_of_fixedPoints _ _ (T141_2 i) (hfix141_2 i) _)
      ⟨141, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 1 hp) Q2.T141_2_2 Q2.hfix141_2_2 Q2.hinj141_2_2
      Q2.hcardT141_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_2_2 i) (Q2.hfix141_2_2 i) _)
      colCert_141_2_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_2_2 (hp : 2 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp)) T141_2
      hfix141_2 hinj141_2 hcardT141_2
      (fun i => conj_mem_of_fixedPoints _ _ (T141_2 i) (hfix141_2 i) _)
      ⟨141, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 2 hp) Q2.T141_2_2 Q2.hfix141_2_2 Q2.hinj141_2_2
      Q2.hcardT141_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_2_2 i) (Q2.hfix141_2_2 i) _)
      colCert_141_2_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_2_3 (hp : 3 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp)) T141_2
      hfix141_2 hinj141_2 hcardT141_2
      (fun i => conj_mem_of_fixedPoints _ _ (T141_2 i) (hfix141_2 i) _)
      ⟨141, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 3 hp) Q2.T141_2_2 Q2.hfix141_2_2 Q2.hinj141_2_2
      Q2.hcardT141_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_2_2 i) (Q2.hfix141_2_2 i) _)
      colCert_141_2_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_2_4 (hp : 4 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp)) T141_2
      hfix141_2 hinj141_2 hcardT141_2
      (fun i => conj_mem_of_fixedPoints _ _ (T141_2 i) (hfix141_2 i) _)
      ⟨141, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 4 hp) Q2.T141_2_2 Q2.hfix141_2_2 Q2.hinj141_2_2
      Q2.hcardT141_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_2_2 i) (Q2.hfix141_2_2 i) _)
      colCert_141_2_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_3_0 (hp : 0 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp)) T141_3
      hfix141_3 hinj141_3 hcardT141_3
      (fun i => conj_mem_of_fixedPoints _ _ (T141_3 i) (hfix141_3 i) _)
      ⟨141, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 0 hp) Q2.T141_3_2 Q2.hfix141_3_2 Q2.hinj141_3_2
      Q2.hcardT141_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_3_2 i) (Q2.hfix141_3_2 i) _)
      colCert_141_3_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_3_1 (hp : 1 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp)) T141_3
      hfix141_3 hinj141_3 hcardT141_3
      (fun i => conj_mem_of_fixedPoints _ _ (T141_3 i) (hfix141_3 i) _)
      ⟨141, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 1 hp) Q2.T141_3_2 Q2.hfix141_3_2 Q2.hinj141_3_2
      Q2.hcardT141_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_3_2 i) (Q2.hfix141_3_2 i) _)
      colCert_141_3_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_3_2 (hp : 2 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp)) T141_3
      hfix141_3 hinj141_3 hcardT141_3
      (fun i => conj_mem_of_fixedPoints _ _ (T141_3 i) (hfix141_3 i) _)
      ⟨141, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 2 hp) Q2.T141_3_2 Q2.hfix141_3_2 Q2.hinj141_3_2
      Q2.hcardT141_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_3_2 i) (Q2.hfix141_3_2 i) _)
      colCert_141_3_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_3_3 (hp : 3 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp)) T141_3
      hfix141_3 hinj141_3 hcardT141_3
      (fun i => conj_mem_of_fixedPoints _ _ (T141_3 i) (hfix141_3 i) _)
      ⟨141, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 3 hp) Q2.T141_3_2 Q2.hfix141_3_2 Q2.hinj141_3_2
      Q2.hcardT141_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_3_2 i) (Q2.hfix141_3_2 i) _)
      colCert_141_3_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_3_4 (hp : 4 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp)) T141_3
      hfix141_3 hinj141_3 hcardT141_3
      (fun i => conj_mem_of_fixedPoints _ _ (T141_3 i) (hfix141_3 i) _)
      ⟨141, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 4 hp) Q2.T141_3_2 Q2.hfix141_3_2 Q2.hinj141_3_2
      Q2.hcardT141_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_3_2 i) (Q2.hfix141_3_2 i) _)
      colCert_141_3_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_4_0 (hp : 0 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp)) T141_4
      hfix141_4 hinj141_4 hcardT141_4
      (fun i => conj_mem_of_fixedPoints _ _ (T141_4 i) (hfix141_4 i) _)
      ⟨141, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 0 hp) Q2.T141_4_2 Q2.hfix141_4_2 Q2.hinj141_4_2
      Q2.hcardT141_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_4_2 i) (Q2.hfix141_4_2 i) _)
      colCert_141_4_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_4_1 (hp : 1 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp)) T141_4
      hfix141_4 hinj141_4 hcardT141_4
      (fun i => conj_mem_of_fixedPoints _ _ (T141_4 i) (hfix141_4 i) _)
      ⟨141, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 1 hp) Q2.T141_4_2 Q2.hfix141_4_2 Q2.hinj141_4_2
      Q2.hcardT141_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_4_2 i) (Q2.hfix141_4_2 i) _)
      colCert_141_4_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_4_2 (hp : 2 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp)) T141_4
      hfix141_4 hinj141_4 hcardT141_4
      (fun i => conj_mem_of_fixedPoints _ _ (T141_4 i) (hfix141_4 i) _)
      ⟨141, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 2 hp) Q2.T141_4_2 Q2.hfix141_4_2 Q2.hinj141_4_2
      Q2.hcardT141_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_4_2 i) (Q2.hfix141_4_2 i) _)
      colCert_141_4_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_4_3 (hp : 3 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp)) T141_4
      hfix141_4 hinj141_4 hcardT141_4
      (fun i => conj_mem_of_fixedPoints _ _ (T141_4 i) (hfix141_4 i) _)
      ⟨141, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 3 hp) Q2.T141_4_2 Q2.hfix141_4_2 Q2.hinj141_4_2
      Q2.hcardT141_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_4_2 i) (Q2.hfix141_4_2 i) _)
      colCert_141_4_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_4_4 (hp : 4 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp)) T141_4
      hfix141_4 hinj141_4 hcardT141_4
      (fun i => conj_mem_of_fixedPoints _ _ (T141_4 i) (hfix141_4 i) _)
      ⟨141, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 4 hp) Q2.T141_4_2 Q2.hfix141_4_2 Q2.hinj141_4_2
      Q2.hcardT141_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_4_2 i) (Q2.hfix141_4_2 i) _)
      colCert_141_4_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_5_0 (hp : 0 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp)) T141_5
      hfix141_5 hinj141_5 hcardT141_5
      (fun i => conj_mem_of_fixedPoints _ _ (T141_5 i) (hfix141_5 i) _)
      ⟨141, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 0 hp) Q2.T141_5_2 Q2.hfix141_5_2 Q2.hinj141_5_2
      Q2.hcardT141_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_5_2 i) (Q2.hfix141_5_2 i) _)
      colCert_141_5_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_5_1 (hp : 1 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp)) T141_5
      hfix141_5 hinj141_5 hcardT141_5
      (fun i => conj_mem_of_fixedPoints _ _ (T141_5 i) (hfix141_5 i) _)
      ⟨141, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 1 hp) Q2.T141_5_2 Q2.hfix141_5_2 Q2.hinj141_5_2
      Q2.hcardT141_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_5_2 i) (Q2.hfix141_5_2 i) _)
      colCert_141_5_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_5_2 (hp : 2 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp)) T141_5
      hfix141_5 hinj141_5 hcardT141_5
      (fun i => conj_mem_of_fixedPoints _ _ (T141_5 i) (hfix141_5 i) _)
      ⟨141, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 2 hp) Q2.T141_5_2 Q2.hfix141_5_2 Q2.hinj141_5_2
      Q2.hcardT141_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_5_2 i) (Q2.hfix141_5_2 i) _)
      colCert_141_5_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_5_3 (hp : 3 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp)) T141_5
      hfix141_5 hinj141_5 hcardT141_5
      (fun i => conj_mem_of_fixedPoints _ _ (T141_5 i) (hfix141_5 i) _)
      ⟨141, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 3 hp) Q2.T141_5_2 Q2.hfix141_5_2 Q2.hinj141_5_2
      Q2.hcardT141_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_5_2 i) (Q2.hfix141_5_2 i) _)
      colCert_141_5_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_5_4 (hp : 4 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp)) T141_5
      hfix141_5 hinj141_5 hcardT141_5
      (fun i => conj_mem_of_fixedPoints _ _ (T141_5 i) (hfix141_5 i) _)
      ⟨141, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 4 hp) Q2.T141_5_2 Q2.hfix141_5_2 Q2.hinj141_5_2
      Q2.hcardT141_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_5_2 i) (Q2.hfix141_5_2 i) _)
      colCert_141_5_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_6_0 (hp : 0 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp)) T141_6
      hfix141_6 hinj141_6 hcardT141_6
      (fun i => conj_mem_of_fixedPoints _ _ (T141_6 i) (hfix141_6 i) _)
      ⟨141, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 0 hp) Q2.T141_6_2 Q2.hfix141_6_2 Q2.hinj141_6_2
      Q2.hcardT141_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_6_2 i) (Q2.hfix141_6_2 i) _)
      colCert_141_6_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_6_1 (hp : 1 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp)) T141_6
      hfix141_6 hinj141_6 hcardT141_6
      (fun i => conj_mem_of_fixedPoints _ _ (T141_6 i) (hfix141_6 i) _)
      ⟨141, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 1 hp) Q2.T141_6_2 Q2.hfix141_6_2 Q2.hinj141_6_2
      Q2.hcardT141_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_6_2 i) (Q2.hfix141_6_2 i) _)
      colCert_141_6_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_6_2 (hp : 2 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp)) T141_6
      hfix141_6 hinj141_6 hcardT141_6
      (fun i => conj_mem_of_fixedPoints _ _ (T141_6 i) (hfix141_6 i) _)
      ⟨141, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 2 hp) Q2.T141_6_2 Q2.hfix141_6_2 Q2.hinj141_6_2
      Q2.hcardT141_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_6_2 i) (Q2.hfix141_6_2 i) _)
      colCert_141_6_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_6_3 (hp : 3 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp)) T141_6
      hfix141_6 hinj141_6 hcardT141_6
      (fun i => conj_mem_of_fixedPoints _ _ (T141_6 i) (hfix141_6 i) _)
      ⟨141, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 3 hp) Q2.T141_6_2 Q2.hfix141_6_2 Q2.hinj141_6_2
      Q2.hcardT141_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_6_2 i) (Q2.hfix141_6_2 i) _)
      colCert_141_6_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_6_4 (hp : 4 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp)) T141_6
      hfix141_6 hinj141_6 hcardT141_6
      (fun i => conj_mem_of_fixedPoints _ _ (T141_6 i) (hfix141_6 i) _)
      ⟨141, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 4 hp) Q2.T141_6_2 Q2.hfix141_6_2 Q2.hinj141_6_2
      Q2.hcardT141_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_6_2 i) (Q2.hfix141_6_2 i) _)
      colCert_141_6_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_7_0 (hp : 0 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp)) T141_7
      hfix141_7 hinj141_7 hcardT141_7
      (fun i => conj_mem_of_fixedPoints _ _ (T141_7 i) (hfix141_7 i) _)
      ⟨141, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 0 hp) Q2.T141_7_2 Q2.hfix141_7_2 Q2.hinj141_7_2
      Q2.hcardT141_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_7_2 i) (Q2.hfix141_7_2 i) _)
      colCert_141_7_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_7_1 (hp : 1 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp)) T141_7
      hfix141_7 hinj141_7 hcardT141_7
      (fun i => conj_mem_of_fixedPoints _ _ (T141_7 i) (hfix141_7 i) _)
      ⟨141, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 1 hp) Q2.T141_7_2 Q2.hfix141_7_2 Q2.hinj141_7_2
      Q2.hcardT141_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_7_2 i) (Q2.hfix141_7_2 i) _)
      colCert_141_7_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_7_2 (hp : 2 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp)) T141_7
      hfix141_7 hinj141_7 hcardT141_7
      (fun i => conj_mem_of_fixedPoints _ _ (T141_7 i) (hfix141_7 i) _)
      ⟨141, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 2 hp) Q2.T141_7_2 Q2.hfix141_7_2 Q2.hinj141_7_2
      Q2.hcardT141_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_7_2 i) (Q2.hfix141_7_2 i) _)
      colCert_141_7_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_7_3 (hp : 3 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp)) T141_7
      hfix141_7 hinj141_7 hcardT141_7
      (fun i => conj_mem_of_fixedPoints _ _ (T141_7 i) (hfix141_7 i) _)
      ⟨141, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 3 hp) Q2.T141_7_2 Q2.hfix141_7_2 Q2.hinj141_7_2
      Q2.hcardT141_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_7_2 i) (Q2.hfix141_7_2 i) _)
      colCert_141_7_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_7_4 (hp : 4 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp)) T141_7
      hfix141_7 hinj141_7 hcardT141_7
      (fun i => conj_mem_of_fixedPoints _ _ (T141_7 i) (hfix141_7 i) _)
      ⟨141, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 4 hp) Q2.T141_7_2 Q2.hfix141_7_2 Q2.hinj141_7_2
      Q2.hcardT141_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_7_2 i) (Q2.hfix141_7_2 i) _)
      colCert_141_7_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_8_0 (hp : 0 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp)) T141_8
      hfix141_8 hinj141_8 hcardT141_8
      (fun i => conj_mem_of_fixedPoints _ _ (T141_8 i) (hfix141_8 i) _)
      ⟨141, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 0 hp) Q2.T141_8_2 Q2.hfix141_8_2 Q2.hinj141_8_2
      Q2.hcardT141_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_8_2 i) (Q2.hfix141_8_2 i) _)
      colCert_141_8_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_8_1 (hp : 1 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp)) T141_8
      hfix141_8 hinj141_8 hcardT141_8
      (fun i => conj_mem_of_fixedPoints _ _ (T141_8 i) (hfix141_8 i) _)
      ⟨141, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 1 hp) Q2.T141_8_2 Q2.hfix141_8_2 Q2.hinj141_8_2
      Q2.hcardT141_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_8_2 i) (Q2.hfix141_8_2 i) _)
      colCert_141_8_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_8_2 (hp : 2 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp)) T141_8
      hfix141_8 hinj141_8 hcardT141_8
      (fun i => conj_mem_of_fixedPoints _ _ (T141_8 i) (hfix141_8 i) _)
      ⟨141, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 2 hp) Q2.T141_8_2 Q2.hfix141_8_2 Q2.hinj141_8_2
      Q2.hcardT141_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_8_2 i) (Q2.hfix141_8_2 i) _)
      colCert_141_8_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_8_3 (hp : 3 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp)) T141_8
      hfix141_8 hinj141_8 hcardT141_8
      (fun i => conj_mem_of_fixedPoints _ _ (T141_8 i) (hfix141_8 i) _)
      ⟨141, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 3 hp) Q2.T141_8_2 Q2.hfix141_8_2 Q2.hinj141_8_2
      Q2.hcardT141_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_8_2 i) (Q2.hfix141_8_2 i) _)
      colCert_141_8_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_8_4 (hp : 4 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp)) T141_8
      hfix141_8 hinj141_8 hcardT141_8
      (fun i => conj_mem_of_fixedPoints _ _ (T141_8 i) (hfix141_8 i) _)
      ⟨141, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 4 hp) Q2.T141_8_2 Q2.hfix141_8_2 Q2.hinj141_8_2
      Q2.hcardT141_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_8_2 i) (Q2.hfix141_8_2 i) _)
      colCert_141_8_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_9_0 (hp : 0 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp)) T141_9
      hfix141_9 hinj141_9 hcardT141_9
      (fun i => conj_mem_of_fixedPoints _ _ (T141_9 i) (hfix141_9 i) _)
      ⟨141, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 0 hp) Q2.T141_9_2 Q2.hfix141_9_2 Q2.hinj141_9_2
      Q2.hcardT141_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_9_2 i) (Q2.hfix141_9_2 i) _)
      colCert_141_9_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_9_1 (hp : 1 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp)) T141_9
      hfix141_9 hinj141_9 hcardT141_9
      (fun i => conj_mem_of_fixedPoints _ _ (T141_9 i) (hfix141_9 i) _)
      ⟨141, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 1 hp) Q2.T141_9_2 Q2.hfix141_9_2 Q2.hinj141_9_2
      Q2.hcardT141_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_9_2 i) (Q2.hfix141_9_2 i) _)
      colCert_141_9_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_9_2 (hp : 2 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp)) T141_9
      hfix141_9 hinj141_9 hcardT141_9
      (fun i => conj_mem_of_fixedPoints _ _ (T141_9 i) (hfix141_9 i) _)
      ⟨141, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 2 hp) Q2.T141_9_2 Q2.hfix141_9_2 Q2.hinj141_9_2
      Q2.hcardT141_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_9_2 i) (Q2.hfix141_9_2 i) _)
      colCert_141_9_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_9_3 (hp : 3 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp)) T141_9
      hfix141_9 hinj141_9 hcardT141_9
      (fun i => conj_mem_of_fixedPoints _ _ (T141_9 i) (hfix141_9 i) _)
      ⟨141, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 3 hp) Q2.T141_9_2 Q2.hfix141_9_2 Q2.hinj141_9_2
      Q2.hcardT141_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_9_2 i) (Q2.hfix141_9_2 i) _)
      colCert_141_9_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_9_4 (hp : 4 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp)) T141_9
      hfix141_9 hinj141_9 hcardT141_9
      (fun i => conj_mem_of_fixedPoints _ _ (T141_9 i) (hfix141_9 i) _)
      ⟨141, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 4 hp) Q2.T141_9_2 Q2.hfix141_9_2 Q2.hinj141_9_2
      Q2.hcardT141_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_9_2 i) (Q2.hfix141_9_2 i) _)
      colCert_141_9_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T141_10
      hfix141_10 hinj141_10 hcardT141_10
      (fun i => conj_mem_of_fixedPoints _ _ (T141_10 i) (hfix141_10 i) _)
      ⟨141, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T141_10_2 Q2.hfix141_10_2 Q2.hinj141_10_2
      Q2.hcardT141_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_10_2 i) (Q2.hfix141_10_2 i) _)
      colCert_141_10_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T141_10
      hfix141_10 hinj141_10 hcardT141_10
      (fun i => conj_mem_of_fixedPoints _ _ (T141_10 i) (hfix141_10 i) _)
      ⟨141, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T141_10_2 Q2.hfix141_10_2 Q2.hinj141_10_2
      Q2.hcardT141_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_10_2 i) (Q2.hfix141_10_2 i) _)
      colCert_141_10_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T141_10
      hfix141_10 hinj141_10 hcardT141_10
      (fun i => conj_mem_of_fixedPoints _ _ (T141_10 i) (hfix141_10 i) _)
      ⟨141, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T141_10_2 Q2.hfix141_10_2 Q2.hinj141_10_2
      Q2.hcardT141_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_10_2 i) (Q2.hfix141_10_2 i) _)
      colCert_141_10_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T141_10
      hfix141_10 hinj141_10 hcardT141_10
      (fun i => conj_mem_of_fixedPoints _ _ (T141_10 i) (hfix141_10 i) _)
      ⟨141, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T141_10_2 Q2.hfix141_10_2 Q2.hinj141_10_2
      Q2.hcardT141_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_10_2 i) (Q2.hfix141_10_2 i) _)
      colCert_141_10_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T141_10
      hfix141_10 hinj141_10 hcardT141_10
      (fun i => conj_mem_of_fixedPoints _ _ (T141_10 i) (hfix141_10 i) _)
      ⟨141, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T141_10_2 Q2.hfix141_10_2 Q2.hinj141_10_2
      Q2.hcardT141_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_10_2 i) (Q2.hfix141_10_2 i) _)
      colCert_141_10_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_11_0 (hp : 0 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp)) T141_11
      hfix141_11 hinj141_11 hcardT141_11
      (fun i => conj_mem_of_fixedPoints _ _ (T141_11 i) (hfix141_11 i) _)
      ⟨141, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 0 hp) Q2.T141_11_2 Q2.hfix141_11_2 Q2.hinj141_11_2
      Q2.hcardT141_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_11_2 i) (Q2.hfix141_11_2 i) _)
      colCert_141_11_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_11_1 (hp : 1 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp)) T141_11
      hfix141_11 hinj141_11 hcardT141_11
      (fun i => conj_mem_of_fixedPoints _ _ (T141_11 i) (hfix141_11 i) _)
      ⟨141, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 1 hp) Q2.T141_11_2 Q2.hfix141_11_2 Q2.hinj141_11_2
      Q2.hcardT141_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_11_2 i) (Q2.hfix141_11_2 i) _)
      colCert_141_11_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_11_2 (hp : 2 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp)) T141_11
      hfix141_11 hinj141_11 hcardT141_11
      (fun i => conj_mem_of_fixedPoints _ _ (T141_11 i) (hfix141_11 i) _)
      ⟨141, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 2 hp) Q2.T141_11_2 Q2.hfix141_11_2 Q2.hinj141_11_2
      Q2.hcardT141_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_11_2 i) (Q2.hfix141_11_2 i) _)
      colCert_141_11_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_11_3 (hp : 3 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp)) T141_11
      hfix141_11 hinj141_11 hcardT141_11
      (fun i => conj_mem_of_fixedPoints _ _ (T141_11 i) (hfix141_11 i) _)
      ⟨141, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 3 hp) Q2.T141_11_2 Q2.hfix141_11_2 Q2.hinj141_11_2
      Q2.hcardT141_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_11_2 i) (Q2.hfix141_11_2 i) _)
      colCert_141_11_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_11_4 (hp : 4 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp)) T141_11
      hfix141_11 hinj141_11 hcardT141_11
      (fun i => conj_mem_of_fixedPoints _ _ (T141_11 i) (hfix141_11 i) _)
      ⟨141, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 4 hp) Q2.T141_11_2 Q2.hfix141_11_2 Q2.hinj141_11_2
      Q2.hcardT141_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_11_2 i) (Q2.hfix141_11_2 i) _)
      colCert_141_11_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T141_12
      hfix141_12 hinj141_12 hcardT141_12
      (fun i => conj_mem_of_fixedPoints _ _ (T141_12 i) (hfix141_12 i) _)
      ⟨141, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T141_12_2 Q2.hfix141_12_2 Q2.hinj141_12_2
      Q2.hcardT141_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_12_2 i) (Q2.hfix141_12_2 i) _)
      colCert_141_12_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T141_12
      hfix141_12 hinj141_12 hcardT141_12
      (fun i => conj_mem_of_fixedPoints _ _ (T141_12 i) (hfix141_12 i) _)
      ⟨141, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T141_12_2 Q2.hfix141_12_2 Q2.hinj141_12_2
      Q2.hcardT141_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_12_2 i) (Q2.hfix141_12_2 i) _)
      colCert_141_12_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T141_12
      hfix141_12 hinj141_12 hcardT141_12
      (fun i => conj_mem_of_fixedPoints _ _ (T141_12 i) (hfix141_12 i) _)
      ⟨141, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T141_12_2 Q2.hfix141_12_2 Q2.hinj141_12_2
      Q2.hcardT141_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_12_2 i) (Q2.hfix141_12_2 i) _)
      colCert_141_12_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T141_12
      hfix141_12 hinj141_12 hcardT141_12
      (fun i => conj_mem_of_fixedPoints _ _ (T141_12 i) (hfix141_12 i) _)
      ⟨141, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T141_12_2 Q2.hfix141_12_2 Q2.hinj141_12_2
      Q2.hcardT141_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_12_2 i) (Q2.hfix141_12_2 i) _)
      colCert_141_12_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T141_12
      hfix141_12 hinj141_12 hcardT141_12
      (fun i => conj_mem_of_fixedPoints _ _ (T141_12 i) (hfix141_12 i) _)
      ⟨141, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T141_12_2 Q2.hfix141_12_2 Q2.hinj141_12_2
      Q2.hcardT141_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_12_2 i) (Q2.hfix141_12_2 i) _)
      colCert_141_12_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_13_0 (hp : 0 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 0 (transLenTr ⟨13, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 0 (transLenTr ⟨13, by decide⟩ 0 hp)) T141_13
      hfix141_13 hinj141_13 hcardT141_13
      (fun i => conj_mem_of_fixedPoints _ _ (T141_13 i) (hfix141_13 i) _)
      ⟨141, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 0 hp) Q2.T141_13_2 Q2.hfix141_13_2 Q2.hinj141_13_2
      Q2.hcardT141_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_13_2 i) (Q2.hfix141_13_2 i) _)
      colCert_141_13_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_13_1 (hp : 1 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 1 (transLenTr ⟨13, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 1 (transLenTr ⟨13, by decide⟩ 1 hp)) T141_13
      hfix141_13 hinj141_13 hcardT141_13
      (fun i => conj_mem_of_fixedPoints _ _ (T141_13 i) (hfix141_13 i) _)
      ⟨141, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 1 hp) Q2.T141_13_2 Q2.hfix141_13_2 Q2.hinj141_13_2
      Q2.hcardT141_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_13_2 i) (Q2.hfix141_13_2 i) _)
      colCert_141_13_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_13_2 (hp : 2 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 2 (transLenTr ⟨13, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 2 (transLenTr ⟨13, by decide⟩ 2 hp)) T141_13
      hfix141_13 hinj141_13 hcardT141_13
      (fun i => conj_mem_of_fixedPoints _ _ (T141_13 i) (hfix141_13 i) _)
      ⟨141, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 2 hp) Q2.T141_13_2 Q2.hfix141_13_2 Q2.hinj141_13_2
      Q2.hcardT141_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_13_2 i) (Q2.hfix141_13_2 i) _)
      colCert_141_13_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_13_3 (hp : 3 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 3 (transLenTr ⟨13, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 3 (transLenTr ⟨13, by decide⟩ 3 hp)) T141_13
      hfix141_13 hinj141_13 hcardT141_13
      (fun i => conj_mem_of_fixedPoints _ _ (T141_13 i) (hfix141_13 i) _)
      ⟨141, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 3 hp) Q2.T141_13_2 Q2.hfix141_13_2 Q2.hinj141_13_2
      Q2.hcardT141_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_13_2 i) (Q2.hfix141_13_2 i) _)
      colCert_141_13_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_13_4 (hp : 4 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 4 (transLenTr ⟨13, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 4 (transLenTr ⟨13, by decide⟩ 4 hp)) T141_13
      hfix141_13 hinj141_13 hcardT141_13
      (fun i => conj_mem_of_fixedPoints _ _ (T141_13 i) (hfix141_13 i) _)
      ⟨141, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 4 hp) Q2.T141_13_2 Q2.hfix141_13_2 Q2.hinj141_13_2
      Q2.hcardT141_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_13_2 i) (Q2.hfix141_13_2 i) _)
      colCert_141_13_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_13_5 (hp : 5 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 5 (transLenTr ⟨13, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨141, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 5 (transLenTr ⟨13, by decide⟩ 5 hp)) T141_13
      hfix141_13 hinj141_13 hcardT141_13
      (fun i => conj_mem_of_fixedPoints _ _ (T141_13 i) (hfix141_13 i) _)
      ⟨141, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 5 hp) Q2.T141_13_2 Q2.hfix141_13_2 Q2.hinj141_13_2
      Q2.hcardT141_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_13_2 i) (Q2.hfix141_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨141, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 5 (transLenTr ⟨13, by decide⟩ 5 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T141_13 = colFn colCertDiv_141_13_5.D1 (m := 5) from colCertDiv_141_13_5.bind1,
    show colData2 (⟨141, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 5 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T141_13_2 = colFn colCertDiv_141_13_5.D2 (m := 5) from colCertDiv_141_13_5.bind2]
  rw [alnId_141 j hj]
  exact fastcode_of_tau ⟨141, by decide⟩ _ _ _
    ((alnId_141 j hj) ▸ Q2.listedAt (⟨141, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨141, by decide⟩ : Fin 148) hj hq).1) colCertDiv_141_13_5_tau_match


theorem leaf_141_13_6 (hp : 6 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 6 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 6 (transLenTr ⟨13, by decide⟩ 6 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨141, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 6 (transLenTr ⟨13, by decide⟩ 6 hp)) T141_13
      hfix141_13 hinj141_13 hcardT141_13
      (fun i => conj_mem_of_fixedPoints _ _ (T141_13 i) (hfix141_13 i) _)
      ⟨141, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 6 hp) Q2.T141_13_2 Q2.hfix141_13_2 Q2.hinj141_13_2
      Q2.hcardT141_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_13_2 i) (Q2.hfix141_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨141, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 6 (transLenTr ⟨13, by decide⟩ 6 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T141_13 = colFn colCertDiv_141_13_6.D1 (m := 5) from colCertDiv_141_13_6.bind1,
    show colData2 (⟨141, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 6 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T141_13_2 = colFn colCertDiv_141_13_6.D2 (m := 5) from colCertDiv_141_13_6.bind2]
  rw [alnId_141 j hj]
  exact fastcode_of_tau ⟨141, by decide⟩ _ _ _
    ((alnId_141 j hj) ▸ Q2.listedAt (⟨141, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨141, by decide⟩ : Fin 148) hj hq).1) colCertDiv_141_13_6_tau_match


theorem leaf_141_13_7 (hp : 7 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 7 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 7 (transLenTr ⟨13, by decide⟩ 7 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨141, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 7 (transLenTr ⟨13, by decide⟩ 7 hp)) T141_13
      hfix141_13 hinj141_13 hcardT141_13
      (fun i => conj_mem_of_fixedPoints _ _ (T141_13 i) (hfix141_13 i) _)
      ⟨141, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 7 hp) Q2.T141_13_2 Q2.hfix141_13_2 Q2.hinj141_13_2
      Q2.hcardT141_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_13_2 i) (Q2.hfix141_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨141, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 7 (transLenTr ⟨13, by decide⟩ 7 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T141_13 = colFn colCertDiv_141_13_7.D1 (m := 5) from colCertDiv_141_13_7.bind1,
    show colData2 (⟨141, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 7 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T141_13_2 = colFn colCertDiv_141_13_7.D2 (m := 5) from colCertDiv_141_13_7.bind2]
  rw [alnId_141 j hj]
  exact fastcode_of_tau ⟨141, by decide⟩ _ _ _
    ((alnId_141 j hj) ▸ Q2.listedAt (⟨141, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨141, by decide⟩ : Fin 148) hj hq).1) colCertDiv_141_13_7_tau_match


theorem leaf_141_13_8 (hp : 8 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 8 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 8 (transLenTr ⟨13, by decide⟩ 8 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨141, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 8 (transLenTr ⟨13, by decide⟩ 8 hp)) T141_13
      hfix141_13 hinj141_13 hcardT141_13
      (fun i => conj_mem_of_fixedPoints _ _ (T141_13 i) (hfix141_13 i) _)
      ⟨141, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 8 hp) Q2.T141_13_2 Q2.hfix141_13_2 Q2.hinj141_13_2
      Q2.hcardT141_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_13_2 i) (Q2.hfix141_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨141, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 8 (transLenTr ⟨13, by decide⟩ 8 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T141_13 = colFn colCertDiv_141_13_8.D1 (m := 5) from colCertDiv_141_13_8.bind1,
    show colData2 (⟨141, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 8 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T141_13_2 = colFn colCertDiv_141_13_8.D2 (m := 5) from colCertDiv_141_13_8.bind2]
  rw [alnId_141 j hj]
  exact fastcode_of_tau ⟨141, by decide⟩ _ _ _
    ((alnId_141 j hj) ▸ Q2.listedAt (⟨141, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨141, by decide⟩ : Fin 148) hj hq).1) colCertDiv_141_13_8_tau_match


theorem leaf_141_13_9 (hp : 9 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 9 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 9 (transLenTr ⟨13, by decide⟩ 9 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 9 (transLenTr ⟨13, by decide⟩ 9 hp)) T141_13
      hfix141_13 hinj141_13 hcardT141_13
      (fun i => conj_mem_of_fixedPoints _ _ (T141_13 i) (hfix141_13 i) _)
      ⟨141, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 9 hp) Q2.T141_13_2 Q2.hfix141_13_2 Q2.hinj141_13_2
      Q2.hcardT141_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_13_2 i) (Q2.hfix141_13_2 i) _)
      colCert_141_13_9.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_13_10 (hp : 10 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 10 (transLenTr ⟨13, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 10 (transLenTr ⟨13, by decide⟩ 10 hp)) T141_13
      hfix141_13 hinj141_13 hcardT141_13
      (fun i => conj_mem_of_fixedPoints _ _ (T141_13 i) (hfix141_13 i) _)
      ⟨141, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 10 hp) Q2.T141_13_2 Q2.hfix141_13_2 Q2.hinj141_13_2
      Q2.hcardT141_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_13_2 i) (Q2.hfix141_13_2 i) _)
      colCert_141_13_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_13_11 (hp : 11 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 11 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 11 (transLenTr ⟨13, by decide⟩ 11 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 11 (transLenTr ⟨13, by decide⟩ 11 hp)) T141_13
      hfix141_13 hinj141_13 hcardT141_13
      (fun i => conj_mem_of_fixedPoints _ _ (T141_13 i) (hfix141_13 i) _)
      ⟨141, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 11 hp) Q2.T141_13_2 Q2.hfix141_13_2 Q2.hinj141_13_2
      Q2.hcardT141_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_13_2 i) (Q2.hfix141_13_2 i) _)
      colCert_141_13_11.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_13_12 (hp : 12 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 12 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 12 (transLenTr ⟨13, by decide⟩ 12 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 12 (transLenTr ⟨13, by decide⟩ 12 hp)) T141_13
      hfix141_13 hinj141_13 hcardT141_13
      (fun i => conj_mem_of_fixedPoints _ _ (T141_13 i) (hfix141_13 i) _)
      ⟨141, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 12 hp) Q2.T141_13_2 Q2.hfix141_13_2 Q2.hinj141_13_2
      Q2.hcardT141_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_13_2 i) (Q2.hfix141_13_2 i) _)
      colCert_141_13_12.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_13_13 (hp : 13 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 13 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 13 (transLenTr ⟨13, by decide⟩ 13 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 13 (transLenTr ⟨13, by decide⟩ 13 hp)) T141_13
      hfix141_13 hinj141_13 hcardT141_13
      (fun i => conj_mem_of_fixedPoints _ _ (T141_13 i) (hfix141_13 i) _)
      ⟨141, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 13 hp) Q2.T141_13_2 Q2.hfix141_13_2 Q2.hinj141_13_2
      Q2.hcardT141_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_13_2 i) (Q2.hfix141_13_2 i) _)
      colCert_141_13_13.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_13_14 (hp : 14 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 14 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 14 (transLenTr ⟨13, by decide⟩ 14 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 14 (transLenTr ⟨13, by decide⟩ 14 hp)) T141_13
      hfix141_13 hinj141_13 hcardT141_13
      (fun i => conj_mem_of_fixedPoints _ _ (T141_13 i) (hfix141_13 i) _)
      ⟨141, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 14 hp) Q2.T141_13_2 Q2.hfix141_13_2 Q2.hinj141_13_2
      Q2.hcardT141_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_13_2 i) (Q2.hfix141_13_2 i) _)
      colCert_141_13_14.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_13_15 (hp : 15 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 15 (transLenTr ⟨13, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 15 (transLenTr ⟨13, by decide⟩ 15 hp)) T141_13
      hfix141_13 hinj141_13 hcardT141_13
      (fun i => conj_mem_of_fixedPoints _ _ (T141_13 i) (hfix141_13 i) _)
      ⟨141, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 15 hp) Q2.T141_13_2 Q2.hfix141_13_2 Q2.hinj141_13_2
      Q2.hcardT141_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_13_2 i) (Q2.hfix141_13_2 i) _)
      colCert_141_13_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_13_16 (hp : 16 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 16 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 16 (transLenTr ⟨13, by decide⟩ 16 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 16 (transLenTr ⟨13, by decide⟩ 16 hp)) T141_13
      hfix141_13 hinj141_13 hcardT141_13
      (fun i => conj_mem_of_fixedPoints _ _ (T141_13 i) (hfix141_13 i) _)
      ⟨141, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 16 hp) Q2.T141_13_2 Q2.hfix141_13_2 Q2.hinj141_13_2
      Q2.hcardT141_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_13_2 i) (Q2.hfix141_13_2 i) _)
      colCert_141_13_16.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_13_17 (hp : 17 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 17 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 17 (transLenTr ⟨13, by decide⟩ 17 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 17 (transLenTr ⟨13, by decide⟩ 17 hp)) T141_13
      hfix141_13 hinj141_13 hcardT141_13
      (fun i => conj_mem_of_fixedPoints _ _ (T141_13 i) (hfix141_13 i) _)
      ⟨141, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 17 hp) Q2.T141_13_2 Q2.hfix141_13_2 Q2.hinj141_13_2
      Q2.hcardT141_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_13_2 i) (Q2.hfix141_13_2 i) _)
      colCert_141_13_17.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_13_18 (hp : 18 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 18 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 18 (transLenTr ⟨13, by decide⟩ 18 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 18 (transLenTr ⟨13, by decide⟩ 18 hp)) T141_13
      hfix141_13 hinj141_13 hcardT141_13
      (fun i => conj_mem_of_fixedPoints _ _ (T141_13 i) (hfix141_13 i) _)
      ⟨141, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 18 hp) Q2.T141_13_2 Q2.hfix141_13_2 Q2.hinj141_13_2
      Q2.hcardT141_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_13_2 i) (Q2.hfix141_13_2 i) _)
      colCert_141_13_18.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_13_19 (hp : 19 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 19 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 19 (transLenTr ⟨13, by decide⟩ 19 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 19 (transLenTr ⟨13, by decide⟩ 19 hp)) T141_13
      hfix141_13 hinj141_13 hcardT141_13
      (fun i => conj_mem_of_fixedPoints _ _ (T141_13 i) (hfix141_13 i) _)
      ⟨141, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 19 hp) Q2.T141_13_2 Q2.hfix141_13_2 Q2.hinj141_13_2
      Q2.hcardT141_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_13_2 i) (Q2.hfix141_13_2 i) _)
      colCert_141_13_19.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_13_20 (hp : 20 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 20 (transLenTr ⟨13, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 20 (transLenTr ⟨13, by decide⟩ 20 hp)) T141_13
      hfix141_13 hinj141_13 hcardT141_13
      (fun i => conj_mem_of_fixedPoints _ _ (T141_13 i) (hfix141_13 i) _)
      ⟨141, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 20 hp) Q2.T141_13_2 Q2.hfix141_13_2 Q2.hinj141_13_2
      Q2.hcardT141_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_13_2 i) (Q2.hfix141_13_2 i) _)
      colCert_141_13_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_13_21 (hp : 21 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 21 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 21 (transLenTr ⟨13, by decide⟩ 21 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 21 (transLenTr ⟨13, by decide⟩ 21 hp)) T141_13
      hfix141_13 hinj141_13 hcardT141_13
      (fun i => conj_mem_of_fixedPoints _ _ (T141_13 i) (hfix141_13 i) _)
      ⟨141, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 21 hp) Q2.T141_13_2 Q2.hfix141_13_2 Q2.hinj141_13_2
      Q2.hcardT141_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_13_2 i) (Q2.hfix141_13_2 i) _)
      colCert_141_13_21.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_13_22 (hp : 22 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 22 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 22 (transLenTr ⟨13, by decide⟩ 22 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 22 (transLenTr ⟨13, by decide⟩ 22 hp)) T141_13
      hfix141_13 hinj141_13 hcardT141_13
      (fun i => conj_mem_of_fixedPoints _ _ (T141_13 i) (hfix141_13 i) _)
      ⟨141, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 22 hp) Q2.T141_13_2 Q2.hfix141_13_2 Q2.hinj141_13_2
      Q2.hcardT141_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_13_2 i) (Q2.hfix141_13_2 i) _)
      colCert_141_13_22.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_13_23 (hp : 23 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 23 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 23 (transLenTr ⟨13, by decide⟩ 23 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 23 (transLenTr ⟨13, by decide⟩ 23 hp)) T141_13
      hfix141_13 hinj141_13 hcardT141_13
      (fun i => conj_mem_of_fixedPoints _ _ (T141_13 i) (hfix141_13 i) _)
      ⟨141, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 23 hp) Q2.T141_13_2 Q2.hfix141_13_2 Q2.hinj141_13_2
      Q2.hcardT141_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_13_2 i) (Q2.hfix141_13_2 i) _)
      colCert_141_13_23.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_13_24 (hp : 24 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 24 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 24 (transLenTr ⟨13, by decide⟩ 24 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 24 (transLenTr ⟨13, by decide⟩ 24 hp)) T141_13
      hfix141_13 hinj141_13 hcardT141_13
      (fun i => conj_mem_of_fixedPoints _ _ (T141_13 i) (hfix141_13 i) _)
      ⟨141, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 24 hp) Q2.T141_13_2 Q2.hfix141_13_2 Q2.hinj141_13_2
      Q2.hcardT141_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_13_2 i) (Q2.hfix141_13_2 i) _)
      colCert_141_13_24.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_14_0 (hp : 0 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 0 (transLenTr ⟨14, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 0 (transLenTr ⟨14, by decide⟩ 0 hp)) T141_14
      hfix141_14 hinj141_14 hcardT141_14
      (fun i => conj_mem_of_fixedPoints _ _ (T141_14 i) (hfix141_14 i) _)
      ⟨141, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 0 hp) Q2.T141_14_2 Q2.hfix141_14_2 Q2.hinj141_14_2
      Q2.hcardT141_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_14_2 i) (Q2.hfix141_14_2 i) _)
      colCert_141_14_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_14_1 (hp : 1 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 1 (transLenTr ⟨14, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 1 (transLenTr ⟨14, by decide⟩ 1 hp)) T141_14
      hfix141_14 hinj141_14 hcardT141_14
      (fun i => conj_mem_of_fixedPoints _ _ (T141_14 i) (hfix141_14 i) _)
      ⟨141, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 1 hp) Q2.T141_14_2 Q2.hfix141_14_2 Q2.hinj141_14_2
      Q2.hcardT141_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_14_2 i) (Q2.hfix141_14_2 i) _)
      colCert_141_14_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_14_2 (hp : 2 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 2 (transLenTr ⟨14, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 2 (transLenTr ⟨14, by decide⟩ 2 hp)) T141_14
      hfix141_14 hinj141_14 hcardT141_14
      (fun i => conj_mem_of_fixedPoints _ _ (T141_14 i) (hfix141_14 i) _)
      ⟨141, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 2 hp) Q2.T141_14_2 Q2.hfix141_14_2 Q2.hinj141_14_2
      Q2.hcardT141_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_14_2 i) (Q2.hfix141_14_2 i) _)
      colCert_141_14_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_14_3 (hp : 3 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 3 (transLenTr ⟨14, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 3 (transLenTr ⟨14, by decide⟩ 3 hp)) T141_14
      hfix141_14 hinj141_14 hcardT141_14
      (fun i => conj_mem_of_fixedPoints _ _ (T141_14 i) (hfix141_14 i) _)
      ⟨141, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 3 hp) Q2.T141_14_2 Q2.hfix141_14_2 Q2.hinj141_14_2
      Q2.hcardT141_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_14_2 i) (Q2.hfix141_14_2 i) _)
      colCert_141_14_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_14_4 (hp : 4 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 4 (transLenTr ⟨14, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 4 (transLenTr ⟨14, by decide⟩ 4 hp)) T141_14
      hfix141_14 hinj141_14 hcardT141_14
      (fun i => conj_mem_of_fixedPoints _ _ (T141_14 i) (hfix141_14 i) _)
      ⟨141, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 4 hp) Q2.T141_14_2 Q2.hfix141_14_2 Q2.hinj141_14_2
      Q2.hcardT141_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_14_2 i) (Q2.hfix141_14_2 i) _)
      colCert_141_14_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_14_5 (hp : 5 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 5 (transLenTr ⟨14, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 5 (transLenTr ⟨14, by decide⟩ 5 hp)) T141_14
      hfix141_14 hinj141_14 hcardT141_14
      (fun i => conj_mem_of_fixedPoints _ _ (T141_14 i) (hfix141_14 i) _)
      ⟨141, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 5 hp) Q2.T141_14_2 Q2.hfix141_14_2 Q2.hinj141_14_2
      Q2.hcardT141_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_14_2 i) (Q2.hfix141_14_2 i) _)
      colCert_141_14_5.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_14_6 (hp : 6 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 6 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 6 (transLenTr ⟨14, by decide⟩ 6 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 6 (transLenTr ⟨14, by decide⟩ 6 hp)) T141_14
      hfix141_14 hinj141_14 hcardT141_14
      (fun i => conj_mem_of_fixedPoints _ _ (T141_14 i) (hfix141_14 i) _)
      ⟨141, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 6 hp) Q2.T141_14_2 Q2.hfix141_14_2 Q2.hinj141_14_2
      Q2.hcardT141_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_14_2 i) (Q2.hfix141_14_2 i) _)
      colCert_141_14_6.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_14_7 (hp : 7 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 7 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 7 (transLenTr ⟨14, by decide⟩ 7 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 7 (transLenTr ⟨14, by decide⟩ 7 hp)) T141_14
      hfix141_14 hinj141_14 hcardT141_14
      (fun i => conj_mem_of_fixedPoints _ _ (T141_14 i) (hfix141_14 i) _)
      ⟨141, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 7 hp) Q2.T141_14_2 Q2.hfix141_14_2 Q2.hinj141_14_2
      Q2.hcardT141_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_14_2 i) (Q2.hfix141_14_2 i) _)
      colCert_141_14_7.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_14_8 (hp : 8 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 8 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 8 (transLenTr ⟨14, by decide⟩ 8 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 8 (transLenTr ⟨14, by decide⟩ 8 hp)) T141_14
      hfix141_14 hinj141_14 hcardT141_14
      (fun i => conj_mem_of_fixedPoints _ _ (T141_14 i) (hfix141_14 i) _)
      ⟨141, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 8 hp) Q2.T141_14_2 Q2.hfix141_14_2 Q2.hinj141_14_2
      Q2.hcardT141_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_14_2 i) (Q2.hfix141_14_2 i) _)
      colCert_141_14_8.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_14_9 (hp : 9 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 9 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 9 (transLenTr ⟨14, by decide⟩ 9 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 9 (transLenTr ⟨14, by decide⟩ 9 hp)) T141_14
      hfix141_14 hinj141_14 hcardT141_14
      (fun i => conj_mem_of_fixedPoints _ _ (T141_14 i) (hfix141_14 i) _)
      ⟨141, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 9 hp) Q2.T141_14_2 Q2.hfix141_14_2 Q2.hinj141_14_2
      Q2.hcardT141_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_14_2 i) (Q2.hfix141_14_2 i) _)
      colCert_141_14_9.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_14_10 (hp : 10 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 10 (transLenTr ⟨14, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 10 (transLenTr ⟨14, by decide⟩ 10 hp)) T141_14
      hfix141_14 hinj141_14 hcardT141_14
      (fun i => conj_mem_of_fixedPoints _ _ (T141_14 i) (hfix141_14 i) _)
      ⟨141, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 10 hp) Q2.T141_14_2 Q2.hfix141_14_2 Q2.hinj141_14_2
      Q2.hcardT141_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_14_2 i) (Q2.hfix141_14_2 i) _)
      colCert_141_14_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_14_11 (hp : 11 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 11 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 11 (transLenTr ⟨14, by decide⟩ 11 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 11 (transLenTr ⟨14, by decide⟩ 11 hp)) T141_14
      hfix141_14 hinj141_14 hcardT141_14
      (fun i => conj_mem_of_fixedPoints _ _ (T141_14 i) (hfix141_14 i) _)
      ⟨141, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 11 hp) Q2.T141_14_2 Q2.hfix141_14_2 Q2.hinj141_14_2
      Q2.hcardT141_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_14_2 i) (Q2.hfix141_14_2 i) _)
      colCert_141_14_11.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_14_12 (hp : 12 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 12 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 12 (transLenTr ⟨14, by decide⟩ 12 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 12 (transLenTr ⟨14, by decide⟩ 12 hp)) T141_14
      hfix141_14 hinj141_14 hcardT141_14
      (fun i => conj_mem_of_fixedPoints _ _ (T141_14 i) (hfix141_14 i) _)
      ⟨141, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 12 hp) Q2.T141_14_2 Q2.hfix141_14_2 Q2.hinj141_14_2
      Q2.hcardT141_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_14_2 i) (Q2.hfix141_14_2 i) _)
      colCert_141_14_12.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_14_13 (hp : 13 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 13 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 13 (transLenTr ⟨14, by decide⟩ 13 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 13 (transLenTr ⟨14, by decide⟩ 13 hp)) T141_14
      hfix141_14 hinj141_14 hcardT141_14
      (fun i => conj_mem_of_fixedPoints _ _ (T141_14 i) (hfix141_14 i) _)
      ⟨141, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 13 hp) Q2.T141_14_2 Q2.hfix141_14_2 Q2.hinj141_14_2
      Q2.hcardT141_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_14_2 i) (Q2.hfix141_14_2 i) _)
      colCert_141_14_13.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_14_14 (hp : 14 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 14 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 14 (transLenTr ⟨14, by decide⟩ 14 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 14 (transLenTr ⟨14, by decide⟩ 14 hp)) T141_14
      hfix141_14 hinj141_14 hcardT141_14
      (fun i => conj_mem_of_fixedPoints _ _ (T141_14 i) (hfix141_14 i) _)
      ⟨141, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 14 hp) Q2.T141_14_2 Q2.hfix141_14_2 Q2.hinj141_14_2
      Q2.hcardT141_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_14_2 i) (Q2.hfix141_14_2 i) _)
      colCert_141_14_14.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_14_15 (hp : 15 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 15 (transLenTr ⟨14, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 15 (transLenTr ⟨14, by decide⟩ 15 hp)) T141_14
      hfix141_14 hinj141_14 hcardT141_14
      (fun i => conj_mem_of_fixedPoints _ _ (T141_14 i) (hfix141_14 i) _)
      ⟨141, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 15 hp) Q2.T141_14_2 Q2.hfix141_14_2 Q2.hinj141_14_2
      Q2.hcardT141_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_14_2 i) (Q2.hfix141_14_2 i) _)
      colCert_141_14_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_14_16 (hp : 16 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 16 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 16 (transLenTr ⟨14, by decide⟩ 16 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 16 (transLenTr ⟨14, by decide⟩ 16 hp)) T141_14
      hfix141_14 hinj141_14 hcardT141_14
      (fun i => conj_mem_of_fixedPoints _ _ (T141_14 i) (hfix141_14 i) _)
      ⟨141, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 16 hp) Q2.T141_14_2 Q2.hfix141_14_2 Q2.hinj141_14_2
      Q2.hcardT141_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_14_2 i) (Q2.hfix141_14_2 i) _)
      colCert_141_14_16.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_14_17 (hp : 17 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 17 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 17 (transLenTr ⟨14, by decide⟩ 17 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 17 (transLenTr ⟨14, by decide⟩ 17 hp)) T141_14
      hfix141_14 hinj141_14 hcardT141_14
      (fun i => conj_mem_of_fixedPoints _ _ (T141_14 i) (hfix141_14 i) _)
      ⟨141, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 17 hp) Q2.T141_14_2 Q2.hfix141_14_2 Q2.hinj141_14_2
      Q2.hcardT141_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_14_2 i) (Q2.hfix141_14_2 i) _)
      colCert_141_14_17.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_14_18 (hp : 18 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 18 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 18 (transLenTr ⟨14, by decide⟩ 18 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 18 (transLenTr ⟨14, by decide⟩ 18 hp)) T141_14
      hfix141_14 hinj141_14 hcardT141_14
      (fun i => conj_mem_of_fixedPoints _ _ (T141_14 i) (hfix141_14 i) _)
      ⟨141, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 18 hp) Q2.T141_14_2 Q2.hfix141_14_2 Q2.hinj141_14_2
      Q2.hcardT141_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_14_2 i) (Q2.hfix141_14_2 i) _)
      colCert_141_14_18.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_14_19 (hp : 19 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 19 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 19 (transLenTr ⟨14, by decide⟩ 19 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 19 (transLenTr ⟨14, by decide⟩ 19 hp)) T141_14
      hfix141_14 hinj141_14 hcardT141_14
      (fun i => conj_mem_of_fixedPoints _ _ (T141_14 i) (hfix141_14 i) _)
      ⟨141, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 19 hp) Q2.T141_14_2 Q2.hfix141_14_2 Q2.hinj141_14_2
      Q2.hcardT141_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_14_2 i) (Q2.hfix141_14_2 i) _)
      colCert_141_14_19.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_14_20 (hp : 20 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 20 (transLenTr ⟨14, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 20 (transLenTr ⟨14, by decide⟩ 20 hp)) T141_14
      hfix141_14 hinj141_14 hcardT141_14
      (fun i => conj_mem_of_fixedPoints _ _ (T141_14 i) (hfix141_14 i) _)
      ⟨141, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 20 hp) Q2.T141_14_2 Q2.hfix141_14_2 Q2.hinj141_14_2
      Q2.hcardT141_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_14_2 i) (Q2.hfix141_14_2 i) _)
      colCert_141_14_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_14_21 (hp : 21 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 21 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 21 (transLenTr ⟨14, by decide⟩ 21 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 21 (transLenTr ⟨14, by decide⟩ 21 hp)) T141_14
      hfix141_14 hinj141_14 hcardT141_14
      (fun i => conj_mem_of_fixedPoints _ _ (T141_14 i) (hfix141_14 i) _)
      ⟨141, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 21 hp) Q2.T141_14_2 Q2.hfix141_14_2 Q2.hinj141_14_2
      Q2.hcardT141_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_14_2 i) (Q2.hfix141_14_2 i) _)
      colCert_141_14_21.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_14_22 (hp : 22 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 22 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 22 (transLenTr ⟨14, by decide⟩ 22 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 22 (transLenTr ⟨14, by decide⟩ 22 hp)) T141_14
      hfix141_14 hinj141_14 hcardT141_14
      (fun i => conj_mem_of_fixedPoints _ _ (T141_14 i) (hfix141_14 i) _)
      ⟨141, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 22 hp) Q2.T141_14_2 Q2.hfix141_14_2 Q2.hinj141_14_2
      Q2.hcardT141_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_14_2 i) (Q2.hfix141_14_2 i) _)
      colCert_141_14_22.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_14_23 (hp : 23 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 23 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 23 (transLenTr ⟨14, by decide⟩ 23 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 23 (transLenTr ⟨14, by decide⟩ 23 hp)) T141_14
      hfix141_14 hinj141_14 hcardT141_14
      (fun i => conj_mem_of_fixedPoints _ _ (T141_14 i) (hfix141_14 i) _)
      ⟨141, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 23 hp) Q2.T141_14_2 Q2.hfix141_14_2 Q2.hinj141_14_2
      Q2.hcardT141_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_14_2 i) (Q2.hfix141_14_2 i) _)
      colCert_141_14_23.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_14_24 (hp : 24 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 24 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 24 (transLenTr ⟨14, by decide⟩ 24 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 24 (transLenTr ⟨14, by decide⟩ 24 hp)) T141_14
      hfix141_14 hinj141_14 hcardT141_14
      (fun i => conj_mem_of_fixedPoints _ _ (T141_14 i) (hfix141_14 i) _)
      ⟨141, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 24 hp) Q2.T141_14_2 Q2.hfix141_14_2 Q2.hinj141_14_2
      Q2.hcardT141_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_14_2 i) (Q2.hfix141_14_2 i) _)
      colCert_141_14_24.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_15_0 (hp : 0 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 0 (transLenTr ⟨15, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 0 (transLenTr ⟨15, by decide⟩ 0 hp)) T141_15
      hfix141_15 hinj141_15 hcardT141_15
      (fun i => conj_mem_of_fixedPoints _ _ (T141_15 i) (hfix141_15 i) _)
      ⟨141, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 0 hp) Q2.T141_15_2 Q2.hfix141_15_2 Q2.hinj141_15_2
      Q2.hcardT141_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_15_2 i) (Q2.hfix141_15_2 i) _)
      colCert_141_15_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_15_1 (hp : 1 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 1 (transLenTr ⟨15, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 1 (transLenTr ⟨15, by decide⟩ 1 hp)) T141_15
      hfix141_15 hinj141_15 hcardT141_15
      (fun i => conj_mem_of_fixedPoints _ _ (T141_15 i) (hfix141_15 i) _)
      ⟨141, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 1 hp) Q2.T141_15_2 Q2.hfix141_15_2 Q2.hinj141_15_2
      Q2.hcardT141_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_15_2 i) (Q2.hfix141_15_2 i) _)
      colCert_141_15_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_15_2 (hp : 2 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 2 (transLenTr ⟨15, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 2 (transLenTr ⟨15, by decide⟩ 2 hp)) T141_15
      hfix141_15 hinj141_15 hcardT141_15
      (fun i => conj_mem_of_fixedPoints _ _ (T141_15 i) (hfix141_15 i) _)
      ⟨141, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 2 hp) Q2.T141_15_2 Q2.hfix141_15_2 Q2.hinj141_15_2
      Q2.hcardT141_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_15_2 i) (Q2.hfix141_15_2 i) _)
      colCert_141_15_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_15_3 (hp : 3 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 3 (transLenTr ⟨15, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 3 (transLenTr ⟨15, by decide⟩ 3 hp)) T141_15
      hfix141_15 hinj141_15 hcardT141_15
      (fun i => conj_mem_of_fixedPoints _ _ (T141_15 i) (hfix141_15 i) _)
      ⟨141, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 3 hp) Q2.T141_15_2 Q2.hfix141_15_2 Q2.hinj141_15_2
      Q2.hcardT141_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_15_2 i) (Q2.hfix141_15_2 i) _)
      colCert_141_15_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_15_4 (hp : 4 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 4 (transLenTr ⟨15, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 4 (transLenTr ⟨15, by decide⟩ 4 hp)) T141_15
      hfix141_15 hinj141_15 hcardT141_15
      (fun i => conj_mem_of_fixedPoints _ _ (T141_15 i) (hfix141_15 i) _)
      ⟨141, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 4 hp) Q2.T141_15_2 Q2.hfix141_15_2 Q2.hinj141_15_2
      Q2.hcardT141_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_15_2 i) (Q2.hfix141_15_2 i) _)
      colCert_141_15_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_15_5 (hp : 5 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 5 (transLenTr ⟨15, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 5 (transLenTr ⟨15, by decide⟩ 5 hp)) T141_15
      hfix141_15 hinj141_15 hcardT141_15
      (fun i => conj_mem_of_fixedPoints _ _ (T141_15 i) (hfix141_15 i) _)
      ⟨141, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 5 hp) Q2.T141_15_2 Q2.hfix141_15_2 Q2.hinj141_15_2
      Q2.hcardT141_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_15_2 i) (Q2.hfix141_15_2 i) _)
      colCert_141_15_5.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_15_6 (hp : 6 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 6 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 6 (transLenTr ⟨15, by decide⟩ 6 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 6 (transLenTr ⟨15, by decide⟩ 6 hp)) T141_15
      hfix141_15 hinj141_15 hcardT141_15
      (fun i => conj_mem_of_fixedPoints _ _ (T141_15 i) (hfix141_15 i) _)
      ⟨141, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 6 hp) Q2.T141_15_2 Q2.hfix141_15_2 Q2.hinj141_15_2
      Q2.hcardT141_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_15_2 i) (Q2.hfix141_15_2 i) _)
      colCert_141_15_6.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_15_7 (hp : 7 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 7 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 7 (transLenTr ⟨15, by decide⟩ 7 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 7 (transLenTr ⟨15, by decide⟩ 7 hp)) T141_15
      hfix141_15 hinj141_15 hcardT141_15
      (fun i => conj_mem_of_fixedPoints _ _ (T141_15 i) (hfix141_15 i) _)
      ⟨141, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 7 hp) Q2.T141_15_2 Q2.hfix141_15_2 Q2.hinj141_15_2
      Q2.hcardT141_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_15_2 i) (Q2.hfix141_15_2 i) _)
      colCert_141_15_7.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_15_8 (hp : 8 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 8 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 8 (transLenTr ⟨15, by decide⟩ 8 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 8 (transLenTr ⟨15, by decide⟩ 8 hp)) T141_15
      hfix141_15 hinj141_15 hcardT141_15
      (fun i => conj_mem_of_fixedPoints _ _ (T141_15 i) (hfix141_15 i) _)
      ⟨141, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 8 hp) Q2.T141_15_2 Q2.hfix141_15_2 Q2.hinj141_15_2
      Q2.hcardT141_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_15_2 i) (Q2.hfix141_15_2 i) _)
      colCert_141_15_8.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_15_9 (hp : 9 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 9 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 9 (transLenTr ⟨15, by decide⟩ 9 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 9 (transLenTr ⟨15, by decide⟩ 9 hp)) T141_15
      hfix141_15 hinj141_15 hcardT141_15
      (fun i => conj_mem_of_fixedPoints _ _ (T141_15 i) (hfix141_15 i) _)
      ⟨141, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 9 hp) Q2.T141_15_2 Q2.hfix141_15_2 Q2.hinj141_15_2
      Q2.hcardT141_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_15_2 i) (Q2.hfix141_15_2 i) _)
      colCert_141_15_9.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_15_10 (hp : 10 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 10 (transLenTr ⟨15, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 10 (transLenTr ⟨15, by decide⟩ 10 hp)) T141_15
      hfix141_15 hinj141_15 hcardT141_15
      (fun i => conj_mem_of_fixedPoints _ _ (T141_15 i) (hfix141_15 i) _)
      ⟨141, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 10 hp) Q2.T141_15_2 Q2.hfix141_15_2 Q2.hinj141_15_2
      Q2.hcardT141_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_15_2 i) (Q2.hfix141_15_2 i) _)
      colCert_141_15_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_15_11 (hp : 11 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 11 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 11 (transLenTr ⟨15, by decide⟩ 11 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 11 (transLenTr ⟨15, by decide⟩ 11 hp)) T141_15
      hfix141_15 hinj141_15 hcardT141_15
      (fun i => conj_mem_of_fixedPoints _ _ (T141_15 i) (hfix141_15 i) _)
      ⟨141, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 11 hp) Q2.T141_15_2 Q2.hfix141_15_2 Q2.hinj141_15_2
      Q2.hcardT141_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_15_2 i) (Q2.hfix141_15_2 i) _)
      colCert_141_15_11.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_15_12 (hp : 12 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 12 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 12 (transLenTr ⟨15, by decide⟩ 12 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 12 (transLenTr ⟨15, by decide⟩ 12 hp)) T141_15
      hfix141_15 hinj141_15 hcardT141_15
      (fun i => conj_mem_of_fixedPoints _ _ (T141_15 i) (hfix141_15 i) _)
      ⟨141, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 12 hp) Q2.T141_15_2 Q2.hfix141_15_2 Q2.hinj141_15_2
      Q2.hcardT141_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_15_2 i) (Q2.hfix141_15_2 i) _)
      colCert_141_15_12.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_15_13 (hp : 13 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 13 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 13 (transLenTr ⟨15, by decide⟩ 13 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 13 (transLenTr ⟨15, by decide⟩ 13 hp)) T141_15
      hfix141_15 hinj141_15 hcardT141_15
      (fun i => conj_mem_of_fixedPoints _ _ (T141_15 i) (hfix141_15 i) _)
      ⟨141, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 13 hp) Q2.T141_15_2 Q2.hfix141_15_2 Q2.hinj141_15_2
      Q2.hcardT141_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_15_2 i) (Q2.hfix141_15_2 i) _)
      colCert_141_15_13.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_15_14 (hp : 14 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 14 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 14 (transLenTr ⟨15, by decide⟩ 14 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 14 (transLenTr ⟨15, by decide⟩ 14 hp)) T141_15
      hfix141_15 hinj141_15 hcardT141_15
      (fun i => conj_mem_of_fixedPoints _ _ (T141_15 i) (hfix141_15 i) _)
      ⟨141, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 14 hp) Q2.T141_15_2 Q2.hfix141_15_2 Q2.hinj141_15_2
      Q2.hcardT141_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_15_2 i) (Q2.hfix141_15_2 i) _)
      colCert_141_15_14.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_15_15 (hp : 15 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 15 (transLenTr ⟨15, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 15 (transLenTr ⟨15, by decide⟩ 15 hp)) T141_15
      hfix141_15 hinj141_15 hcardT141_15
      (fun i => conj_mem_of_fixedPoints _ _ (T141_15 i) (hfix141_15 i) _)
      ⟨141, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 15 hp) Q2.T141_15_2 Q2.hfix141_15_2 Q2.hinj141_15_2
      Q2.hcardT141_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_15_2 i) (Q2.hfix141_15_2 i) _)
      colCert_141_15_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_15_16 (hp : 16 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 16 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 16 (transLenTr ⟨15, by decide⟩ 16 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 16 (transLenTr ⟨15, by decide⟩ 16 hp)) T141_15
      hfix141_15 hinj141_15 hcardT141_15
      (fun i => conj_mem_of_fixedPoints _ _ (T141_15 i) (hfix141_15 i) _)
      ⟨141, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 16 hp) Q2.T141_15_2 Q2.hfix141_15_2 Q2.hinj141_15_2
      Q2.hcardT141_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_15_2 i) (Q2.hfix141_15_2 i) _)
      colCert_141_15_16.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_15_17 (hp : 17 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 17 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 17 (transLenTr ⟨15, by decide⟩ 17 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 17 (transLenTr ⟨15, by decide⟩ 17 hp)) T141_15
      hfix141_15 hinj141_15 hcardT141_15
      (fun i => conj_mem_of_fixedPoints _ _ (T141_15 i) (hfix141_15 i) _)
      ⟨141, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 17 hp) Q2.T141_15_2 Q2.hfix141_15_2 Q2.hinj141_15_2
      Q2.hcardT141_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_15_2 i) (Q2.hfix141_15_2 i) _)
      colCert_141_15_17.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_15_18 (hp : 18 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 18 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 18 (transLenTr ⟨15, by decide⟩ 18 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 18 (transLenTr ⟨15, by decide⟩ 18 hp)) T141_15
      hfix141_15 hinj141_15 hcardT141_15
      (fun i => conj_mem_of_fixedPoints _ _ (T141_15 i) (hfix141_15 i) _)
      ⟨141, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 18 hp) Q2.T141_15_2 Q2.hfix141_15_2 Q2.hinj141_15_2
      Q2.hcardT141_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_15_2 i) (Q2.hfix141_15_2 i) _)
      colCert_141_15_18.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_15_19 (hp : 19 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 19 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 19 (transLenTr ⟨15, by decide⟩ 19 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 19 (transLenTr ⟨15, by decide⟩ 19 hp)) T141_15
      hfix141_15 hinj141_15 hcardT141_15
      (fun i => conj_mem_of_fixedPoints _ _ (T141_15 i) (hfix141_15 i) _)
      ⟨141, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 19 hp) Q2.T141_15_2 Q2.hfix141_15_2 Q2.hinj141_15_2
      Q2.hcardT141_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_15_2 i) (Q2.hfix141_15_2 i) _)
      colCert_141_15_19.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_15_20 (hp : 20 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 20 (transLenTr ⟨15, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 20 (transLenTr ⟨15, by decide⟩ 20 hp)) T141_15
      hfix141_15 hinj141_15 hcardT141_15
      (fun i => conj_mem_of_fixedPoints _ _ (T141_15 i) (hfix141_15 i) _)
      ⟨141, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 20 hp) Q2.T141_15_2 Q2.hfix141_15_2 Q2.hinj141_15_2
      Q2.hcardT141_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_15_2 i) (Q2.hfix141_15_2 i) _)
      colCert_141_15_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_15_21 (hp : 21 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 21 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 21 (transLenTr ⟨15, by decide⟩ 21 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 21 (transLenTr ⟨15, by decide⟩ 21 hp)) T141_15
      hfix141_15 hinj141_15 hcardT141_15
      (fun i => conj_mem_of_fixedPoints _ _ (T141_15 i) (hfix141_15 i) _)
      ⟨141, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 21 hp) Q2.T141_15_2 Q2.hfix141_15_2 Q2.hinj141_15_2
      Q2.hcardT141_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_15_2 i) (Q2.hfix141_15_2 i) _)
      colCert_141_15_21.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_15_22 (hp : 22 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 22 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 22 (transLenTr ⟨15, by decide⟩ 22 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 22 (transLenTr ⟨15, by decide⟩ 22 hp)) T141_15
      hfix141_15 hinj141_15 hcardT141_15
      (fun i => conj_mem_of_fixedPoints _ _ (T141_15 i) (hfix141_15 i) _)
      ⟨141, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 22 hp) Q2.T141_15_2 Q2.hfix141_15_2 Q2.hinj141_15_2
      Q2.hcardT141_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_15_2 i) (Q2.hfix141_15_2 i) _)
      colCert_141_15_22.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_15_23 (hp : 23 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 23 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 23 (transLenTr ⟨15, by decide⟩ 23 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 23 (transLenTr ⟨15, by decide⟩ 23 hp)) T141_15
      hfix141_15 hinj141_15 hcardT141_15
      (fun i => conj_mem_of_fixedPoints _ _ (T141_15 i) (hfix141_15 i) _)
      ⟨141, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 23 hp) Q2.T141_15_2 Q2.hfix141_15_2 Q2.hinj141_15_2
      Q2.hcardT141_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_15_2 i) (Q2.hfix141_15_2 i) _)
      colCert_141_15_23.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_15_24 (hp : 24 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 24 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 24 (transLenTr ⟨15, by decide⟩ 24 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 24 (transLenTr ⟨15, by decide⟩ 24 hp)) T141_15
      hfix141_15 hinj141_15 hcardT141_15
      (fun i => conj_mem_of_fixedPoints _ _ (T141_15 i) (hfix141_15 i) _)
      ⟨141, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 24 hp) Q2.T141_15_2 Q2.hfix141_15_2 Q2.hinj141_15_2
      Q2.hcardT141_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_15_2 i) (Q2.hfix141_15_2 i) _)
      colCert_141_15_24.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_16_0 (hp : 0 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 0 (transLenTr ⟨16, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 0 (transLenTr ⟨16, by decide⟩ 0 hp)) T141_16
      hfix141_16 hinj141_16 hcardT141_16
      (fun i => conj_mem_of_fixedPoints _ _ (T141_16 i) (hfix141_16 i) _)
      ⟨141, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 0 hp) Q2.T141_16_2 Q2.hfix141_16_2 Q2.hinj141_16_2
      Q2.hcardT141_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_16_2 i) (Q2.hfix141_16_2 i) _)
      colCert_141_16_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_16_1 (hp : 1 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 1 (transLenTr ⟨16, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 1 (transLenTr ⟨16, by decide⟩ 1 hp)) T141_16
      hfix141_16 hinj141_16 hcardT141_16
      (fun i => conj_mem_of_fixedPoints _ _ (T141_16 i) (hfix141_16 i) _)
      ⟨141, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 1 hp) Q2.T141_16_2 Q2.hfix141_16_2 Q2.hinj141_16_2
      Q2.hcardT141_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_16_2 i) (Q2.hfix141_16_2 i) _)
      colCert_141_16_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_16_2 (hp : 2 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 2 (transLenTr ⟨16, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 2 (transLenTr ⟨16, by decide⟩ 2 hp)) T141_16
      hfix141_16 hinj141_16 hcardT141_16
      (fun i => conj_mem_of_fixedPoints _ _ (T141_16 i) (hfix141_16 i) _)
      ⟨141, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 2 hp) Q2.T141_16_2 Q2.hfix141_16_2 Q2.hinj141_16_2
      Q2.hcardT141_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_16_2 i) (Q2.hfix141_16_2 i) _)
      colCert_141_16_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_16_3 (hp : 3 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 3 (transLenTr ⟨16, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 3 (transLenTr ⟨16, by decide⟩ 3 hp)) T141_16
      hfix141_16 hinj141_16 hcardT141_16
      (fun i => conj_mem_of_fixedPoints _ _ (T141_16 i) (hfix141_16 i) _)
      ⟨141, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 3 hp) Q2.T141_16_2 Q2.hfix141_16_2 Q2.hinj141_16_2
      Q2.hcardT141_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_16_2 i) (Q2.hfix141_16_2 i) _)
      colCert_141_16_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_16_4 (hp : 4 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 4 (transLenTr ⟨16, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 4 (transLenTr ⟨16, by decide⟩ 4 hp)) T141_16
      hfix141_16 hinj141_16 hcardT141_16
      (fun i => conj_mem_of_fixedPoints _ _ (T141_16 i) (hfix141_16 i) _)
      ⟨141, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 4 hp) Q2.T141_16_2 Q2.hfix141_16_2 Q2.hinj141_16_2
      Q2.hcardT141_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_16_2 i) (Q2.hfix141_16_2 i) _)
      colCert_141_16_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_16_5 (hp : 5 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 5 (transLenTr ⟨16, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 5 (transLenTr ⟨16, by decide⟩ 5 hp)) T141_16
      hfix141_16 hinj141_16 hcardT141_16
      (fun i => conj_mem_of_fixedPoints _ _ (T141_16 i) (hfix141_16 i) _)
      ⟨141, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 5 hp) Q2.T141_16_2 Q2.hfix141_16_2 Q2.hinj141_16_2
      Q2.hcardT141_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_16_2 i) (Q2.hfix141_16_2 i) _)
      colCert_141_16_5.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_16_6 (hp : 6 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 6 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 6 (transLenTr ⟨16, by decide⟩ 6 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 6 (transLenTr ⟨16, by decide⟩ 6 hp)) T141_16
      hfix141_16 hinj141_16 hcardT141_16
      (fun i => conj_mem_of_fixedPoints _ _ (T141_16 i) (hfix141_16 i) _)
      ⟨141, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 6 hp) Q2.T141_16_2 Q2.hfix141_16_2 Q2.hinj141_16_2
      Q2.hcardT141_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_16_2 i) (Q2.hfix141_16_2 i) _)
      colCert_141_16_6.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_16_7 (hp : 7 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 7 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 7 (transLenTr ⟨16, by decide⟩ 7 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 7 (transLenTr ⟨16, by decide⟩ 7 hp)) T141_16
      hfix141_16 hinj141_16 hcardT141_16
      (fun i => conj_mem_of_fixedPoints _ _ (T141_16 i) (hfix141_16 i) _)
      ⟨141, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 7 hp) Q2.T141_16_2 Q2.hfix141_16_2 Q2.hinj141_16_2
      Q2.hcardT141_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_16_2 i) (Q2.hfix141_16_2 i) _)
      colCert_141_16_7.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_16_8 (hp : 8 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 8 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 8 (transLenTr ⟨16, by decide⟩ 8 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 8 (transLenTr ⟨16, by decide⟩ 8 hp)) T141_16
      hfix141_16 hinj141_16 hcardT141_16
      (fun i => conj_mem_of_fixedPoints _ _ (T141_16 i) (hfix141_16 i) _)
      ⟨141, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 8 hp) Q2.T141_16_2 Q2.hfix141_16_2 Q2.hinj141_16_2
      Q2.hcardT141_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_16_2 i) (Q2.hfix141_16_2 i) _)
      colCert_141_16_8.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_16_9 (hp : 9 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 9 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 9 (transLenTr ⟨16, by decide⟩ 9 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 9 (transLenTr ⟨16, by decide⟩ 9 hp)) T141_16
      hfix141_16 hinj141_16 hcardT141_16
      (fun i => conj_mem_of_fixedPoints _ _ (T141_16 i) (hfix141_16 i) _)
      ⟨141, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 9 hp) Q2.T141_16_2 Q2.hfix141_16_2 Q2.hinj141_16_2
      Q2.hcardT141_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_16_2 i) (Q2.hfix141_16_2 i) _)
      colCert_141_16_9.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_16_10 (hp : 10 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 10 (transLenTr ⟨16, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 10 (transLenTr ⟨16, by decide⟩ 10 hp)) T141_16
      hfix141_16 hinj141_16 hcardT141_16
      (fun i => conj_mem_of_fixedPoints _ _ (T141_16 i) (hfix141_16 i) _)
      ⟨141, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 10 hp) Q2.T141_16_2 Q2.hfix141_16_2 Q2.hinj141_16_2
      Q2.hcardT141_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_16_2 i) (Q2.hfix141_16_2 i) _)
      colCert_141_16_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_16_11 (hp : 11 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 11 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 11 (transLenTr ⟨16, by decide⟩ 11 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 11 (transLenTr ⟨16, by decide⟩ 11 hp)) T141_16
      hfix141_16 hinj141_16 hcardT141_16
      (fun i => conj_mem_of_fixedPoints _ _ (T141_16 i) (hfix141_16 i) _)
      ⟨141, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 11 hp) Q2.T141_16_2 Q2.hfix141_16_2 Q2.hinj141_16_2
      Q2.hcardT141_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_16_2 i) (Q2.hfix141_16_2 i) _)
      colCert_141_16_11.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_16_12 (hp : 12 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 12 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 12 (transLenTr ⟨16, by decide⟩ 12 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 12 (transLenTr ⟨16, by decide⟩ 12 hp)) T141_16
      hfix141_16 hinj141_16 hcardT141_16
      (fun i => conj_mem_of_fixedPoints _ _ (T141_16 i) (hfix141_16 i) _)
      ⟨141, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 12 hp) Q2.T141_16_2 Q2.hfix141_16_2 Q2.hinj141_16_2
      Q2.hcardT141_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_16_2 i) (Q2.hfix141_16_2 i) _)
      colCert_141_16_12.hD ?_).symm
  rw [alnId_141 j hj]


end LeanDring.P5Presentation
