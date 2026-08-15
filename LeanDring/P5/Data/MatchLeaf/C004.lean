/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColRestCheap.C139
import LeanDring.P5.Data.ColRestCheap.C140
import LeanDring.P5.Data.ColRestCheap.C007
import LeanDring.P5.Data.ColRestCheap.C008
import LeanDring.P5.Data.ColRestCheap.C009
import LeanDring.P5.Data.ColRestHeavy.C027
import LeanDring.P5.Data.ColRestHeavy.C028
import LeanDring.P5.Data.ColRestHeavy.C029
import LeanDring.P5.Data.ColRestHeavy.C030
import LeanDring.P5.Data.ColRestHeavy.C031
import LeanDring.P5.Data.ColRestHeavy.C032
import LeanDring.P5.Data.ColRestHeavy.C033
import LeanDring.P5.Data.ColRestHeavy.C034
import LeanDring.P5.Data.ColRestHeavy.C035
import LeanDring.P5.Data.ColRestHeavy.C036
import LeanDring.P5.Data.ColRestHeavy.C037
import LeanDring.P5.Data.ColRestHeavy.C038
import LeanDring.P5.Data.EntryA.C029
import LeanDring.P5.Data.EntryA.C030
import LeanDring.P5.Data.EntryA.C031
import LeanDring.P5.Data.EntryA.C032
import LeanDring.P5.Data.EntryA.C033
import LeanDring.P5.Data.EntryA.C034
import LeanDring.P5.Data.EntryA.C035
import LeanDring.P5.Data.EntryA.C036
import LeanDring.P5.Data.EntryA.C037
import LeanDring.P5.Data.EntryA.C038
import LeanDring.P5.Data.EntryA.C039
import LeanDring.P5.Data.EntryA.C040
import LeanDring.P5.Data.EntryA.C041
import LeanDring.P5.Data.EntryA.C042
import LeanDring.P5.Data.EntryK.C014
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesAlign.C011
import LeanDring.P5.Data.SpeciesAlign.C006
import LeanDring.P5.Data.SpeciesAlign.C007
import LeanDring.P5.Data.SpeciesAlign.C008
import LeanDring.P5.Data.SpeciesAlign.C009
import LeanDring.P5.Data.SpeciesAlign.C010

/-! # Stage-5 leaves, chunk 3 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_41_41_2 (hp : 2 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 41 []).length)
    (hq : (normIsRep.getD 41 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 2 hp)
        (rowE2 (⟨41, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp))
        (rowE1 (⟨41, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨41, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨41, by decide⟩ (listedAt ⟨41, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp)) T41_41
      hfix41_41 hinj41_41 hcardT41_41
      (fun i => conj_mem_of_fixedPoints _ _ (T41_41 i) (hfix41_41 i) _)
      ⟨41, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨41, by decide⟩ (Q2.listedAt ⟨41, by decide⟩
        (alnCheck_rep ⟨41, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 2 hp) Q2.T41_41_2 Q2.hfix41_41_2 Q2.hinj41_41_2
      Q2.hcardT41_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T41_41_2 i) (Q2.hfix41_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨41, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T41_41 = colFn colCert_41_41_2.D (m := 25) from colCert_41_41_2.bind1,
    show colData2 (⟨41, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 2 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T41_41_2 = colFn colCert_41_41_2.D (m := 25) from colCert_41_41_2.bind2]
  exact alnAll_41_41_2 j hj hq

theorem leaf_41_41_3 (hp : 3 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 41 []).length)
    (hq : (normIsRep.getD 41 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 3 hp)
        (rowE2 (⟨41, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp))
        (rowE1 (⟨41, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨41, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨41, by decide⟩ (listedAt ⟨41, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp)) T41_41
      hfix41_41 hinj41_41 hcardT41_41
      (fun i => conj_mem_of_fixedPoints _ _ (T41_41 i) (hfix41_41 i) _)
      ⟨41, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨41, by decide⟩ (Q2.listedAt ⟨41, by decide⟩
        (alnCheck_rep ⟨41, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 3 hp) Q2.T41_41_2 Q2.hfix41_41_2 Q2.hinj41_41_2
      Q2.hcardT41_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T41_41_2 i) (Q2.hfix41_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨41, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T41_41 = colFn colCert_41_41_3.D (m := 25) from colCert_41_41_3.bind1,
    show colData2 (⟨41, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 3 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T41_41_2 = colFn colCert_41_41_3.D (m := 25) from colCert_41_41_3.bind2]
  exact alnAll_41_41_3 j hj hq

theorem leaf_41_41_4 (hp : 4 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 41 []).length)
    (hq : (normIsRep.getD 41 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 4 hp)
        (rowE2 (⟨41, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp))
        (rowE1 (⟨41, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨41, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨41, by decide⟩ (listedAt ⟨41, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp)) T41_41
      hfix41_41 hinj41_41 hcardT41_41
      (fun i => conj_mem_of_fixedPoints _ _ (T41_41 i) (hfix41_41 i) _)
      ⟨41, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨41, by decide⟩ (Q2.listedAt ⟨41, by decide⟩
        (alnCheck_rep ⟨41, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 4 hp) Q2.T41_41_2 Q2.hfix41_41_2 Q2.hinj41_41_2
      Q2.hcardT41_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T41_41_2 i) (Q2.hfix41_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨41, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T41_41 = colFn colCert_41_41_4.D (m := 25) from colCert_41_41_4.bind1,
    show colData2 (⟨41, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 4 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T41_41_2 = colFn colCert_41_41_4.D (m := 25) from colCert_41_41_4.bind2]
  exact alnAll_41_41_4 j hj hq

theorem leaf_41_41_5 (hp : 5 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 41 []).length)
    (hq : (normIsRep.getD 41 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 5 hp)
        (rowE2 (⟨41, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp))
        (rowE1 (⟨41, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨41, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨41, by decide⟩ (listedAt ⟨41, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp)) T41_41
      hfix41_41 hinj41_41 hcardT41_41
      (fun i => conj_mem_of_fixedPoints _ _ (T41_41 i) (hfix41_41 i) _)
      ⟨41, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨41, by decide⟩ (Q2.listedAt ⟨41, by decide⟩
        (alnCheck_rep ⟨41, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 5 hp) Q2.T41_41_2 Q2.hfix41_41_2 Q2.hinj41_41_2
      Q2.hcardT41_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T41_41_2 i) (Q2.hfix41_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨41, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T41_41 = colFn colCert_41_41_5.D (m := 25) from colCert_41_41_5.bind1,
    show colData2 (⟨41, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 5 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T41_41_2 = colFn colCert_41_41_5.D (m := 25) from colCert_41_41_5.bind2]
  exact alnAll_41_41_5 j hj hq

theorem leaf_41_41_10 (hp : 10 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 41 []).length)
    (hq : (normIsRep.getD 41 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 10 hp)
        (rowE2 (⟨41, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp))
        (rowE1 (⟨41, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨41, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨41, by decide⟩ (listedAt ⟨41, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp)) T41_41
      hfix41_41 hinj41_41 hcardT41_41
      (fun i => conj_mem_of_fixedPoints _ _ (T41_41 i) (hfix41_41 i) _)
      ⟨41, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨41, by decide⟩ (Q2.listedAt ⟨41, by decide⟩
        (alnCheck_rep ⟨41, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 10 hp) Q2.T41_41_2 Q2.hfix41_41_2 Q2.hinj41_41_2
      Q2.hcardT41_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T41_41_2 i) (Q2.hfix41_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨41, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T41_41 = colFn colCert_41_41_10.D (m := 25) from colCert_41_41_10.bind1,
    show colData2 (⟨41, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 10 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T41_41_2 = colFn colCert_41_41_10.D (m := 25) from colCert_41_41_10.bind2]
  exact alnAll_41_41_10 j hj hq

theorem leaf_41_41_15 (hp : 15 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 41 []).length)
    (hq : (normIsRep.getD 41 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 15 hp)
        (rowE2 (⟨41, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp))
        (rowE1 (⟨41, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨41, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨41, by decide⟩ (listedAt ⟨41, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp)) T41_41
      hfix41_41 hinj41_41 hcardT41_41
      (fun i => conj_mem_of_fixedPoints _ _ (T41_41 i) (hfix41_41 i) _)
      ⟨41, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨41, by decide⟩ (Q2.listedAt ⟨41, by decide⟩
        (alnCheck_rep ⟨41, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 15 hp) Q2.T41_41_2 Q2.hfix41_41_2 Q2.hinj41_41_2
      Q2.hcardT41_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T41_41_2 i) (Q2.hfix41_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨41, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T41_41 = colFn colCert_41_41_15.D (m := 25) from colCert_41_41_15.bind1,
    show colData2 (⟨41, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 15 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T41_41_2 = colFn colCert_41_41_15.D (m := 25) from colCert_41_41_15.bind2]
  exact alnAll_41_41_15 j hj hq

theorem leaf_41_41_20 (hp : 20 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 41 []).length)
    (hq : (normIsRep.getD 41 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 20 hp)
        (rowE2 (⟨41, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp))
        (rowE1 (⟨41, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨41, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨41, by decide⟩ (listedAt ⟨41, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp)) T41_41
      hfix41_41 hinj41_41 hcardT41_41
      (fun i => conj_mem_of_fixedPoints _ _ (T41_41 i) (hfix41_41 i) _)
      ⟨41, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨41, by decide⟩ (Q2.listedAt ⟨41, by decide⟩
        (alnCheck_rep ⟨41, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 20 hp) Q2.T41_41_2 Q2.hfix41_41_2 Q2.hinj41_41_2
      Q2.hcardT41_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T41_41_2 i) (Q2.hfix41_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨41, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T41_41 = colFn colCert_41_41_20.D (m := 25) from colCert_41_41_20.bind1,
    show colData2 (⟨41, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 20 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T41_41_2 = colFn colCert_41_41_20.D (m := 25) from colCert_41_41_20.bind2]
  exact alnAll_41_41_20 j hj hq

theorem leaf_42_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 42 []).length)
    (hq : (normIsRep.getD 42 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨42, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨42, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨42, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨42, by decide⟩ (listedAt ⟨42, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T42_12
      hfix42_12 hinj42_12 hcardT42_12
      (fun i => conj_mem_of_fixedPoints _ _ (T42_12 i) (hfix42_12 i) _)
      ⟨42, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨42, by decide⟩ (Q2.listedAt ⟨42, by decide⟩
        (alnCheck_rep ⟨42, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T42_12_2 Q2.hfix42_12_2 Q2.hinj42_12_2
      Q2.hcardT42_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T42_12_2 i) (Q2.hfix42_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨42, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T42_12 = colFn colCert_42_12_0.D (m := 125) from colCert_42_12_0.bind1,
    show colData2 (⟨42, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T42_12_2 = colFn colCert_42_12_0.D (m := 125) from colCert_42_12_0.bind2]
  exact alnAll_42_12_0 j hj hq

theorem leaf_42_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 42 []).length)
    (hq : (normIsRep.getD 42 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨42, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨42, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨42, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨42, by decide⟩ (listedAt ⟨42, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T42_12
      hfix42_12 hinj42_12 hcardT42_12
      (fun i => conj_mem_of_fixedPoints _ _ (T42_12 i) (hfix42_12 i) _)
      ⟨42, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨42, by decide⟩ (Q2.listedAt ⟨42, by decide⟩
        (alnCheck_rep ⟨42, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T42_12_2 Q2.hfix42_12_2 Q2.hinj42_12_2
      Q2.hcardT42_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T42_12_2 i) (Q2.hfix42_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨42, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T42_12 = colFn colCert_42_12_1.D (m := 125) from colCert_42_12_1.bind1,
    show colData2 (⟨42, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T42_12_2 = colFn colCert_42_12_1.D (m := 125) from colCert_42_12_1.bind2]
  exact alnAll_42_12_1 j hj hq

theorem leaf_42_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 42 []).length)
    (hq : (normIsRep.getD 42 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨42, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨42, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨42, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨42, by decide⟩ (listedAt ⟨42, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T42_12
      hfix42_12 hinj42_12 hcardT42_12
      (fun i => conj_mem_of_fixedPoints _ _ (T42_12 i) (hfix42_12 i) _)
      ⟨42, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨42, by decide⟩ (Q2.listedAt ⟨42, by decide⟩
        (alnCheck_rep ⟨42, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T42_12_2 Q2.hfix42_12_2 Q2.hinj42_12_2
      Q2.hcardT42_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T42_12_2 i) (Q2.hfix42_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨42, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T42_12 = colFn colCert_42_12_2.D (m := 125) from colCert_42_12_2.bind1,
    show colData2 (⟨42, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T42_12_2 = colFn colCert_42_12_2.D (m := 125) from colCert_42_12_2.bind2]
  exact alnAll_42_12_2 j hj hq

theorem leaf_42_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 42 []).length)
    (hq : (normIsRep.getD 42 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨42, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨42, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨42, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨42, by decide⟩ (listedAt ⟨42, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T42_12
      hfix42_12 hinj42_12 hcardT42_12
      (fun i => conj_mem_of_fixedPoints _ _ (T42_12 i) (hfix42_12 i) _)
      ⟨42, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨42, by decide⟩ (Q2.listedAt ⟨42, by decide⟩
        (alnCheck_rep ⟨42, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T42_12_2 Q2.hfix42_12_2 Q2.hinj42_12_2
      Q2.hcardT42_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T42_12_2 i) (Q2.hfix42_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨42, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T42_12 = colFn colCert_42_12_3.D (m := 125) from colCert_42_12_3.bind1,
    show colData2 (⟨42, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T42_12_2 = colFn colCert_42_12_3.D (m := 125) from colCert_42_12_3.bind2]
  exact alnAll_42_12_3 j hj hq

theorem leaf_42_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 42 []).length)
    (hq : (normIsRep.getD 42 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨42, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨42, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨42, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨42, by decide⟩ (listedAt ⟨42, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T42_12
      hfix42_12 hinj42_12 hcardT42_12
      (fun i => conj_mem_of_fixedPoints _ _ (T42_12 i) (hfix42_12 i) _)
      ⟨42, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨42, by decide⟩ (Q2.listedAt ⟨42, by decide⟩
        (alnCheck_rep ⟨42, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T42_12_2 Q2.hfix42_12_2 Q2.hinj42_12_2
      Q2.hcardT42_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T42_12_2 i) (Q2.hfix42_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨42, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T42_12 = colFn colCert_42_12_4.D (m := 125) from colCert_42_12_4.bind1,
    show colData2 (⟨42, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T42_12_2 = colFn colCert_42_12_4.D (m := 125) from colCert_42_12_4.bind2]
  exact alnAll_42_12_4 j hj hq

theorem leaf_42_42_0 (hp : 0 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 42 []).length)
    (hq : (normIsRep.getD 42 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 0 hp)
        (rowE2 (⟨42, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp))
        (rowE1 (⟨42, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨42, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨42, by decide⟩ (listedAt ⟨42, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp)) T42_42
      hfix42_42 hinj42_42 hcardT42_42
      (fun i => conj_mem_of_fixedPoints _ _ (T42_42 i) (hfix42_42 i) _)
      ⟨42, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨42, by decide⟩ (Q2.listedAt ⟨42, by decide⟩
        (alnCheck_rep ⟨42, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 0 hp) Q2.T42_42_2 Q2.hfix42_42_2 Q2.hinj42_42_2
      Q2.hcardT42_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T42_42_2 i) (Q2.hfix42_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨42, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T42_42 = colFn colCert_42_42_0.D (m := 25) from colCert_42_42_0.bind1,
    show colData2 (⟨42, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 0 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T42_42_2 = colFn colCert_42_42_0.D (m := 25) from colCert_42_42_0.bind2]
  exact alnAll_42_42_0 j hj hq

theorem leaf_42_42_1 (hp : 1 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 42 []).length)
    (hq : (normIsRep.getD 42 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 1 hp)
        (rowE2 (⟨42, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp))
        (rowE1 (⟨42, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨42, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨42, by decide⟩ (listedAt ⟨42, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp)) T42_42
      hfix42_42 hinj42_42 hcardT42_42
      (fun i => conj_mem_of_fixedPoints _ _ (T42_42 i) (hfix42_42 i) _)
      ⟨42, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨42, by decide⟩ (Q2.listedAt ⟨42, by decide⟩
        (alnCheck_rep ⟨42, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 1 hp) Q2.T42_42_2 Q2.hfix42_42_2 Q2.hinj42_42_2
      Q2.hcardT42_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T42_42_2 i) (Q2.hfix42_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨42, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T42_42 = colFn colCert_42_42_1.D (m := 25) from colCert_42_42_1.bind1,
    show colData2 (⟨42, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 1 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T42_42_2 = colFn colCert_42_42_1.D (m := 25) from colCert_42_42_1.bind2]
  exact alnAll_42_42_1 j hj hq

theorem leaf_42_42_2 (hp : 2 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 42 []).length)
    (hq : (normIsRep.getD 42 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 2 hp)
        (rowE2 (⟨42, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp))
        (rowE1 (⟨42, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨42, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨42, by decide⟩ (listedAt ⟨42, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp)) T42_42
      hfix42_42 hinj42_42 hcardT42_42
      (fun i => conj_mem_of_fixedPoints _ _ (T42_42 i) (hfix42_42 i) _)
      ⟨42, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨42, by decide⟩ (Q2.listedAt ⟨42, by decide⟩
        (alnCheck_rep ⟨42, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 2 hp) Q2.T42_42_2 Q2.hfix42_42_2 Q2.hinj42_42_2
      Q2.hcardT42_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T42_42_2 i) (Q2.hfix42_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨42, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T42_42 = colFn colCert_42_42_2.D (m := 25) from colCert_42_42_2.bind1,
    show colData2 (⟨42, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 2 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T42_42_2 = colFn colCert_42_42_2.D (m := 25) from colCert_42_42_2.bind2]
  exact alnAll_42_42_2 j hj hq

theorem leaf_42_42_3 (hp : 3 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 42 []).length)
    (hq : (normIsRep.getD 42 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 3 hp)
        (rowE2 (⟨42, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp))
        (rowE1 (⟨42, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨42, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨42, by decide⟩ (listedAt ⟨42, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp)) T42_42
      hfix42_42 hinj42_42 hcardT42_42
      (fun i => conj_mem_of_fixedPoints _ _ (T42_42 i) (hfix42_42 i) _)
      ⟨42, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨42, by decide⟩ (Q2.listedAt ⟨42, by decide⟩
        (alnCheck_rep ⟨42, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 3 hp) Q2.T42_42_2 Q2.hfix42_42_2 Q2.hinj42_42_2
      Q2.hcardT42_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T42_42_2 i) (Q2.hfix42_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨42, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T42_42 = colFn colCert_42_42_3.D (m := 25) from colCert_42_42_3.bind1,
    show colData2 (⟨42, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 3 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T42_42_2 = colFn colCert_42_42_3.D (m := 25) from colCert_42_42_3.bind2]
  exact alnAll_42_42_3 j hj hq

theorem leaf_42_42_4 (hp : 4 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 42 []).length)
    (hq : (normIsRep.getD 42 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 4 hp)
        (rowE2 (⟨42, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp))
        (rowE1 (⟨42, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨42, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨42, by decide⟩ (listedAt ⟨42, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp)) T42_42
      hfix42_42 hinj42_42 hcardT42_42
      (fun i => conj_mem_of_fixedPoints _ _ (T42_42 i) (hfix42_42 i) _)
      ⟨42, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨42, by decide⟩ (Q2.listedAt ⟨42, by decide⟩
        (alnCheck_rep ⟨42, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 4 hp) Q2.T42_42_2 Q2.hfix42_42_2 Q2.hinj42_42_2
      Q2.hcardT42_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T42_42_2 i) (Q2.hfix42_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨42, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T42_42 = colFn colCert_42_42_4.D (m := 25) from colCert_42_42_4.bind1,
    show colData2 (⟨42, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 4 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T42_42_2 = colFn colCert_42_42_4.D (m := 25) from colCert_42_42_4.bind2]
  exact alnAll_42_42_4 j hj hq

theorem leaf_42_42_5 (hp : 5 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 42 []).length)
    (hq : (normIsRep.getD 42 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 5 hp)
        (rowE2 (⟨42, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp))
        (rowE1 (⟨42, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨42, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨42, by decide⟩ (listedAt ⟨42, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp)) T42_42
      hfix42_42 hinj42_42 hcardT42_42
      (fun i => conj_mem_of_fixedPoints _ _ (T42_42 i) (hfix42_42 i) _)
      ⟨42, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨42, by decide⟩ (Q2.listedAt ⟨42, by decide⟩
        (alnCheck_rep ⟨42, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 5 hp) Q2.T42_42_2 Q2.hfix42_42_2 Q2.hinj42_42_2
      Q2.hcardT42_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T42_42_2 i) (Q2.hfix42_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨42, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T42_42 = colFn colCert_42_42_5.D (m := 25) from colCert_42_42_5.bind1,
    show colData2 (⟨42, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 5 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T42_42_2 = colFn colCert_42_42_5.D (m := 25) from colCert_42_42_5.bind2]
  exact alnAll_42_42_5 j hj hq

theorem leaf_42_42_10 (hp : 10 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 42 []).length)
    (hq : (normIsRep.getD 42 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 10 hp)
        (rowE2 (⟨42, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp))
        (rowE1 (⟨42, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨42, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨42, by decide⟩ (listedAt ⟨42, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp)) T42_42
      hfix42_42 hinj42_42 hcardT42_42
      (fun i => conj_mem_of_fixedPoints _ _ (T42_42 i) (hfix42_42 i) _)
      ⟨42, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨42, by decide⟩ (Q2.listedAt ⟨42, by decide⟩
        (alnCheck_rep ⟨42, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 10 hp) Q2.T42_42_2 Q2.hfix42_42_2 Q2.hinj42_42_2
      Q2.hcardT42_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T42_42_2 i) (Q2.hfix42_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨42, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T42_42 = colFn colCert_42_42_10.D (m := 25) from colCert_42_42_10.bind1,
    show colData2 (⟨42, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 10 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T42_42_2 = colFn colCert_42_42_10.D (m := 25) from colCert_42_42_10.bind2]
  exact alnAll_42_42_10 j hj hq

theorem leaf_42_42_15 (hp : 15 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 42 []).length)
    (hq : (normIsRep.getD 42 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 15 hp)
        (rowE2 (⟨42, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp))
        (rowE1 (⟨42, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨42, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨42, by decide⟩ (listedAt ⟨42, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp)) T42_42
      hfix42_42 hinj42_42 hcardT42_42
      (fun i => conj_mem_of_fixedPoints _ _ (T42_42 i) (hfix42_42 i) _)
      ⟨42, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨42, by decide⟩ (Q2.listedAt ⟨42, by decide⟩
        (alnCheck_rep ⟨42, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 15 hp) Q2.T42_42_2 Q2.hfix42_42_2 Q2.hinj42_42_2
      Q2.hcardT42_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T42_42_2 i) (Q2.hfix42_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨42, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T42_42 = colFn colCert_42_42_15.D (m := 25) from colCert_42_42_15.bind1,
    show colData2 (⟨42, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 15 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T42_42_2 = colFn colCert_42_42_15.D (m := 25) from colCert_42_42_15.bind2]
  exact alnAll_42_42_15 j hj hq

theorem leaf_42_42_20 (hp : 20 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 42 []).length)
    (hq : (normIsRep.getD 42 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 20 hp)
        (rowE2 (⟨42, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp))
        (rowE1 (⟨42, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨42, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨42, by decide⟩ (listedAt ⟨42, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp)) T42_42
      hfix42_42 hinj42_42 hcardT42_42
      (fun i => conj_mem_of_fixedPoints _ _ (T42_42 i) (hfix42_42 i) _)
      ⟨42, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨42, by decide⟩ (Q2.listedAt ⟨42, by decide⟩
        (alnCheck_rep ⟨42, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 20 hp) Q2.T42_42_2 Q2.hfix42_42_2 Q2.hinj42_42_2
      Q2.hcardT42_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T42_42_2 i) (Q2.hfix42_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨42, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T42_42 = colFn colCert_42_42_20.D (m := 25) from colCert_42_42_20.bind1,
    show colData2 (⟨42, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 20 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T42_42_2 = colFn colCert_42_42_20.D (m := 25) from colCert_42_42_20.bind2]
  exact alnAll_42_42_20 j hj hq

theorem leaf_43_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 43 []).length)
    (hq : (normIsRep.getD 43 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨43, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨43, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨43, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨43, by decide⟩ (listedAt ⟨43, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T43_12
      hfix43_12 hinj43_12 hcardT43_12
      (fun i => conj_mem_of_fixedPoints _ _ (T43_12 i) (hfix43_12 i) _)
      ⟨43, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨43, by decide⟩ (Q2.listedAt ⟨43, by decide⟩
        (alnCheck_rep ⟨43, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T43_12_2 Q2.hfix43_12_2 Q2.hinj43_12_2
      Q2.hcardT43_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T43_12_2 i) (Q2.hfix43_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨43, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T43_12 = colFn colCert_43_12_0.D (m := 125) from colCert_43_12_0.bind1,
    show colData2 (⟨43, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T43_12_2 = colFn colCert_43_12_0.D (m := 125) from colCert_43_12_0.bind2]
  exact alnAll_43_12_0 j hj hq

theorem leaf_43_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 43 []).length)
    (hq : (normIsRep.getD 43 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨43, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨43, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨43, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨43, by decide⟩ (listedAt ⟨43, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T43_12
      hfix43_12 hinj43_12 hcardT43_12
      (fun i => conj_mem_of_fixedPoints _ _ (T43_12 i) (hfix43_12 i) _)
      ⟨43, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨43, by decide⟩ (Q2.listedAt ⟨43, by decide⟩
        (alnCheck_rep ⟨43, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T43_12_2 Q2.hfix43_12_2 Q2.hinj43_12_2
      Q2.hcardT43_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T43_12_2 i) (Q2.hfix43_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨43, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T43_12 = colFn colCert_43_12_1.D (m := 125) from colCert_43_12_1.bind1,
    show colData2 (⟨43, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T43_12_2 = colFn colCert_43_12_1.D (m := 125) from colCert_43_12_1.bind2]
  exact alnAll_43_12_1 j hj hq

theorem leaf_43_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 43 []).length)
    (hq : (normIsRep.getD 43 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨43, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨43, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨43, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨43, by decide⟩ (listedAt ⟨43, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T43_12
      hfix43_12 hinj43_12 hcardT43_12
      (fun i => conj_mem_of_fixedPoints _ _ (T43_12 i) (hfix43_12 i) _)
      ⟨43, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨43, by decide⟩ (Q2.listedAt ⟨43, by decide⟩
        (alnCheck_rep ⟨43, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T43_12_2 Q2.hfix43_12_2 Q2.hinj43_12_2
      Q2.hcardT43_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T43_12_2 i) (Q2.hfix43_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨43, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T43_12 = colFn colCert_43_12_2.D (m := 125) from colCert_43_12_2.bind1,
    show colData2 (⟨43, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T43_12_2 = colFn colCert_43_12_2.D (m := 125) from colCert_43_12_2.bind2]
  exact alnAll_43_12_2 j hj hq

theorem leaf_43_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 43 []).length)
    (hq : (normIsRep.getD 43 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨43, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨43, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨43, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨43, by decide⟩ (listedAt ⟨43, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T43_12
      hfix43_12 hinj43_12 hcardT43_12
      (fun i => conj_mem_of_fixedPoints _ _ (T43_12 i) (hfix43_12 i) _)
      ⟨43, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨43, by decide⟩ (Q2.listedAt ⟨43, by decide⟩
        (alnCheck_rep ⟨43, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T43_12_2 Q2.hfix43_12_2 Q2.hinj43_12_2
      Q2.hcardT43_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T43_12_2 i) (Q2.hfix43_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨43, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T43_12 = colFn colCert_43_12_3.D (m := 125) from colCert_43_12_3.bind1,
    show colData2 (⟨43, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T43_12_2 = colFn colCert_43_12_3.D (m := 125) from colCert_43_12_3.bind2]
  exact alnAll_43_12_3 j hj hq

theorem leaf_43_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 43 []).length)
    (hq : (normIsRep.getD 43 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨43, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨43, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨43, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨43, by decide⟩ (listedAt ⟨43, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T43_12
      hfix43_12 hinj43_12 hcardT43_12
      (fun i => conj_mem_of_fixedPoints _ _ (T43_12 i) (hfix43_12 i) _)
      ⟨43, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨43, by decide⟩ (Q2.listedAt ⟨43, by decide⟩
        (alnCheck_rep ⟨43, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T43_12_2 Q2.hfix43_12_2 Q2.hinj43_12_2
      Q2.hcardT43_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T43_12_2 i) (Q2.hfix43_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨43, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T43_12 = colFn colCert_43_12_4.D (m := 125) from colCert_43_12_4.bind1,
    show colData2 (⟨43, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T43_12_2 = colFn colCert_43_12_4.D (m := 125) from colCert_43_12_4.bind2]
  exact alnAll_43_12_4 j hj hq

theorem leaf_43_43_0 (hp : 0 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 43 []).length)
    (hq : (normIsRep.getD 43 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 0 hp)
        (rowE2 (⟨43, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp))
        (rowE1 (⟨43, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨43, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨43, by decide⟩ (listedAt ⟨43, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp)) T43_43
      hfix43_43 hinj43_43 hcardT43_43
      (fun i => conj_mem_of_fixedPoints _ _ (T43_43 i) (hfix43_43 i) _)
      ⟨43, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨43, by decide⟩ (Q2.listedAt ⟨43, by decide⟩
        (alnCheck_rep ⟨43, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 0 hp) Q2.T43_43_2 Q2.hfix43_43_2 Q2.hinj43_43_2
      Q2.hcardT43_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T43_43_2 i) (Q2.hfix43_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨43, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T43_43 = colFn colCert_43_43_0.D (m := 25) from colCert_43_43_0.bind1,
    show colData2 (⟨43, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 0 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T43_43_2 = colFn colCert_43_43_0.D (m := 25) from colCert_43_43_0.bind2]
  exact alnAll_43_43_0 j hj hq

theorem leaf_43_43_1 (hp : 1 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 43 []).length)
    (hq : (normIsRep.getD 43 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 1 hp)
        (rowE2 (⟨43, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp))
        (rowE1 (⟨43, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨43, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨43, by decide⟩ (listedAt ⟨43, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp)) T43_43
      hfix43_43 hinj43_43 hcardT43_43
      (fun i => conj_mem_of_fixedPoints _ _ (T43_43 i) (hfix43_43 i) _)
      ⟨43, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨43, by decide⟩ (Q2.listedAt ⟨43, by decide⟩
        (alnCheck_rep ⟨43, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 1 hp) Q2.T43_43_2 Q2.hfix43_43_2 Q2.hinj43_43_2
      Q2.hcardT43_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T43_43_2 i) (Q2.hfix43_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨43, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T43_43 = colFn colCert_43_43_1.D (m := 25) from colCert_43_43_1.bind1,
    show colData2 (⟨43, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 1 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T43_43_2 = colFn colCert_43_43_1.D (m := 25) from colCert_43_43_1.bind2]
  exact alnAll_43_43_1 j hj hq

theorem leaf_43_43_2 (hp : 2 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 43 []).length)
    (hq : (normIsRep.getD 43 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 2 hp)
        (rowE2 (⟨43, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp))
        (rowE1 (⟨43, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨43, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨43, by decide⟩ (listedAt ⟨43, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp)) T43_43
      hfix43_43 hinj43_43 hcardT43_43
      (fun i => conj_mem_of_fixedPoints _ _ (T43_43 i) (hfix43_43 i) _)
      ⟨43, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨43, by decide⟩ (Q2.listedAt ⟨43, by decide⟩
        (alnCheck_rep ⟨43, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 2 hp) Q2.T43_43_2 Q2.hfix43_43_2 Q2.hinj43_43_2
      Q2.hcardT43_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T43_43_2 i) (Q2.hfix43_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨43, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T43_43 = colFn colCert_43_43_2.D (m := 25) from colCert_43_43_2.bind1,
    show colData2 (⟨43, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 2 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T43_43_2 = colFn colCert_43_43_2.D (m := 25) from colCert_43_43_2.bind2]
  exact alnAll_43_43_2 j hj hq

theorem leaf_43_43_3 (hp : 3 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 43 []).length)
    (hq : (normIsRep.getD 43 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 3 hp)
        (rowE2 (⟨43, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp))
        (rowE1 (⟨43, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨43, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨43, by decide⟩ (listedAt ⟨43, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp)) T43_43
      hfix43_43 hinj43_43 hcardT43_43
      (fun i => conj_mem_of_fixedPoints _ _ (T43_43 i) (hfix43_43 i) _)
      ⟨43, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨43, by decide⟩ (Q2.listedAt ⟨43, by decide⟩
        (alnCheck_rep ⟨43, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 3 hp) Q2.T43_43_2 Q2.hfix43_43_2 Q2.hinj43_43_2
      Q2.hcardT43_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T43_43_2 i) (Q2.hfix43_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨43, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T43_43 = colFn colCert_43_43_3.D (m := 25) from colCert_43_43_3.bind1,
    show colData2 (⟨43, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 3 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T43_43_2 = colFn colCert_43_43_3.D (m := 25) from colCert_43_43_3.bind2]
  exact alnAll_43_43_3 j hj hq

theorem leaf_43_43_4 (hp : 4 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 43 []).length)
    (hq : (normIsRep.getD 43 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 4 hp)
        (rowE2 (⟨43, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp))
        (rowE1 (⟨43, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨43, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨43, by decide⟩ (listedAt ⟨43, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp)) T43_43
      hfix43_43 hinj43_43 hcardT43_43
      (fun i => conj_mem_of_fixedPoints _ _ (T43_43 i) (hfix43_43 i) _)
      ⟨43, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨43, by decide⟩ (Q2.listedAt ⟨43, by decide⟩
        (alnCheck_rep ⟨43, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 4 hp) Q2.T43_43_2 Q2.hfix43_43_2 Q2.hinj43_43_2
      Q2.hcardT43_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T43_43_2 i) (Q2.hfix43_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨43, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T43_43 = colFn colCert_43_43_4.D (m := 25) from colCert_43_43_4.bind1,
    show colData2 (⟨43, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 4 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T43_43_2 = colFn colCert_43_43_4.D (m := 25) from colCert_43_43_4.bind2]
  exact alnAll_43_43_4 j hj hq

theorem leaf_43_43_5 (hp : 5 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 43 []).length)
    (hq : (normIsRep.getD 43 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 5 hp)
        (rowE2 (⟨43, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp))
        (rowE1 (⟨43, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨43, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨43, by decide⟩ (listedAt ⟨43, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp)) T43_43
      hfix43_43 hinj43_43 hcardT43_43
      (fun i => conj_mem_of_fixedPoints _ _ (T43_43 i) (hfix43_43 i) _)
      ⟨43, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨43, by decide⟩ (Q2.listedAt ⟨43, by decide⟩
        (alnCheck_rep ⟨43, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 5 hp) Q2.T43_43_2 Q2.hfix43_43_2 Q2.hinj43_43_2
      Q2.hcardT43_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T43_43_2 i) (Q2.hfix43_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨43, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T43_43 = colFn colCert_43_43_5.D (m := 25) from colCert_43_43_5.bind1,
    show colData2 (⟨43, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 5 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T43_43_2 = colFn colCert_43_43_5.D (m := 25) from colCert_43_43_5.bind2]
  exact alnAll_43_43_5 j hj hq

theorem leaf_43_43_10 (hp : 10 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 43 []).length)
    (hq : (normIsRep.getD 43 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 10 hp)
        (rowE2 (⟨43, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp))
        (rowE1 (⟨43, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨43, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨43, by decide⟩ (listedAt ⟨43, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp)) T43_43
      hfix43_43 hinj43_43 hcardT43_43
      (fun i => conj_mem_of_fixedPoints _ _ (T43_43 i) (hfix43_43 i) _)
      ⟨43, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨43, by decide⟩ (Q2.listedAt ⟨43, by decide⟩
        (alnCheck_rep ⟨43, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 10 hp) Q2.T43_43_2 Q2.hfix43_43_2 Q2.hinj43_43_2
      Q2.hcardT43_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T43_43_2 i) (Q2.hfix43_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨43, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T43_43 = colFn colCert_43_43_10.D (m := 25) from colCert_43_43_10.bind1,
    show colData2 (⟨43, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 10 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T43_43_2 = colFn colCert_43_43_10.D (m := 25) from colCert_43_43_10.bind2]
  exact alnAll_43_43_10 j hj hq

theorem leaf_43_43_15 (hp : 15 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 43 []).length)
    (hq : (normIsRep.getD 43 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 15 hp)
        (rowE2 (⟨43, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp))
        (rowE1 (⟨43, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨43, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨43, by decide⟩ (listedAt ⟨43, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp)) T43_43
      hfix43_43 hinj43_43 hcardT43_43
      (fun i => conj_mem_of_fixedPoints _ _ (T43_43 i) (hfix43_43 i) _)
      ⟨43, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨43, by decide⟩ (Q2.listedAt ⟨43, by decide⟩
        (alnCheck_rep ⟨43, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 15 hp) Q2.T43_43_2 Q2.hfix43_43_2 Q2.hinj43_43_2
      Q2.hcardT43_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T43_43_2 i) (Q2.hfix43_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨43, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T43_43 = colFn colCert_43_43_15.D (m := 25) from colCert_43_43_15.bind1,
    show colData2 (⟨43, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 15 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T43_43_2 = colFn colCert_43_43_15.D (m := 25) from colCert_43_43_15.bind2]
  exact alnAll_43_43_15 j hj hq

theorem leaf_43_43_20 (hp : 20 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 43 []).length)
    (hq : (normIsRep.getD 43 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 20 hp)
        (rowE2 (⟨43, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp))
        (rowE1 (⟨43, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨43, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨43, by decide⟩ (listedAt ⟨43, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp)) T43_43
      hfix43_43 hinj43_43 hcardT43_43
      (fun i => conj_mem_of_fixedPoints _ _ (T43_43 i) (hfix43_43 i) _)
      ⟨43, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨43, by decide⟩ (Q2.listedAt ⟨43, by decide⟩
        (alnCheck_rep ⟨43, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 20 hp) Q2.T43_43_2 Q2.hfix43_43_2 Q2.hinj43_43_2
      Q2.hcardT43_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T43_43_2 i) (Q2.hfix43_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨43, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T43_43 = colFn colCert_43_43_20.D (m := 25) from colCert_43_43_20.bind1,
    show colData2 (⟨43, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 20 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T43_43_2 = colFn colCert_43_43_20.D (m := 25) from colCert_43_43_20.bind2]
  exact alnAll_43_43_20 j hj hq

theorem leaf_44_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 44 []).length)
    (hq : (normIsRep.getD 44 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨44, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨44, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨44, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨44, by decide⟩ (listedAt ⟨44, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T44_12
      hfix44_12 hinj44_12 hcardT44_12
      (fun i => conj_mem_of_fixedPoints _ _ (T44_12 i) (hfix44_12 i) _)
      ⟨44, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨44, by decide⟩ (Q2.listedAt ⟨44, by decide⟩
        (alnCheck_rep ⟨44, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T44_12_2 Q2.hfix44_12_2 Q2.hinj44_12_2
      Q2.hcardT44_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T44_12_2 i) (Q2.hfix44_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨44, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T44_12 = colFn colCert_44_12_0.D (m := 125) from colCert_44_12_0.bind1,
    show colData2 (⟨44, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T44_12_2 = colFn colCert_44_12_0.D (m := 125) from colCert_44_12_0.bind2]
  exact alnAll_44_12_0 j hj hq

theorem leaf_44_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 44 []).length)
    (hq : (normIsRep.getD 44 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨44, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨44, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨44, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨44, by decide⟩ (listedAt ⟨44, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T44_12
      hfix44_12 hinj44_12 hcardT44_12
      (fun i => conj_mem_of_fixedPoints _ _ (T44_12 i) (hfix44_12 i) _)
      ⟨44, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨44, by decide⟩ (Q2.listedAt ⟨44, by decide⟩
        (alnCheck_rep ⟨44, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T44_12_2 Q2.hfix44_12_2 Q2.hinj44_12_2
      Q2.hcardT44_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T44_12_2 i) (Q2.hfix44_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨44, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T44_12 = colFn colCert_44_12_1.D (m := 125) from colCert_44_12_1.bind1,
    show colData2 (⟨44, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T44_12_2 = colFn colCert_44_12_1.D (m := 125) from colCert_44_12_1.bind2]
  exact alnAll_44_12_1 j hj hq

theorem leaf_44_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 44 []).length)
    (hq : (normIsRep.getD 44 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨44, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨44, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨44, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨44, by decide⟩ (listedAt ⟨44, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T44_12
      hfix44_12 hinj44_12 hcardT44_12
      (fun i => conj_mem_of_fixedPoints _ _ (T44_12 i) (hfix44_12 i) _)
      ⟨44, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨44, by decide⟩ (Q2.listedAt ⟨44, by decide⟩
        (alnCheck_rep ⟨44, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T44_12_2 Q2.hfix44_12_2 Q2.hinj44_12_2
      Q2.hcardT44_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T44_12_2 i) (Q2.hfix44_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨44, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T44_12 = colFn colCert_44_12_2.D (m := 125) from colCert_44_12_2.bind1,
    show colData2 (⟨44, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T44_12_2 = colFn colCert_44_12_2.D (m := 125) from colCert_44_12_2.bind2]
  exact alnAll_44_12_2 j hj hq

theorem leaf_44_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 44 []).length)
    (hq : (normIsRep.getD 44 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨44, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨44, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨44, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨44, by decide⟩ (listedAt ⟨44, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T44_12
      hfix44_12 hinj44_12 hcardT44_12
      (fun i => conj_mem_of_fixedPoints _ _ (T44_12 i) (hfix44_12 i) _)
      ⟨44, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨44, by decide⟩ (Q2.listedAt ⟨44, by decide⟩
        (alnCheck_rep ⟨44, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T44_12_2 Q2.hfix44_12_2 Q2.hinj44_12_2
      Q2.hcardT44_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T44_12_2 i) (Q2.hfix44_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨44, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T44_12 = colFn colCert_44_12_3.D (m := 125) from colCert_44_12_3.bind1,
    show colData2 (⟨44, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T44_12_2 = colFn colCert_44_12_3.D (m := 125) from colCert_44_12_3.bind2]
  exact alnAll_44_12_3 j hj hq

theorem leaf_44_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 44 []).length)
    (hq : (normIsRep.getD 44 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨44, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨44, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨44, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨44, by decide⟩ (listedAt ⟨44, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T44_12
      hfix44_12 hinj44_12 hcardT44_12
      (fun i => conj_mem_of_fixedPoints _ _ (T44_12 i) (hfix44_12 i) _)
      ⟨44, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨44, by decide⟩ (Q2.listedAt ⟨44, by decide⟩
        (alnCheck_rep ⟨44, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T44_12_2 Q2.hfix44_12_2 Q2.hinj44_12_2
      Q2.hcardT44_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T44_12_2 i) (Q2.hfix44_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨44, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T44_12 = colFn colCert_44_12_4.D (m := 125) from colCert_44_12_4.bind1,
    show colData2 (⟨44, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T44_12_2 = colFn colCert_44_12_4.D (m := 125) from colCert_44_12_4.bind2]
  exact alnAll_44_12_4 j hj hq

theorem leaf_44_44_0 (hp : 0 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 44 []).length)
    (hq : (normIsRep.getD 44 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 0 hp)
        (rowE2 (⟨44, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp))
        (rowE1 (⟨44, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨44, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨44, by decide⟩ (listedAt ⟨44, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp)) T44_44
      hfix44_44 hinj44_44 hcardT44_44
      (fun i => conj_mem_of_fixedPoints _ _ (T44_44 i) (hfix44_44 i) _)
      ⟨44, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨44, by decide⟩ (Q2.listedAt ⟨44, by decide⟩
        (alnCheck_rep ⟨44, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 0 hp) Q2.T44_44_2 Q2.hfix44_44_2 Q2.hinj44_44_2
      Q2.hcardT44_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T44_44_2 i) (Q2.hfix44_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨44, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T44_44 = colFn colCert_44_44_0.D (m := 25) from colCert_44_44_0.bind1,
    show colData2 (⟨44, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 0 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T44_44_2 = colFn colCert_44_44_0.D (m := 25) from colCert_44_44_0.bind2]
  exact alnAll_44_44_0 j hj hq

theorem leaf_44_44_1 (hp : 1 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 44 []).length)
    (hq : (normIsRep.getD 44 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 1 hp)
        (rowE2 (⟨44, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp))
        (rowE1 (⟨44, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨44, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨44, by decide⟩ (listedAt ⟨44, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp)) T44_44
      hfix44_44 hinj44_44 hcardT44_44
      (fun i => conj_mem_of_fixedPoints _ _ (T44_44 i) (hfix44_44 i) _)
      ⟨44, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨44, by decide⟩ (Q2.listedAt ⟨44, by decide⟩
        (alnCheck_rep ⟨44, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 1 hp) Q2.T44_44_2 Q2.hfix44_44_2 Q2.hinj44_44_2
      Q2.hcardT44_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T44_44_2 i) (Q2.hfix44_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨44, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T44_44 = colFn colCert_44_44_1.D (m := 25) from colCert_44_44_1.bind1,
    show colData2 (⟨44, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 1 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T44_44_2 = colFn colCert_44_44_1.D (m := 25) from colCert_44_44_1.bind2]
  exact alnAll_44_44_1 j hj hq

theorem leaf_44_44_2 (hp : 2 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 44 []).length)
    (hq : (normIsRep.getD 44 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 2 hp)
        (rowE2 (⟨44, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp))
        (rowE1 (⟨44, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨44, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨44, by decide⟩ (listedAt ⟨44, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp)) T44_44
      hfix44_44 hinj44_44 hcardT44_44
      (fun i => conj_mem_of_fixedPoints _ _ (T44_44 i) (hfix44_44 i) _)
      ⟨44, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨44, by decide⟩ (Q2.listedAt ⟨44, by decide⟩
        (alnCheck_rep ⟨44, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 2 hp) Q2.T44_44_2 Q2.hfix44_44_2 Q2.hinj44_44_2
      Q2.hcardT44_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T44_44_2 i) (Q2.hfix44_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨44, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T44_44 = colFn colCert_44_44_2.D (m := 25) from colCert_44_44_2.bind1,
    show colData2 (⟨44, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 2 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T44_44_2 = colFn colCert_44_44_2.D (m := 25) from colCert_44_44_2.bind2]
  exact alnAll_44_44_2 j hj hq

theorem leaf_44_44_3 (hp : 3 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 44 []).length)
    (hq : (normIsRep.getD 44 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 3 hp)
        (rowE2 (⟨44, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp))
        (rowE1 (⟨44, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨44, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨44, by decide⟩ (listedAt ⟨44, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp)) T44_44
      hfix44_44 hinj44_44 hcardT44_44
      (fun i => conj_mem_of_fixedPoints _ _ (T44_44 i) (hfix44_44 i) _)
      ⟨44, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨44, by decide⟩ (Q2.listedAt ⟨44, by decide⟩
        (alnCheck_rep ⟨44, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 3 hp) Q2.T44_44_2 Q2.hfix44_44_2 Q2.hinj44_44_2
      Q2.hcardT44_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T44_44_2 i) (Q2.hfix44_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨44, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T44_44 = colFn colCert_44_44_3.D (m := 25) from colCert_44_44_3.bind1,
    show colData2 (⟨44, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 3 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T44_44_2 = colFn colCert_44_44_3.D (m := 25) from colCert_44_44_3.bind2]
  exact alnAll_44_44_3 j hj hq

theorem leaf_44_44_4 (hp : 4 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 44 []).length)
    (hq : (normIsRep.getD 44 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 4 hp)
        (rowE2 (⟨44, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp))
        (rowE1 (⟨44, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨44, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨44, by decide⟩ (listedAt ⟨44, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp)) T44_44
      hfix44_44 hinj44_44 hcardT44_44
      (fun i => conj_mem_of_fixedPoints _ _ (T44_44 i) (hfix44_44 i) _)
      ⟨44, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨44, by decide⟩ (Q2.listedAt ⟨44, by decide⟩
        (alnCheck_rep ⟨44, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 4 hp) Q2.T44_44_2 Q2.hfix44_44_2 Q2.hinj44_44_2
      Q2.hcardT44_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T44_44_2 i) (Q2.hfix44_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨44, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T44_44 = colFn colCert_44_44_4.D (m := 25) from colCert_44_44_4.bind1,
    show colData2 (⟨44, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 4 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T44_44_2 = colFn colCert_44_44_4.D (m := 25) from colCert_44_44_4.bind2]
  exact alnAll_44_44_4 j hj hq

theorem leaf_44_44_5 (hp : 5 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 44 []).length)
    (hq : (normIsRep.getD 44 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 5 hp)
        (rowE2 (⟨44, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp))
        (rowE1 (⟨44, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨44, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨44, by decide⟩ (listedAt ⟨44, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp)) T44_44
      hfix44_44 hinj44_44 hcardT44_44
      (fun i => conj_mem_of_fixedPoints _ _ (T44_44 i) (hfix44_44 i) _)
      ⟨44, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨44, by decide⟩ (Q2.listedAt ⟨44, by decide⟩
        (alnCheck_rep ⟨44, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 5 hp) Q2.T44_44_2 Q2.hfix44_44_2 Q2.hinj44_44_2
      Q2.hcardT44_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T44_44_2 i) (Q2.hfix44_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨44, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T44_44 = colFn colCert_44_44_5.D (m := 25) from colCert_44_44_5.bind1,
    show colData2 (⟨44, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 5 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T44_44_2 = colFn colCert_44_44_5.D (m := 25) from colCert_44_44_5.bind2]
  exact alnAll_44_44_5 j hj hq

theorem leaf_44_44_10 (hp : 10 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 44 []).length)
    (hq : (normIsRep.getD 44 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 10 hp)
        (rowE2 (⟨44, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp))
        (rowE1 (⟨44, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨44, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨44, by decide⟩ (listedAt ⟨44, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp)) T44_44
      hfix44_44 hinj44_44 hcardT44_44
      (fun i => conj_mem_of_fixedPoints _ _ (T44_44 i) (hfix44_44 i) _)
      ⟨44, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨44, by decide⟩ (Q2.listedAt ⟨44, by decide⟩
        (alnCheck_rep ⟨44, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 10 hp) Q2.T44_44_2 Q2.hfix44_44_2 Q2.hinj44_44_2
      Q2.hcardT44_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T44_44_2 i) (Q2.hfix44_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨44, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T44_44 = colFn colCert_44_44_10.D (m := 25) from colCert_44_44_10.bind1,
    show colData2 (⟨44, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 10 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T44_44_2 = colFn colCert_44_44_10.D (m := 25) from colCert_44_44_10.bind2]
  exact alnAll_44_44_10 j hj hq

theorem leaf_44_44_15 (hp : 15 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 44 []).length)
    (hq : (normIsRep.getD 44 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 15 hp)
        (rowE2 (⟨44, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp))
        (rowE1 (⟨44, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨44, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨44, by decide⟩ (listedAt ⟨44, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp)) T44_44
      hfix44_44 hinj44_44 hcardT44_44
      (fun i => conj_mem_of_fixedPoints _ _ (T44_44 i) (hfix44_44 i) _)
      ⟨44, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨44, by decide⟩ (Q2.listedAt ⟨44, by decide⟩
        (alnCheck_rep ⟨44, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 15 hp) Q2.T44_44_2 Q2.hfix44_44_2 Q2.hinj44_44_2
      Q2.hcardT44_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T44_44_2 i) (Q2.hfix44_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨44, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T44_44 = colFn colCert_44_44_15.D (m := 25) from colCert_44_44_15.bind1,
    show colData2 (⟨44, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 15 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T44_44_2 = colFn colCert_44_44_15.D (m := 25) from colCert_44_44_15.bind2]
  exact alnAll_44_44_15 j hj hq

theorem leaf_44_44_20 (hp : 20 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 44 []).length)
    (hq : (normIsRep.getD 44 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 20 hp)
        (rowE2 (⟨44, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp))
        (rowE1 (⟨44, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨44, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨44, by decide⟩ (listedAt ⟨44, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp)) T44_44
      hfix44_44 hinj44_44 hcardT44_44
      (fun i => conj_mem_of_fixedPoints _ _ (T44_44 i) (hfix44_44 i) _)
      ⟨44, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨44, by decide⟩ (Q2.listedAt ⟨44, by decide⟩
        (alnCheck_rep ⟨44, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 20 hp) Q2.T44_44_2 Q2.hfix44_44_2 Q2.hinj44_44_2
      Q2.hcardT44_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T44_44_2 i) (Q2.hfix44_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨44, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T44_44 = colFn colCert_44_44_20.D (m := 25) from colCert_44_44_20.bind1,
    show colData2 (⟨44, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 20 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T44_44_2 = colFn colCert_44_44_20.D (m := 25) from colCert_44_44_20.bind2]
  exact alnAll_44_44_20 j hj hq

theorem leaf_45_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 45 []).length)
    (hq : (normIsRep.getD 45 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨45, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨45, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨45, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨45, by decide⟩ (listedAt ⟨45, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T45_12
      hfix45_12 hinj45_12 hcardT45_12
      (fun i => conj_mem_of_fixedPoints _ _ (T45_12 i) (hfix45_12 i) _)
      ⟨45, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨45, by decide⟩ (Q2.listedAt ⟨45, by decide⟩
        (alnCheck_rep ⟨45, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T45_12_2 Q2.hfix45_12_2 Q2.hinj45_12_2
      Q2.hcardT45_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T45_12_2 i) (Q2.hfix45_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨45, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T45_12 = colFn colCert_45_12_0.D (m := 125) from colCert_45_12_0.bind1,
    show colData2 (⟨45, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T45_12_2 = colFn colCert_45_12_0.D (m := 125) from colCert_45_12_0.bind2]
  exact alnAll_45_12_0 j hj hq

theorem leaf_45_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 45 []).length)
    (hq : (normIsRep.getD 45 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨45, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨45, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨45, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨45, by decide⟩ (listedAt ⟨45, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T45_12
      hfix45_12 hinj45_12 hcardT45_12
      (fun i => conj_mem_of_fixedPoints _ _ (T45_12 i) (hfix45_12 i) _)
      ⟨45, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨45, by decide⟩ (Q2.listedAt ⟨45, by decide⟩
        (alnCheck_rep ⟨45, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T45_12_2 Q2.hfix45_12_2 Q2.hinj45_12_2
      Q2.hcardT45_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T45_12_2 i) (Q2.hfix45_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨45, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T45_12 = colFn colCert_45_12_1.D (m := 125) from colCert_45_12_1.bind1,
    show colData2 (⟨45, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T45_12_2 = colFn colCert_45_12_1.D (m := 125) from colCert_45_12_1.bind2]
  exact alnAll_45_12_1 j hj hq

theorem leaf_45_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 45 []).length)
    (hq : (normIsRep.getD 45 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨45, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨45, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨45, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨45, by decide⟩ (listedAt ⟨45, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T45_12
      hfix45_12 hinj45_12 hcardT45_12
      (fun i => conj_mem_of_fixedPoints _ _ (T45_12 i) (hfix45_12 i) _)
      ⟨45, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨45, by decide⟩ (Q2.listedAt ⟨45, by decide⟩
        (alnCheck_rep ⟨45, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T45_12_2 Q2.hfix45_12_2 Q2.hinj45_12_2
      Q2.hcardT45_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T45_12_2 i) (Q2.hfix45_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨45, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T45_12 = colFn colCert_45_12_2.D (m := 125) from colCert_45_12_2.bind1,
    show colData2 (⟨45, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T45_12_2 = colFn colCert_45_12_2.D (m := 125) from colCert_45_12_2.bind2]
  exact alnAll_45_12_2 j hj hq

theorem leaf_45_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 45 []).length)
    (hq : (normIsRep.getD 45 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨45, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨45, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨45, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨45, by decide⟩ (listedAt ⟨45, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T45_12
      hfix45_12 hinj45_12 hcardT45_12
      (fun i => conj_mem_of_fixedPoints _ _ (T45_12 i) (hfix45_12 i) _)
      ⟨45, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨45, by decide⟩ (Q2.listedAt ⟨45, by decide⟩
        (alnCheck_rep ⟨45, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T45_12_2 Q2.hfix45_12_2 Q2.hinj45_12_2
      Q2.hcardT45_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T45_12_2 i) (Q2.hfix45_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨45, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T45_12 = colFn colCert_45_12_3.D (m := 125) from colCert_45_12_3.bind1,
    show colData2 (⟨45, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T45_12_2 = colFn colCert_45_12_3.D (m := 125) from colCert_45_12_3.bind2]
  exact alnAll_45_12_3 j hj hq

theorem leaf_45_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 45 []).length)
    (hq : (normIsRep.getD 45 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨45, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨45, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨45, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨45, by decide⟩ (listedAt ⟨45, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T45_12
      hfix45_12 hinj45_12 hcardT45_12
      (fun i => conj_mem_of_fixedPoints _ _ (T45_12 i) (hfix45_12 i) _)
      ⟨45, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨45, by decide⟩ (Q2.listedAt ⟨45, by decide⟩
        (alnCheck_rep ⟨45, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T45_12_2 Q2.hfix45_12_2 Q2.hinj45_12_2
      Q2.hcardT45_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T45_12_2 i) (Q2.hfix45_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨45, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T45_12 = colFn colCert_45_12_4.D (m := 125) from colCert_45_12_4.bind1,
    show colData2 (⟨45, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T45_12_2 = colFn colCert_45_12_4.D (m := 125) from colCert_45_12_4.bind2]
  exact alnAll_45_12_4 j hj hq

theorem leaf_45_45_0 (hp : 0 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 45 []).length)
    (hq : (normIsRep.getD 45 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 0 hp)
        (rowE2 (⟨45, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp))
        (rowE1 (⟨45, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨45, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨45, by decide⟩ (listedAt ⟨45, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp)) T45_45
      hfix45_45 hinj45_45 hcardT45_45
      (fun i => conj_mem_of_fixedPoints _ _ (T45_45 i) (hfix45_45 i) _)
      ⟨45, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨45, by decide⟩ (Q2.listedAt ⟨45, by decide⟩
        (alnCheck_rep ⟨45, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 0 hp) Q2.T45_45_2 Q2.hfix45_45_2 Q2.hinj45_45_2
      Q2.hcardT45_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T45_45_2 i) (Q2.hfix45_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨45, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T45_45 = colFn colCert_45_45_0.D (m := 25) from colCert_45_45_0.bind1,
    show colData2 (⟨45, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 0 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T45_45_2 = colFn colCert_45_45_0.D (m := 25) from colCert_45_45_0.bind2]
  exact alnAll_45_45_0 j hj hq

theorem leaf_45_45_1 (hp : 1 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 45 []).length)
    (hq : (normIsRep.getD 45 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 1 hp)
        (rowE2 (⟨45, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp))
        (rowE1 (⟨45, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨45, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨45, by decide⟩ (listedAt ⟨45, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp)) T45_45
      hfix45_45 hinj45_45 hcardT45_45
      (fun i => conj_mem_of_fixedPoints _ _ (T45_45 i) (hfix45_45 i) _)
      ⟨45, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨45, by decide⟩ (Q2.listedAt ⟨45, by decide⟩
        (alnCheck_rep ⟨45, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 1 hp) Q2.T45_45_2 Q2.hfix45_45_2 Q2.hinj45_45_2
      Q2.hcardT45_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T45_45_2 i) (Q2.hfix45_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨45, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T45_45 = colFn colCert_45_45_1.D (m := 25) from colCert_45_45_1.bind1,
    show colData2 (⟨45, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 1 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T45_45_2 = colFn colCert_45_45_1.D (m := 25) from colCert_45_45_1.bind2]
  exact alnAll_45_45_1 j hj hq

theorem leaf_45_45_2 (hp : 2 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 45 []).length)
    (hq : (normIsRep.getD 45 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 2 hp)
        (rowE2 (⟨45, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp))
        (rowE1 (⟨45, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨45, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨45, by decide⟩ (listedAt ⟨45, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp)) T45_45
      hfix45_45 hinj45_45 hcardT45_45
      (fun i => conj_mem_of_fixedPoints _ _ (T45_45 i) (hfix45_45 i) _)
      ⟨45, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨45, by decide⟩ (Q2.listedAt ⟨45, by decide⟩
        (alnCheck_rep ⟨45, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 2 hp) Q2.T45_45_2 Q2.hfix45_45_2 Q2.hinj45_45_2
      Q2.hcardT45_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T45_45_2 i) (Q2.hfix45_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨45, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T45_45 = colFn colCert_45_45_2.D (m := 25) from colCert_45_45_2.bind1,
    show colData2 (⟨45, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 2 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T45_45_2 = colFn colCert_45_45_2.D (m := 25) from colCert_45_45_2.bind2]
  exact alnAll_45_45_2 j hj hq

theorem leaf_45_45_3 (hp : 3 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 45 []).length)
    (hq : (normIsRep.getD 45 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 3 hp)
        (rowE2 (⟨45, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp))
        (rowE1 (⟨45, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨45, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨45, by decide⟩ (listedAt ⟨45, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp)) T45_45
      hfix45_45 hinj45_45 hcardT45_45
      (fun i => conj_mem_of_fixedPoints _ _ (T45_45 i) (hfix45_45 i) _)
      ⟨45, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨45, by decide⟩ (Q2.listedAt ⟨45, by decide⟩
        (alnCheck_rep ⟨45, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 3 hp) Q2.T45_45_2 Q2.hfix45_45_2 Q2.hinj45_45_2
      Q2.hcardT45_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T45_45_2 i) (Q2.hfix45_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨45, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T45_45 = colFn colCert_45_45_3.D (m := 25) from colCert_45_45_3.bind1,
    show colData2 (⟨45, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 3 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T45_45_2 = colFn colCert_45_45_3.D (m := 25) from colCert_45_45_3.bind2]
  exact alnAll_45_45_3 j hj hq

theorem leaf_45_45_4 (hp : 4 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 45 []).length)
    (hq : (normIsRep.getD 45 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 4 hp)
        (rowE2 (⟨45, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp))
        (rowE1 (⟨45, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨45, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨45, by decide⟩ (listedAt ⟨45, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp)) T45_45
      hfix45_45 hinj45_45 hcardT45_45
      (fun i => conj_mem_of_fixedPoints _ _ (T45_45 i) (hfix45_45 i) _)
      ⟨45, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨45, by decide⟩ (Q2.listedAt ⟨45, by decide⟩
        (alnCheck_rep ⟨45, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 4 hp) Q2.T45_45_2 Q2.hfix45_45_2 Q2.hinj45_45_2
      Q2.hcardT45_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T45_45_2 i) (Q2.hfix45_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨45, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T45_45 = colFn colCert_45_45_4.D (m := 25) from colCert_45_45_4.bind1,
    show colData2 (⟨45, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 4 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T45_45_2 = colFn colCert_45_45_4.D (m := 25) from colCert_45_45_4.bind2]
  exact alnAll_45_45_4 j hj hq

theorem leaf_45_45_5 (hp : 5 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 45 []).length)
    (hq : (normIsRep.getD 45 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 5 hp)
        (rowE2 (⟨45, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp))
        (rowE1 (⟨45, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨45, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨45, by decide⟩ (listedAt ⟨45, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp)) T45_45
      hfix45_45 hinj45_45 hcardT45_45
      (fun i => conj_mem_of_fixedPoints _ _ (T45_45 i) (hfix45_45 i) _)
      ⟨45, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨45, by decide⟩ (Q2.listedAt ⟨45, by decide⟩
        (alnCheck_rep ⟨45, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 5 hp) Q2.T45_45_2 Q2.hfix45_45_2 Q2.hinj45_45_2
      Q2.hcardT45_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T45_45_2 i) (Q2.hfix45_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨45, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T45_45 = colFn colCert_45_45_5.D (m := 25) from colCert_45_45_5.bind1,
    show colData2 (⟨45, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 5 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T45_45_2 = colFn colCert_45_45_5.D (m := 25) from colCert_45_45_5.bind2]
  exact alnAll_45_45_5 j hj hq

theorem leaf_45_45_10 (hp : 10 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 45 []).length)
    (hq : (normIsRep.getD 45 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 10 hp)
        (rowE2 (⟨45, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp))
        (rowE1 (⟨45, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨45, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨45, by decide⟩ (listedAt ⟨45, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp)) T45_45
      hfix45_45 hinj45_45 hcardT45_45
      (fun i => conj_mem_of_fixedPoints _ _ (T45_45 i) (hfix45_45 i) _)
      ⟨45, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨45, by decide⟩ (Q2.listedAt ⟨45, by decide⟩
        (alnCheck_rep ⟨45, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 10 hp) Q2.T45_45_2 Q2.hfix45_45_2 Q2.hinj45_45_2
      Q2.hcardT45_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T45_45_2 i) (Q2.hfix45_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨45, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T45_45 = colFn colCert_45_45_10.D (m := 25) from colCert_45_45_10.bind1,
    show colData2 (⟨45, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 10 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T45_45_2 = colFn colCert_45_45_10.D (m := 25) from colCert_45_45_10.bind2]
  exact alnAll_45_45_10 j hj hq

theorem leaf_45_45_15 (hp : 15 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 45 []).length)
    (hq : (normIsRep.getD 45 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 15 hp)
        (rowE2 (⟨45, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp))
        (rowE1 (⟨45, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨45, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨45, by decide⟩ (listedAt ⟨45, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp)) T45_45
      hfix45_45 hinj45_45 hcardT45_45
      (fun i => conj_mem_of_fixedPoints _ _ (T45_45 i) (hfix45_45 i) _)
      ⟨45, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨45, by decide⟩ (Q2.listedAt ⟨45, by decide⟩
        (alnCheck_rep ⟨45, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 15 hp) Q2.T45_45_2 Q2.hfix45_45_2 Q2.hinj45_45_2
      Q2.hcardT45_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T45_45_2 i) (Q2.hfix45_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨45, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T45_45 = colFn colCert_45_45_15.D (m := 25) from colCert_45_45_15.bind1,
    show colData2 (⟨45, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 15 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T45_45_2 = colFn colCert_45_45_15.D (m := 25) from colCert_45_45_15.bind2]
  exact alnAll_45_45_15 j hj hq

theorem leaf_45_45_20 (hp : 20 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 45 []).length)
    (hq : (normIsRep.getD 45 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 20 hp)
        (rowE2 (⟨45, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp))
        (rowE1 (⟨45, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨45, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨45, by decide⟩ (listedAt ⟨45, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp)) T45_45
      hfix45_45 hinj45_45 hcardT45_45
      (fun i => conj_mem_of_fixedPoints _ _ (T45_45 i) (hfix45_45 i) _)
      ⟨45, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨45, by decide⟩ (Q2.listedAt ⟨45, by decide⟩
        (alnCheck_rep ⟨45, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 20 hp) Q2.T45_45_2 Q2.hfix45_45_2 Q2.hinj45_45_2
      Q2.hcardT45_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T45_45_2 i) (Q2.hfix45_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨45, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T45_45 = colFn colCert_45_45_20.D (m := 25) from colCert_45_45_20.bind1,
    show colData2 (⟨45, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 20 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T45_45_2 = colFn colCert_45_45_20.D (m := 25) from colCert_45_45_20.bind2]
  exact alnAll_45_45_20 j hj hq

theorem leaf_46_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 46 []).length)
    (hq : (normIsRep.getD 46 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨46, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨46, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨46, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨46, by decide⟩ (listedAt ⟨46, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T46_12
      hfix46_12 hinj46_12 hcardT46_12
      (fun i => conj_mem_of_fixedPoints _ _ (T46_12 i) (hfix46_12 i) _)
      ⟨46, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨46, by decide⟩ (Q2.listedAt ⟨46, by decide⟩
        (alnCheck_rep ⟨46, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T46_12_2 Q2.hfix46_12_2 Q2.hinj46_12_2
      Q2.hcardT46_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T46_12_2 i) (Q2.hfix46_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨46, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T46_12 = colFn colCert_46_12_0.D (m := 125) from colCert_46_12_0.bind1,
    show colData2 (⟨46, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T46_12_2 = colFn colCert_46_12_0.D (m := 125) from colCert_46_12_0.bind2]
  exact alnAll_46_12_0 j hj hq

theorem leaf_46_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 46 []).length)
    (hq : (normIsRep.getD 46 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨46, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨46, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨46, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨46, by decide⟩ (listedAt ⟨46, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T46_12
      hfix46_12 hinj46_12 hcardT46_12
      (fun i => conj_mem_of_fixedPoints _ _ (T46_12 i) (hfix46_12 i) _)
      ⟨46, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨46, by decide⟩ (Q2.listedAt ⟨46, by decide⟩
        (alnCheck_rep ⟨46, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T46_12_2 Q2.hfix46_12_2 Q2.hinj46_12_2
      Q2.hcardT46_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T46_12_2 i) (Q2.hfix46_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨46, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T46_12 = colFn colCert_46_12_1.D (m := 125) from colCert_46_12_1.bind1,
    show colData2 (⟨46, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T46_12_2 = colFn colCert_46_12_1.D (m := 125) from colCert_46_12_1.bind2]
  exact alnAll_46_12_1 j hj hq

theorem leaf_46_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 46 []).length)
    (hq : (normIsRep.getD 46 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨46, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨46, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨46, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨46, by decide⟩ (listedAt ⟨46, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T46_12
      hfix46_12 hinj46_12 hcardT46_12
      (fun i => conj_mem_of_fixedPoints _ _ (T46_12 i) (hfix46_12 i) _)
      ⟨46, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨46, by decide⟩ (Q2.listedAt ⟨46, by decide⟩
        (alnCheck_rep ⟨46, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T46_12_2 Q2.hfix46_12_2 Q2.hinj46_12_2
      Q2.hcardT46_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T46_12_2 i) (Q2.hfix46_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨46, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T46_12 = colFn colCert_46_12_2.D (m := 125) from colCert_46_12_2.bind1,
    show colData2 (⟨46, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T46_12_2 = colFn colCert_46_12_2.D (m := 125) from colCert_46_12_2.bind2]
  exact alnAll_46_12_2 j hj hq

theorem leaf_46_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 46 []).length)
    (hq : (normIsRep.getD 46 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨46, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨46, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨46, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨46, by decide⟩ (listedAt ⟨46, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T46_12
      hfix46_12 hinj46_12 hcardT46_12
      (fun i => conj_mem_of_fixedPoints _ _ (T46_12 i) (hfix46_12 i) _)
      ⟨46, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨46, by decide⟩ (Q2.listedAt ⟨46, by decide⟩
        (alnCheck_rep ⟨46, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T46_12_2 Q2.hfix46_12_2 Q2.hinj46_12_2
      Q2.hcardT46_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T46_12_2 i) (Q2.hfix46_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨46, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T46_12 = colFn colCert_46_12_3.D (m := 125) from colCert_46_12_3.bind1,
    show colData2 (⟨46, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T46_12_2 = colFn colCert_46_12_3.D (m := 125) from colCert_46_12_3.bind2]
  exact alnAll_46_12_3 j hj hq

theorem leaf_46_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 46 []).length)
    (hq : (normIsRep.getD 46 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨46, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨46, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨46, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨46, by decide⟩ (listedAt ⟨46, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T46_12
      hfix46_12 hinj46_12 hcardT46_12
      (fun i => conj_mem_of_fixedPoints _ _ (T46_12 i) (hfix46_12 i) _)
      ⟨46, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨46, by decide⟩ (Q2.listedAt ⟨46, by decide⟩
        (alnCheck_rep ⟨46, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T46_12_2 Q2.hfix46_12_2 Q2.hinj46_12_2
      Q2.hcardT46_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T46_12_2 i) (Q2.hfix46_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨46, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T46_12 = colFn colCert_46_12_4.D (m := 125) from colCert_46_12_4.bind1,
    show colData2 (⟨46, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T46_12_2 = colFn colCert_46_12_4.D (m := 125) from colCert_46_12_4.bind2]
  exact alnAll_46_12_4 j hj hq

theorem leaf_46_46_0 (hp : 0 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 46 []).length)
    (hq : (normIsRep.getD 46 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 0 hp)
        (rowE2 (⟨46, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp))
        (rowE1 (⟨46, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨46, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨46, by decide⟩ (listedAt ⟨46, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp)) T46_46
      hfix46_46 hinj46_46 hcardT46_46
      (fun i => conj_mem_of_fixedPoints _ _ (T46_46 i) (hfix46_46 i) _)
      ⟨46, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨46, by decide⟩ (Q2.listedAt ⟨46, by decide⟩
        (alnCheck_rep ⟨46, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 0 hp) Q2.T46_46_2 Q2.hfix46_46_2 Q2.hinj46_46_2
      Q2.hcardT46_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T46_46_2 i) (Q2.hfix46_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨46, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T46_46 = colFn colCert_46_46_0.D (m := 25) from colCert_46_46_0.bind1,
    show colData2 (⟨46, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 0 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T46_46_2 = colFn colCert_46_46_0.D (m := 25) from colCert_46_46_0.bind2]
  exact alnAll_46_46_0 j hj hq

theorem leaf_46_46_1 (hp : 1 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 46 []).length)
    (hq : (normIsRep.getD 46 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 1 hp)
        (rowE2 (⟨46, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp))
        (rowE1 (⟨46, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨46, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨46, by decide⟩ (listedAt ⟨46, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp)) T46_46
      hfix46_46 hinj46_46 hcardT46_46
      (fun i => conj_mem_of_fixedPoints _ _ (T46_46 i) (hfix46_46 i) _)
      ⟨46, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨46, by decide⟩ (Q2.listedAt ⟨46, by decide⟩
        (alnCheck_rep ⟨46, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 1 hp) Q2.T46_46_2 Q2.hfix46_46_2 Q2.hinj46_46_2
      Q2.hcardT46_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T46_46_2 i) (Q2.hfix46_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨46, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T46_46 = colFn colCert_46_46_1.D (m := 25) from colCert_46_46_1.bind1,
    show colData2 (⟨46, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 1 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T46_46_2 = colFn colCert_46_46_1.D (m := 25) from colCert_46_46_1.bind2]
  exact alnAll_46_46_1 j hj hq

theorem leaf_46_46_2 (hp : 2 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 46 []).length)
    (hq : (normIsRep.getD 46 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 2 hp)
        (rowE2 (⟨46, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp))
        (rowE1 (⟨46, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨46, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨46, by decide⟩ (listedAt ⟨46, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp)) T46_46
      hfix46_46 hinj46_46 hcardT46_46
      (fun i => conj_mem_of_fixedPoints _ _ (T46_46 i) (hfix46_46 i) _)
      ⟨46, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨46, by decide⟩ (Q2.listedAt ⟨46, by decide⟩
        (alnCheck_rep ⟨46, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 2 hp) Q2.T46_46_2 Q2.hfix46_46_2 Q2.hinj46_46_2
      Q2.hcardT46_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T46_46_2 i) (Q2.hfix46_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨46, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T46_46 = colFn colCert_46_46_2.D (m := 25) from colCert_46_46_2.bind1,
    show colData2 (⟨46, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 2 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T46_46_2 = colFn colCert_46_46_2.D (m := 25) from colCert_46_46_2.bind2]
  exact alnAll_46_46_2 j hj hq

theorem leaf_46_46_3 (hp : 3 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 46 []).length)
    (hq : (normIsRep.getD 46 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 3 hp)
        (rowE2 (⟨46, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp))
        (rowE1 (⟨46, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨46, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨46, by decide⟩ (listedAt ⟨46, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp)) T46_46
      hfix46_46 hinj46_46 hcardT46_46
      (fun i => conj_mem_of_fixedPoints _ _ (T46_46 i) (hfix46_46 i) _)
      ⟨46, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨46, by decide⟩ (Q2.listedAt ⟨46, by decide⟩
        (alnCheck_rep ⟨46, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 3 hp) Q2.T46_46_2 Q2.hfix46_46_2 Q2.hinj46_46_2
      Q2.hcardT46_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T46_46_2 i) (Q2.hfix46_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨46, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T46_46 = colFn colCert_46_46_3.D (m := 25) from colCert_46_46_3.bind1,
    show colData2 (⟨46, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 3 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T46_46_2 = colFn colCert_46_46_3.D (m := 25) from colCert_46_46_3.bind2]
  exact alnAll_46_46_3 j hj hq

theorem leaf_46_46_4 (hp : 4 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 46 []).length)
    (hq : (normIsRep.getD 46 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 4 hp)
        (rowE2 (⟨46, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp))
        (rowE1 (⟨46, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨46, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨46, by decide⟩ (listedAt ⟨46, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp)) T46_46
      hfix46_46 hinj46_46 hcardT46_46
      (fun i => conj_mem_of_fixedPoints _ _ (T46_46 i) (hfix46_46 i) _)
      ⟨46, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨46, by decide⟩ (Q2.listedAt ⟨46, by decide⟩
        (alnCheck_rep ⟨46, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 4 hp) Q2.T46_46_2 Q2.hfix46_46_2 Q2.hinj46_46_2
      Q2.hcardT46_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T46_46_2 i) (Q2.hfix46_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨46, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T46_46 = colFn colCert_46_46_4.D (m := 25) from colCert_46_46_4.bind1,
    show colData2 (⟨46, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 4 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T46_46_2 = colFn colCert_46_46_4.D (m := 25) from colCert_46_46_4.bind2]
  exact alnAll_46_46_4 j hj hq

theorem leaf_46_46_5 (hp : 5 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 46 []).length)
    (hq : (normIsRep.getD 46 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 5 hp)
        (rowE2 (⟨46, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp))
        (rowE1 (⟨46, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨46, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨46, by decide⟩ (listedAt ⟨46, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp)) T46_46
      hfix46_46 hinj46_46 hcardT46_46
      (fun i => conj_mem_of_fixedPoints _ _ (T46_46 i) (hfix46_46 i) _)
      ⟨46, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨46, by decide⟩ (Q2.listedAt ⟨46, by decide⟩
        (alnCheck_rep ⟨46, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 5 hp) Q2.T46_46_2 Q2.hfix46_46_2 Q2.hinj46_46_2
      Q2.hcardT46_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T46_46_2 i) (Q2.hfix46_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨46, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T46_46 = colFn colCert_46_46_5.D (m := 25) from colCert_46_46_5.bind1,
    show colData2 (⟨46, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 5 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T46_46_2 = colFn colCert_46_46_5.D (m := 25) from colCert_46_46_5.bind2]
  exact alnAll_46_46_5 j hj hq

theorem leaf_46_46_10 (hp : 10 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 46 []).length)
    (hq : (normIsRep.getD 46 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 10 hp)
        (rowE2 (⟨46, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp))
        (rowE1 (⟨46, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨46, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨46, by decide⟩ (listedAt ⟨46, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp)) T46_46
      hfix46_46 hinj46_46 hcardT46_46
      (fun i => conj_mem_of_fixedPoints _ _ (T46_46 i) (hfix46_46 i) _)
      ⟨46, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨46, by decide⟩ (Q2.listedAt ⟨46, by decide⟩
        (alnCheck_rep ⟨46, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 10 hp) Q2.T46_46_2 Q2.hfix46_46_2 Q2.hinj46_46_2
      Q2.hcardT46_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T46_46_2 i) (Q2.hfix46_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨46, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T46_46 = colFn colCert_46_46_10.D (m := 25) from colCert_46_46_10.bind1,
    show colData2 (⟨46, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 10 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T46_46_2 = colFn colCert_46_46_10.D (m := 25) from colCert_46_46_10.bind2]
  exact alnAll_46_46_10 j hj hq

theorem leaf_46_46_15 (hp : 15 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 46 []).length)
    (hq : (normIsRep.getD 46 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 15 hp)
        (rowE2 (⟨46, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp))
        (rowE1 (⟨46, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨46, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨46, by decide⟩ (listedAt ⟨46, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp)) T46_46
      hfix46_46 hinj46_46 hcardT46_46
      (fun i => conj_mem_of_fixedPoints _ _ (T46_46 i) (hfix46_46 i) _)
      ⟨46, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨46, by decide⟩ (Q2.listedAt ⟨46, by decide⟩
        (alnCheck_rep ⟨46, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 15 hp) Q2.T46_46_2 Q2.hfix46_46_2 Q2.hinj46_46_2
      Q2.hcardT46_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T46_46_2 i) (Q2.hfix46_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨46, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T46_46 = colFn colCert_46_46_15.D (m := 25) from colCert_46_46_15.bind1,
    show colData2 (⟨46, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 15 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T46_46_2 = colFn colCert_46_46_15.D (m := 25) from colCert_46_46_15.bind2]
  exact alnAll_46_46_15 j hj hq

theorem leaf_46_46_20 (hp : 20 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 46 []).length)
    (hq : (normIsRep.getD 46 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 20 hp)
        (rowE2 (⟨46, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp))
        (rowE1 (⟨46, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨46, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨46, by decide⟩ (listedAt ⟨46, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp)) T46_46
      hfix46_46 hinj46_46 hcardT46_46
      (fun i => conj_mem_of_fixedPoints _ _ (T46_46 i) (hfix46_46 i) _)
      ⟨46, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨46, by decide⟩ (Q2.listedAt ⟨46, by decide⟩
        (alnCheck_rep ⟨46, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 20 hp) Q2.T46_46_2 Q2.hfix46_46_2 Q2.hinj46_46_2
      Q2.hcardT46_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T46_46_2 i) (Q2.hfix46_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨46, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T46_46 = colFn colCert_46_46_20.D (m := 25) from colCert_46_46_20.bind1,
    show colData2 (⟨46, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 20 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T46_46_2 = colFn colCert_46_46_20.D (m := 25) from colCert_46_46_20.bind2]
  exact alnAll_46_46_20 j hj hq

theorem leaf_47_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 47 []).length)
    (hq : (normIsRep.getD 47 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨47, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨47, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨47, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨47, by decide⟩ (listedAt ⟨47, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T47_12
      hfix47_12 hinj47_12 hcardT47_12
      (fun i => conj_mem_of_fixedPoints _ _ (T47_12 i) (hfix47_12 i) _)
      ⟨47, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨47, by decide⟩ (Q2.listedAt ⟨47, by decide⟩
        (alnCheck_rep ⟨47, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T47_12_2 Q2.hfix47_12_2 Q2.hinj47_12_2
      Q2.hcardT47_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T47_12_2 i) (Q2.hfix47_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨47, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T47_12 = colFn colCert_47_12_0.D (m := 125) from colCert_47_12_0.bind1,
    show colData2 (⟨47, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T47_12_2 = colFn colCert_47_12_0.D (m := 125) from colCert_47_12_0.bind2]
  exact alnAll_47_12_0 j hj hq

theorem leaf_47_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 47 []).length)
    (hq : (normIsRep.getD 47 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨47, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨47, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨47, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨47, by decide⟩ (listedAt ⟨47, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T47_12
      hfix47_12 hinj47_12 hcardT47_12
      (fun i => conj_mem_of_fixedPoints _ _ (T47_12 i) (hfix47_12 i) _)
      ⟨47, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨47, by decide⟩ (Q2.listedAt ⟨47, by decide⟩
        (alnCheck_rep ⟨47, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T47_12_2 Q2.hfix47_12_2 Q2.hinj47_12_2
      Q2.hcardT47_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T47_12_2 i) (Q2.hfix47_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨47, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T47_12 = colFn colCert_47_12_1.D (m := 125) from colCert_47_12_1.bind1,
    show colData2 (⟨47, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T47_12_2 = colFn colCert_47_12_1.D (m := 125) from colCert_47_12_1.bind2]
  exact alnAll_47_12_1 j hj hq

theorem leaf_47_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 47 []).length)
    (hq : (normIsRep.getD 47 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨47, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨47, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨47, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨47, by decide⟩ (listedAt ⟨47, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T47_12
      hfix47_12 hinj47_12 hcardT47_12
      (fun i => conj_mem_of_fixedPoints _ _ (T47_12 i) (hfix47_12 i) _)
      ⟨47, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨47, by decide⟩ (Q2.listedAt ⟨47, by decide⟩
        (alnCheck_rep ⟨47, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T47_12_2 Q2.hfix47_12_2 Q2.hinj47_12_2
      Q2.hcardT47_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T47_12_2 i) (Q2.hfix47_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨47, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T47_12 = colFn colCert_47_12_2.D (m := 125) from colCert_47_12_2.bind1,
    show colData2 (⟨47, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T47_12_2 = colFn colCert_47_12_2.D (m := 125) from colCert_47_12_2.bind2]
  exact alnAll_47_12_2 j hj hq

theorem leaf_47_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 47 []).length)
    (hq : (normIsRep.getD 47 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨47, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨47, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨47, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨47, by decide⟩ (listedAt ⟨47, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T47_12
      hfix47_12 hinj47_12 hcardT47_12
      (fun i => conj_mem_of_fixedPoints _ _ (T47_12 i) (hfix47_12 i) _)
      ⟨47, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨47, by decide⟩ (Q2.listedAt ⟨47, by decide⟩
        (alnCheck_rep ⟨47, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T47_12_2 Q2.hfix47_12_2 Q2.hinj47_12_2
      Q2.hcardT47_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T47_12_2 i) (Q2.hfix47_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨47, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T47_12 = colFn colCert_47_12_3.D (m := 125) from colCert_47_12_3.bind1,
    show colData2 (⟨47, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T47_12_2 = colFn colCert_47_12_3.D (m := 125) from colCert_47_12_3.bind2]
  exact alnAll_47_12_3 j hj hq

theorem leaf_47_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 47 []).length)
    (hq : (normIsRep.getD 47 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨47, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨47, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨47, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨47, by decide⟩ (listedAt ⟨47, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T47_12
      hfix47_12 hinj47_12 hcardT47_12
      (fun i => conj_mem_of_fixedPoints _ _ (T47_12 i) (hfix47_12 i) _)
      ⟨47, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨47, by decide⟩ (Q2.listedAt ⟨47, by decide⟩
        (alnCheck_rep ⟨47, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T47_12_2 Q2.hfix47_12_2 Q2.hinj47_12_2
      Q2.hcardT47_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T47_12_2 i) (Q2.hfix47_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨47, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T47_12 = colFn colCert_47_12_4.D (m := 125) from colCert_47_12_4.bind1,
    show colData2 (⟨47, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T47_12_2 = colFn colCert_47_12_4.D (m := 125) from colCert_47_12_4.bind2]
  exact alnAll_47_12_4 j hj hq

theorem leaf_47_47_0 (hp : 0 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 47 []).length)
    (hq : (normIsRep.getD 47 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 0 hp)
        (rowE2 (⟨47, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp))
        (rowE1 (⟨47, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨47, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨47, by decide⟩ (listedAt ⟨47, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp)) T47_47
      hfix47_47 hinj47_47 hcardT47_47
      (fun i => conj_mem_of_fixedPoints _ _ (T47_47 i) (hfix47_47 i) _)
      ⟨47, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨47, by decide⟩ (Q2.listedAt ⟨47, by decide⟩
        (alnCheck_rep ⟨47, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 0 hp) Q2.T47_47_2 Q2.hfix47_47_2 Q2.hinj47_47_2
      Q2.hcardT47_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T47_47_2 i) (Q2.hfix47_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨47, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T47_47 = colFn colCert_47_47_0.D (m := 25) from colCert_47_47_0.bind1,
    show colData2 (⟨47, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 0 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T47_47_2 = colFn colCert_47_47_0.D (m := 25) from colCert_47_47_0.bind2]
  exact alnAll_47_47_0 j hj hq

theorem leaf_47_47_1 (hp : 1 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 47 []).length)
    (hq : (normIsRep.getD 47 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 1 hp)
        (rowE2 (⟨47, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp))
        (rowE1 (⟨47, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨47, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨47, by decide⟩ (listedAt ⟨47, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp)) T47_47
      hfix47_47 hinj47_47 hcardT47_47
      (fun i => conj_mem_of_fixedPoints _ _ (T47_47 i) (hfix47_47 i) _)
      ⟨47, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨47, by decide⟩ (Q2.listedAt ⟨47, by decide⟩
        (alnCheck_rep ⟨47, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 1 hp) Q2.T47_47_2 Q2.hfix47_47_2 Q2.hinj47_47_2
      Q2.hcardT47_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T47_47_2 i) (Q2.hfix47_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨47, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T47_47 = colFn colCert_47_47_1.D (m := 25) from colCert_47_47_1.bind1,
    show colData2 (⟨47, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 1 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T47_47_2 = colFn colCert_47_47_1.D (m := 25) from colCert_47_47_1.bind2]
  exact alnAll_47_47_1 j hj hq

theorem leaf_47_47_2 (hp : 2 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 47 []).length)
    (hq : (normIsRep.getD 47 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 2 hp)
        (rowE2 (⟨47, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp))
        (rowE1 (⟨47, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨47, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨47, by decide⟩ (listedAt ⟨47, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp)) T47_47
      hfix47_47 hinj47_47 hcardT47_47
      (fun i => conj_mem_of_fixedPoints _ _ (T47_47 i) (hfix47_47 i) _)
      ⟨47, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨47, by decide⟩ (Q2.listedAt ⟨47, by decide⟩
        (alnCheck_rep ⟨47, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 2 hp) Q2.T47_47_2 Q2.hfix47_47_2 Q2.hinj47_47_2
      Q2.hcardT47_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T47_47_2 i) (Q2.hfix47_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨47, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T47_47 = colFn colCert_47_47_2.D (m := 25) from colCert_47_47_2.bind1,
    show colData2 (⟨47, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 2 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T47_47_2 = colFn colCert_47_47_2.D (m := 25) from colCert_47_47_2.bind2]
  exact alnAll_47_47_2 j hj hq

theorem leaf_47_47_3 (hp : 3 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 47 []).length)
    (hq : (normIsRep.getD 47 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 3 hp)
        (rowE2 (⟨47, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp))
        (rowE1 (⟨47, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨47, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨47, by decide⟩ (listedAt ⟨47, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp)) T47_47
      hfix47_47 hinj47_47 hcardT47_47
      (fun i => conj_mem_of_fixedPoints _ _ (T47_47 i) (hfix47_47 i) _)
      ⟨47, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨47, by decide⟩ (Q2.listedAt ⟨47, by decide⟩
        (alnCheck_rep ⟨47, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 3 hp) Q2.T47_47_2 Q2.hfix47_47_2 Q2.hinj47_47_2
      Q2.hcardT47_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T47_47_2 i) (Q2.hfix47_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨47, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T47_47 = colFn colCert_47_47_3.D (m := 25) from colCert_47_47_3.bind1,
    show colData2 (⟨47, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 3 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T47_47_2 = colFn colCert_47_47_3.D (m := 25) from colCert_47_47_3.bind2]
  exact alnAll_47_47_3 j hj hq

theorem leaf_47_47_4 (hp : 4 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 47 []).length)
    (hq : (normIsRep.getD 47 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 4 hp)
        (rowE2 (⟨47, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp))
        (rowE1 (⟨47, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨47, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨47, by decide⟩ (listedAt ⟨47, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp)) T47_47
      hfix47_47 hinj47_47 hcardT47_47
      (fun i => conj_mem_of_fixedPoints _ _ (T47_47 i) (hfix47_47 i) _)
      ⟨47, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨47, by decide⟩ (Q2.listedAt ⟨47, by decide⟩
        (alnCheck_rep ⟨47, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 4 hp) Q2.T47_47_2 Q2.hfix47_47_2 Q2.hinj47_47_2
      Q2.hcardT47_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T47_47_2 i) (Q2.hfix47_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨47, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T47_47 = colFn colCert_47_47_4.D (m := 25) from colCert_47_47_4.bind1,
    show colData2 (⟨47, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 4 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T47_47_2 = colFn colCert_47_47_4.D (m := 25) from colCert_47_47_4.bind2]
  exact alnAll_47_47_4 j hj hq

theorem leaf_47_47_5 (hp : 5 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 47 []).length)
    (hq : (normIsRep.getD 47 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 5 hp)
        (rowE2 (⟨47, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp))
        (rowE1 (⟨47, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨47, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨47, by decide⟩ (listedAt ⟨47, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp)) T47_47
      hfix47_47 hinj47_47 hcardT47_47
      (fun i => conj_mem_of_fixedPoints _ _ (T47_47 i) (hfix47_47 i) _)
      ⟨47, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨47, by decide⟩ (Q2.listedAt ⟨47, by decide⟩
        (alnCheck_rep ⟨47, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 5 hp) Q2.T47_47_2 Q2.hfix47_47_2 Q2.hinj47_47_2
      Q2.hcardT47_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T47_47_2 i) (Q2.hfix47_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨47, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T47_47 = colFn colCert_47_47_5.D (m := 25) from colCert_47_47_5.bind1,
    show colData2 (⟨47, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 5 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T47_47_2 = colFn colCert_47_47_5.D (m := 25) from colCert_47_47_5.bind2]
  exact alnAll_47_47_5 j hj hq

theorem leaf_47_47_10 (hp : 10 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 47 []).length)
    (hq : (normIsRep.getD 47 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 10 hp)
        (rowE2 (⟨47, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp))
        (rowE1 (⟨47, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨47, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨47, by decide⟩ (listedAt ⟨47, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp)) T47_47
      hfix47_47 hinj47_47 hcardT47_47
      (fun i => conj_mem_of_fixedPoints _ _ (T47_47 i) (hfix47_47 i) _)
      ⟨47, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨47, by decide⟩ (Q2.listedAt ⟨47, by decide⟩
        (alnCheck_rep ⟨47, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 10 hp) Q2.T47_47_2 Q2.hfix47_47_2 Q2.hinj47_47_2
      Q2.hcardT47_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T47_47_2 i) (Q2.hfix47_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨47, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T47_47 = colFn colCert_47_47_10.D (m := 25) from colCert_47_47_10.bind1,
    show colData2 (⟨47, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 10 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T47_47_2 = colFn colCert_47_47_10.D (m := 25) from colCert_47_47_10.bind2]
  exact alnAll_47_47_10 j hj hq

theorem leaf_47_47_15 (hp : 15 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 47 []).length)
    (hq : (normIsRep.getD 47 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 15 hp)
        (rowE2 (⟨47, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp))
        (rowE1 (⟨47, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨47, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨47, by decide⟩ (listedAt ⟨47, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp)) T47_47
      hfix47_47 hinj47_47 hcardT47_47
      (fun i => conj_mem_of_fixedPoints _ _ (T47_47 i) (hfix47_47 i) _)
      ⟨47, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨47, by decide⟩ (Q2.listedAt ⟨47, by decide⟩
        (alnCheck_rep ⟨47, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 15 hp) Q2.T47_47_2 Q2.hfix47_47_2 Q2.hinj47_47_2
      Q2.hcardT47_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T47_47_2 i) (Q2.hfix47_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨47, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T47_47 = colFn colCert_47_47_15.D (m := 25) from colCert_47_47_15.bind1,
    show colData2 (⟨47, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 15 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T47_47_2 = colFn colCert_47_47_15.D (m := 25) from colCert_47_47_15.bind2]
  exact alnAll_47_47_15 j hj hq

theorem leaf_47_47_20 (hp : 20 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 47 []).length)
    (hq : (normIsRep.getD 47 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 20 hp)
        (rowE2 (⟨47, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp))
        (rowE1 (⟨47, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨47, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨47, by decide⟩ (listedAt ⟨47, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp)) T47_47
      hfix47_47 hinj47_47 hcardT47_47
      (fun i => conj_mem_of_fixedPoints _ _ (T47_47 i) (hfix47_47 i) _)
      ⟨47, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨47, by decide⟩ (Q2.listedAt ⟨47, by decide⟩
        (alnCheck_rep ⟨47, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 20 hp) Q2.T47_47_2 Q2.hfix47_47_2 Q2.hinj47_47_2
      Q2.hcardT47_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T47_47_2 i) (Q2.hfix47_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨47, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T47_47 = colFn colCert_47_47_20.D (m := 25) from colCert_47_47_20.bind1,
    show colData2 (⟨47, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 20 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T47_47_2 = colFn colCert_47_47_20.D (m := 25) from colCert_47_47_20.bind2]
  exact alnAll_47_47_20 j hj hq

theorem leaf_48_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 48 []).length)
    (hq : (normIsRep.getD 48 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨48, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨48, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨48, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨48, by decide⟩ (listedAt ⟨48, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T48_12
      hfix48_12 hinj48_12 hcardT48_12
      (fun i => conj_mem_of_fixedPoints _ _ (T48_12 i) (hfix48_12 i) _)
      ⟨48, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨48, by decide⟩ (Q2.listedAt ⟨48, by decide⟩
        (alnCheck_rep ⟨48, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T48_12_2 Q2.hfix48_12_2 Q2.hinj48_12_2
      Q2.hcardT48_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T48_12_2 i) (Q2.hfix48_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨48, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T48_12 = colFn colCert_48_12_0.D (m := 125) from colCert_48_12_0.bind1,
    show colData2 (⟨48, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T48_12_2 = colFn colCert_48_12_0.D (m := 125) from colCert_48_12_0.bind2]
  exact alnAll_48_12_0 j hj hq

theorem leaf_48_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 48 []).length)
    (hq : (normIsRep.getD 48 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨48, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨48, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨48, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨48, by decide⟩ (listedAt ⟨48, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T48_12
      hfix48_12 hinj48_12 hcardT48_12
      (fun i => conj_mem_of_fixedPoints _ _ (T48_12 i) (hfix48_12 i) _)
      ⟨48, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨48, by decide⟩ (Q2.listedAt ⟨48, by decide⟩
        (alnCheck_rep ⟨48, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T48_12_2 Q2.hfix48_12_2 Q2.hinj48_12_2
      Q2.hcardT48_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T48_12_2 i) (Q2.hfix48_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨48, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T48_12 = colFn colCert_48_12_1.D (m := 125) from colCert_48_12_1.bind1,
    show colData2 (⟨48, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T48_12_2 = colFn colCert_48_12_1.D (m := 125) from colCert_48_12_1.bind2]
  exact alnAll_48_12_1 j hj hq

theorem leaf_48_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 48 []).length)
    (hq : (normIsRep.getD 48 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨48, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨48, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨48, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨48, by decide⟩ (listedAt ⟨48, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T48_12
      hfix48_12 hinj48_12 hcardT48_12
      (fun i => conj_mem_of_fixedPoints _ _ (T48_12 i) (hfix48_12 i) _)
      ⟨48, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨48, by decide⟩ (Q2.listedAt ⟨48, by decide⟩
        (alnCheck_rep ⟨48, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T48_12_2 Q2.hfix48_12_2 Q2.hinj48_12_2
      Q2.hcardT48_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T48_12_2 i) (Q2.hfix48_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨48, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T48_12 = colFn colCert_48_12_2.D (m := 125) from colCert_48_12_2.bind1,
    show colData2 (⟨48, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T48_12_2 = colFn colCert_48_12_2.D (m := 125) from colCert_48_12_2.bind2]
  exact alnAll_48_12_2 j hj hq

theorem leaf_48_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 48 []).length)
    (hq : (normIsRep.getD 48 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨48, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨48, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨48, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨48, by decide⟩ (listedAt ⟨48, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T48_12
      hfix48_12 hinj48_12 hcardT48_12
      (fun i => conj_mem_of_fixedPoints _ _ (T48_12 i) (hfix48_12 i) _)
      ⟨48, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨48, by decide⟩ (Q2.listedAt ⟨48, by decide⟩
        (alnCheck_rep ⟨48, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T48_12_2 Q2.hfix48_12_2 Q2.hinj48_12_2
      Q2.hcardT48_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T48_12_2 i) (Q2.hfix48_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨48, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T48_12 = colFn colCert_48_12_3.D (m := 125) from colCert_48_12_3.bind1,
    show colData2 (⟨48, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T48_12_2 = colFn colCert_48_12_3.D (m := 125) from colCert_48_12_3.bind2]
  exact alnAll_48_12_3 j hj hq

theorem leaf_48_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 48 []).length)
    (hq : (normIsRep.getD 48 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨48, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨48, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨48, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨48, by decide⟩ (listedAt ⟨48, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T48_12
      hfix48_12 hinj48_12 hcardT48_12
      (fun i => conj_mem_of_fixedPoints _ _ (T48_12 i) (hfix48_12 i) _)
      ⟨48, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨48, by decide⟩ (Q2.listedAt ⟨48, by decide⟩
        (alnCheck_rep ⟨48, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T48_12_2 Q2.hfix48_12_2 Q2.hinj48_12_2
      Q2.hcardT48_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T48_12_2 i) (Q2.hfix48_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨48, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T48_12 = colFn colCert_48_12_4.D (m := 125) from colCert_48_12_4.bind1,
    show colData2 (⟨48, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T48_12_2 = colFn colCert_48_12_4.D (m := 125) from colCert_48_12_4.bind2]
  exact alnAll_48_12_4 j hj hq

theorem leaf_48_48_0 (hp : 0 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 48 []).length)
    (hq : (normIsRep.getD 48 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 0 hp)
        (rowE2 (⟨48, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp))
        (rowE1 (⟨48, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨48, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨48, by decide⟩ (listedAt ⟨48, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp)) T48_48
      hfix48_48 hinj48_48 hcardT48_48
      (fun i => conj_mem_of_fixedPoints _ _ (T48_48 i) (hfix48_48 i) _)
      ⟨48, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨48, by decide⟩ (Q2.listedAt ⟨48, by decide⟩
        (alnCheck_rep ⟨48, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 0 hp) Q2.T48_48_2 Q2.hfix48_48_2 Q2.hinj48_48_2
      Q2.hcardT48_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T48_48_2 i) (Q2.hfix48_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨48, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T48_48 = colFn colCert_48_48_0.D (m := 25) from colCert_48_48_0.bind1,
    show colData2 (⟨48, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 0 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T48_48_2 = colFn colCert_48_48_0.D (m := 25) from colCert_48_48_0.bind2]
  exact alnAll_48_48_0 j hj hq

theorem leaf_48_48_1 (hp : 1 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 48 []).length)
    (hq : (normIsRep.getD 48 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 1 hp)
        (rowE2 (⟨48, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp))
        (rowE1 (⟨48, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨48, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨48, by decide⟩ (listedAt ⟨48, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp)) T48_48
      hfix48_48 hinj48_48 hcardT48_48
      (fun i => conj_mem_of_fixedPoints _ _ (T48_48 i) (hfix48_48 i) _)
      ⟨48, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨48, by decide⟩ (Q2.listedAt ⟨48, by decide⟩
        (alnCheck_rep ⟨48, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 1 hp) Q2.T48_48_2 Q2.hfix48_48_2 Q2.hinj48_48_2
      Q2.hcardT48_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T48_48_2 i) (Q2.hfix48_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨48, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T48_48 = colFn colCert_48_48_1.D (m := 25) from colCert_48_48_1.bind1,
    show colData2 (⟨48, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 1 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T48_48_2 = colFn colCert_48_48_1.D (m := 25) from colCert_48_48_1.bind2]
  exact alnAll_48_48_1 j hj hq

theorem leaf_48_48_2 (hp : 2 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 48 []).length)
    (hq : (normIsRep.getD 48 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 2 hp)
        (rowE2 (⟨48, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp))
        (rowE1 (⟨48, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨48, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨48, by decide⟩ (listedAt ⟨48, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp)) T48_48
      hfix48_48 hinj48_48 hcardT48_48
      (fun i => conj_mem_of_fixedPoints _ _ (T48_48 i) (hfix48_48 i) _)
      ⟨48, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨48, by decide⟩ (Q2.listedAt ⟨48, by decide⟩
        (alnCheck_rep ⟨48, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 2 hp) Q2.T48_48_2 Q2.hfix48_48_2 Q2.hinj48_48_2
      Q2.hcardT48_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T48_48_2 i) (Q2.hfix48_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨48, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T48_48 = colFn colCert_48_48_2.D (m := 25) from colCert_48_48_2.bind1,
    show colData2 (⟨48, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 2 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T48_48_2 = colFn colCert_48_48_2.D (m := 25) from colCert_48_48_2.bind2]
  exact alnAll_48_48_2 j hj hq

theorem leaf_48_48_3 (hp : 3 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 48 []).length)
    (hq : (normIsRep.getD 48 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 3 hp)
        (rowE2 (⟨48, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp))
        (rowE1 (⟨48, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨48, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨48, by decide⟩ (listedAt ⟨48, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp)) T48_48
      hfix48_48 hinj48_48 hcardT48_48
      (fun i => conj_mem_of_fixedPoints _ _ (T48_48 i) (hfix48_48 i) _)
      ⟨48, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨48, by decide⟩ (Q2.listedAt ⟨48, by decide⟩
        (alnCheck_rep ⟨48, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 3 hp) Q2.T48_48_2 Q2.hfix48_48_2 Q2.hinj48_48_2
      Q2.hcardT48_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T48_48_2 i) (Q2.hfix48_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨48, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T48_48 = colFn colCert_48_48_3.D (m := 25) from colCert_48_48_3.bind1,
    show colData2 (⟨48, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 3 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T48_48_2 = colFn colCert_48_48_3.D (m := 25) from colCert_48_48_3.bind2]
  exact alnAll_48_48_3 j hj hq

theorem leaf_48_48_4 (hp : 4 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 48 []).length)
    (hq : (normIsRep.getD 48 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 4 hp)
        (rowE2 (⟨48, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp))
        (rowE1 (⟨48, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨48, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨48, by decide⟩ (listedAt ⟨48, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp)) T48_48
      hfix48_48 hinj48_48 hcardT48_48
      (fun i => conj_mem_of_fixedPoints _ _ (T48_48 i) (hfix48_48 i) _)
      ⟨48, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨48, by decide⟩ (Q2.listedAt ⟨48, by decide⟩
        (alnCheck_rep ⟨48, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 4 hp) Q2.T48_48_2 Q2.hfix48_48_2 Q2.hinj48_48_2
      Q2.hcardT48_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T48_48_2 i) (Q2.hfix48_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨48, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T48_48 = colFn colCert_48_48_4.D (m := 25) from colCert_48_48_4.bind1,
    show colData2 (⟨48, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 4 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T48_48_2 = colFn colCert_48_48_4.D (m := 25) from colCert_48_48_4.bind2]
  exact alnAll_48_48_4 j hj hq

theorem leaf_48_48_5 (hp : 5 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 48 []).length)
    (hq : (normIsRep.getD 48 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 5 hp)
        (rowE2 (⟨48, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp))
        (rowE1 (⟨48, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨48, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨48, by decide⟩ (listedAt ⟨48, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp)) T48_48
      hfix48_48 hinj48_48 hcardT48_48
      (fun i => conj_mem_of_fixedPoints _ _ (T48_48 i) (hfix48_48 i) _)
      ⟨48, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨48, by decide⟩ (Q2.listedAt ⟨48, by decide⟩
        (alnCheck_rep ⟨48, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 5 hp) Q2.T48_48_2 Q2.hfix48_48_2 Q2.hinj48_48_2
      Q2.hcardT48_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T48_48_2 i) (Q2.hfix48_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨48, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T48_48 = colFn colCert_48_48_5.D (m := 25) from colCert_48_48_5.bind1,
    show colData2 (⟨48, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 5 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T48_48_2 = colFn colCert_48_48_5.D (m := 25) from colCert_48_48_5.bind2]
  exact alnAll_48_48_5 j hj hq

theorem leaf_48_48_10 (hp : 10 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 48 []).length)
    (hq : (normIsRep.getD 48 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 10 hp)
        (rowE2 (⟨48, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp))
        (rowE1 (⟨48, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨48, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨48, by decide⟩ (listedAt ⟨48, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp)) T48_48
      hfix48_48 hinj48_48 hcardT48_48
      (fun i => conj_mem_of_fixedPoints _ _ (T48_48 i) (hfix48_48 i) _)
      ⟨48, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨48, by decide⟩ (Q2.listedAt ⟨48, by decide⟩
        (alnCheck_rep ⟨48, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 10 hp) Q2.T48_48_2 Q2.hfix48_48_2 Q2.hinj48_48_2
      Q2.hcardT48_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T48_48_2 i) (Q2.hfix48_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨48, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T48_48 = colFn colCert_48_48_10.D (m := 25) from colCert_48_48_10.bind1,
    show colData2 (⟨48, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 10 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T48_48_2 = colFn colCert_48_48_10.D (m := 25) from colCert_48_48_10.bind2]
  exact alnAll_48_48_10 j hj hq

theorem leaf_48_48_15 (hp : 15 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 48 []).length)
    (hq : (normIsRep.getD 48 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 15 hp)
        (rowE2 (⟨48, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp))
        (rowE1 (⟨48, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨48, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨48, by decide⟩ (listedAt ⟨48, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp)) T48_48
      hfix48_48 hinj48_48 hcardT48_48
      (fun i => conj_mem_of_fixedPoints _ _ (T48_48 i) (hfix48_48 i) _)
      ⟨48, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨48, by decide⟩ (Q2.listedAt ⟨48, by decide⟩
        (alnCheck_rep ⟨48, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 15 hp) Q2.T48_48_2 Q2.hfix48_48_2 Q2.hinj48_48_2
      Q2.hcardT48_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T48_48_2 i) (Q2.hfix48_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨48, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T48_48 = colFn colCert_48_48_15.D (m := 25) from colCert_48_48_15.bind1,
    show colData2 (⟨48, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 15 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T48_48_2 = colFn colCert_48_48_15.D (m := 25) from colCert_48_48_15.bind2]
  exact alnAll_48_48_15 j hj hq

theorem leaf_48_48_20 (hp : 20 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 48 []).length)
    (hq : (normIsRep.getD 48 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 20 hp)
        (rowE2 (⟨48, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp))
        (rowE1 (⟨48, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨48, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨48, by decide⟩ (listedAt ⟨48, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp)) T48_48
      hfix48_48 hinj48_48 hcardT48_48
      (fun i => conj_mem_of_fixedPoints _ _ (T48_48 i) (hfix48_48 i) _)
      ⟨48, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨48, by decide⟩ (Q2.listedAt ⟨48, by decide⟩
        (alnCheck_rep ⟨48, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 20 hp) Q2.T48_48_2 Q2.hfix48_48_2 Q2.hinj48_48_2
      Q2.hcardT48_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T48_48_2 i) (Q2.hfix48_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨48, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T48_48 = colFn colCert_48_48_20.D (m := 25) from colCert_48_48_20.bind1,
    show colData2 (⟨48, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 20 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T48_48_2 = colFn colCert_48_48_20.D (m := 25) from colCert_48_48_20.bind2]
  exact alnAll_48_48_20 j hj hq

theorem leaf_49_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 49 []).length)
    (hq : (normIsRep.getD 49 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨49, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨49, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨49, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨49, by decide⟩ (listedAt ⟨49, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T49_12
      hfix49_12 hinj49_12 hcardT49_12
      (fun i => conj_mem_of_fixedPoints _ _ (T49_12 i) (hfix49_12 i) _)
      ⟨49, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨49, by decide⟩ (Q2.listedAt ⟨49, by decide⟩
        (alnCheck_rep ⟨49, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T49_12_2 Q2.hfix49_12_2 Q2.hinj49_12_2
      Q2.hcardT49_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T49_12_2 i) (Q2.hfix49_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨49, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T49_12 = colFn colCert_49_12_0.D (m := 125) from colCert_49_12_0.bind1,
    show colData2 (⟨49, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T49_12_2 = colFn colCert_49_12_0.D (m := 125) from colCert_49_12_0.bind2]
  exact alnAll_49_12_0 j hj hq

theorem leaf_49_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 49 []).length)
    (hq : (normIsRep.getD 49 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨49, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨49, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨49, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨49, by decide⟩ (listedAt ⟨49, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T49_12
      hfix49_12 hinj49_12 hcardT49_12
      (fun i => conj_mem_of_fixedPoints _ _ (T49_12 i) (hfix49_12 i) _)
      ⟨49, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨49, by decide⟩ (Q2.listedAt ⟨49, by decide⟩
        (alnCheck_rep ⟨49, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T49_12_2 Q2.hfix49_12_2 Q2.hinj49_12_2
      Q2.hcardT49_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T49_12_2 i) (Q2.hfix49_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨49, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T49_12 = colFn colCert_49_12_1.D (m := 125) from colCert_49_12_1.bind1,
    show colData2 (⟨49, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T49_12_2 = colFn colCert_49_12_1.D (m := 125) from colCert_49_12_1.bind2]
  exact alnAll_49_12_1 j hj hq

theorem leaf_49_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 49 []).length)
    (hq : (normIsRep.getD 49 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨49, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨49, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨49, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨49, by decide⟩ (listedAt ⟨49, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T49_12
      hfix49_12 hinj49_12 hcardT49_12
      (fun i => conj_mem_of_fixedPoints _ _ (T49_12 i) (hfix49_12 i) _)
      ⟨49, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨49, by decide⟩ (Q2.listedAt ⟨49, by decide⟩
        (alnCheck_rep ⟨49, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T49_12_2 Q2.hfix49_12_2 Q2.hinj49_12_2
      Q2.hcardT49_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T49_12_2 i) (Q2.hfix49_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨49, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T49_12 = colFn colCert_49_12_2.D (m := 125) from colCert_49_12_2.bind1,
    show colData2 (⟨49, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T49_12_2 = colFn colCert_49_12_2.D (m := 125) from colCert_49_12_2.bind2]
  exact alnAll_49_12_2 j hj hq

theorem leaf_49_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 49 []).length)
    (hq : (normIsRep.getD 49 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨49, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨49, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨49, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨49, by decide⟩ (listedAt ⟨49, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T49_12
      hfix49_12 hinj49_12 hcardT49_12
      (fun i => conj_mem_of_fixedPoints _ _ (T49_12 i) (hfix49_12 i) _)
      ⟨49, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨49, by decide⟩ (Q2.listedAt ⟨49, by decide⟩
        (alnCheck_rep ⟨49, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T49_12_2 Q2.hfix49_12_2 Q2.hinj49_12_2
      Q2.hcardT49_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T49_12_2 i) (Q2.hfix49_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨49, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T49_12 = colFn colCert_49_12_3.D (m := 125) from colCert_49_12_3.bind1,
    show colData2 (⟨49, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T49_12_2 = colFn colCert_49_12_3.D (m := 125) from colCert_49_12_3.bind2]
  exact alnAll_49_12_3 j hj hq

theorem leaf_49_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 49 []).length)
    (hq : (normIsRep.getD 49 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨49, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨49, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨49, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨49, by decide⟩ (listedAt ⟨49, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T49_12
      hfix49_12 hinj49_12 hcardT49_12
      (fun i => conj_mem_of_fixedPoints _ _ (T49_12 i) (hfix49_12 i) _)
      ⟨49, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨49, by decide⟩ (Q2.listedAt ⟨49, by decide⟩
        (alnCheck_rep ⟨49, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T49_12_2 Q2.hfix49_12_2 Q2.hinj49_12_2
      Q2.hcardT49_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T49_12_2 i) (Q2.hfix49_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨49, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T49_12 = colFn colCert_49_12_4.D (m := 125) from colCert_49_12_4.bind1,
    show colData2 (⟨49, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T49_12_2 = colFn colCert_49_12_4.D (m := 125) from colCert_49_12_4.bind2]
  exact alnAll_49_12_4 j hj hq

theorem leaf_49_49_0 (hp : 0 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 49 []).length)
    (hq : (normIsRep.getD 49 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 0 hp)
        (rowE2 (⟨49, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp))
        (rowE1 (⟨49, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨49, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨49, by decide⟩ (listedAt ⟨49, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp)) T49_49
      hfix49_49 hinj49_49 hcardT49_49
      (fun i => conj_mem_of_fixedPoints _ _ (T49_49 i) (hfix49_49 i) _)
      ⟨49, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨49, by decide⟩ (Q2.listedAt ⟨49, by decide⟩
        (alnCheck_rep ⟨49, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 0 hp) Q2.T49_49_2 Q2.hfix49_49_2 Q2.hinj49_49_2
      Q2.hcardT49_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T49_49_2 i) (Q2.hfix49_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨49, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T49_49 = colFn colCert_49_49_0.D (m := 25) from colCert_49_49_0.bind1,
    show colData2 (⟨49, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 0 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T49_49_2 = colFn colCert_49_49_0.D (m := 25) from colCert_49_49_0.bind2]
  exact alnAll_49_49_0 j hj hq

theorem leaf_49_49_1 (hp : 1 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 49 []).length)
    (hq : (normIsRep.getD 49 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 1 hp)
        (rowE2 (⟨49, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp))
        (rowE1 (⟨49, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨49, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨49, by decide⟩ (listedAt ⟨49, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp)) T49_49
      hfix49_49 hinj49_49 hcardT49_49
      (fun i => conj_mem_of_fixedPoints _ _ (T49_49 i) (hfix49_49 i) _)
      ⟨49, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨49, by decide⟩ (Q2.listedAt ⟨49, by decide⟩
        (alnCheck_rep ⟨49, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 1 hp) Q2.T49_49_2 Q2.hfix49_49_2 Q2.hinj49_49_2
      Q2.hcardT49_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T49_49_2 i) (Q2.hfix49_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨49, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T49_49 = colFn colCert_49_49_1.D (m := 25) from colCert_49_49_1.bind1,
    show colData2 (⟨49, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 1 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T49_49_2 = colFn colCert_49_49_1.D (m := 25) from colCert_49_49_1.bind2]
  exact alnAll_49_49_1 j hj hq

theorem leaf_49_49_2 (hp : 2 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 49 []).length)
    (hq : (normIsRep.getD 49 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 2 hp)
        (rowE2 (⟨49, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp))
        (rowE1 (⟨49, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨49, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨49, by decide⟩ (listedAt ⟨49, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp)) T49_49
      hfix49_49 hinj49_49 hcardT49_49
      (fun i => conj_mem_of_fixedPoints _ _ (T49_49 i) (hfix49_49 i) _)
      ⟨49, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨49, by decide⟩ (Q2.listedAt ⟨49, by decide⟩
        (alnCheck_rep ⟨49, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 2 hp) Q2.T49_49_2 Q2.hfix49_49_2 Q2.hinj49_49_2
      Q2.hcardT49_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T49_49_2 i) (Q2.hfix49_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨49, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T49_49 = colFn colCert_49_49_2.D (m := 25) from colCert_49_49_2.bind1,
    show colData2 (⟨49, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 2 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T49_49_2 = colFn colCert_49_49_2.D (m := 25) from colCert_49_49_2.bind2]
  exact alnAll_49_49_2 j hj hq

theorem leaf_49_49_3 (hp : 3 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 49 []).length)
    (hq : (normIsRep.getD 49 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 3 hp)
        (rowE2 (⟨49, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp))
        (rowE1 (⟨49, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨49, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨49, by decide⟩ (listedAt ⟨49, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp)) T49_49
      hfix49_49 hinj49_49 hcardT49_49
      (fun i => conj_mem_of_fixedPoints _ _ (T49_49 i) (hfix49_49 i) _)
      ⟨49, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨49, by decide⟩ (Q2.listedAt ⟨49, by decide⟩
        (alnCheck_rep ⟨49, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 3 hp) Q2.T49_49_2 Q2.hfix49_49_2 Q2.hinj49_49_2
      Q2.hcardT49_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T49_49_2 i) (Q2.hfix49_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨49, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T49_49 = colFn colCert_49_49_3.D (m := 25) from colCert_49_49_3.bind1,
    show colData2 (⟨49, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 3 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T49_49_2 = colFn colCert_49_49_3.D (m := 25) from colCert_49_49_3.bind2]
  exact alnAll_49_49_3 j hj hq

theorem leaf_49_49_4 (hp : 4 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 49 []).length)
    (hq : (normIsRep.getD 49 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 4 hp)
        (rowE2 (⟨49, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp))
        (rowE1 (⟨49, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨49, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨49, by decide⟩ (listedAt ⟨49, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp)) T49_49
      hfix49_49 hinj49_49 hcardT49_49
      (fun i => conj_mem_of_fixedPoints _ _ (T49_49 i) (hfix49_49 i) _)
      ⟨49, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨49, by decide⟩ (Q2.listedAt ⟨49, by decide⟩
        (alnCheck_rep ⟨49, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 4 hp) Q2.T49_49_2 Q2.hfix49_49_2 Q2.hinj49_49_2
      Q2.hcardT49_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T49_49_2 i) (Q2.hfix49_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨49, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T49_49 = colFn colCert_49_49_4.D (m := 25) from colCert_49_49_4.bind1,
    show colData2 (⟨49, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 4 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T49_49_2 = colFn colCert_49_49_4.D (m := 25) from colCert_49_49_4.bind2]
  exact alnAll_49_49_4 j hj hq

theorem leaf_49_49_5 (hp : 5 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 49 []).length)
    (hq : (normIsRep.getD 49 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 5 hp)
        (rowE2 (⟨49, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp))
        (rowE1 (⟨49, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨49, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨49, by decide⟩ (listedAt ⟨49, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp)) T49_49
      hfix49_49 hinj49_49 hcardT49_49
      (fun i => conj_mem_of_fixedPoints _ _ (T49_49 i) (hfix49_49 i) _)
      ⟨49, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨49, by decide⟩ (Q2.listedAt ⟨49, by decide⟩
        (alnCheck_rep ⟨49, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 5 hp) Q2.T49_49_2 Q2.hfix49_49_2 Q2.hinj49_49_2
      Q2.hcardT49_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T49_49_2 i) (Q2.hfix49_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨49, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T49_49 = colFn colCert_49_49_5.D (m := 25) from colCert_49_49_5.bind1,
    show colData2 (⟨49, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 5 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T49_49_2 = colFn colCert_49_49_5.D (m := 25) from colCert_49_49_5.bind2]
  exact alnAll_49_49_5 j hj hq

theorem leaf_49_49_10 (hp : 10 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 49 []).length)
    (hq : (normIsRep.getD 49 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 10 hp)
        (rowE2 (⟨49, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp))
        (rowE1 (⟨49, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨49, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨49, by decide⟩ (listedAt ⟨49, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp)) T49_49
      hfix49_49 hinj49_49 hcardT49_49
      (fun i => conj_mem_of_fixedPoints _ _ (T49_49 i) (hfix49_49 i) _)
      ⟨49, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨49, by decide⟩ (Q2.listedAt ⟨49, by decide⟩
        (alnCheck_rep ⟨49, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 10 hp) Q2.T49_49_2 Q2.hfix49_49_2 Q2.hinj49_49_2
      Q2.hcardT49_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T49_49_2 i) (Q2.hfix49_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨49, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T49_49 = colFn colCert_49_49_10.D (m := 25) from colCert_49_49_10.bind1,
    show colData2 (⟨49, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 10 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T49_49_2 = colFn colCert_49_49_10.D (m := 25) from colCert_49_49_10.bind2]
  exact alnAll_49_49_10 j hj hq

theorem leaf_49_49_15 (hp : 15 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 49 []).length)
    (hq : (normIsRep.getD 49 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 15 hp)
        (rowE2 (⟨49, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp))
        (rowE1 (⟨49, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨49, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨49, by decide⟩ (listedAt ⟨49, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp)) T49_49
      hfix49_49 hinj49_49 hcardT49_49
      (fun i => conj_mem_of_fixedPoints _ _ (T49_49 i) (hfix49_49 i) _)
      ⟨49, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨49, by decide⟩ (Q2.listedAt ⟨49, by decide⟩
        (alnCheck_rep ⟨49, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 15 hp) Q2.T49_49_2 Q2.hfix49_49_2 Q2.hinj49_49_2
      Q2.hcardT49_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T49_49_2 i) (Q2.hfix49_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨49, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T49_49 = colFn colCert_49_49_15.D (m := 25) from colCert_49_49_15.bind1,
    show colData2 (⟨49, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 15 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T49_49_2 = colFn colCert_49_49_15.D (m := 25) from colCert_49_49_15.bind2]
  exact alnAll_49_49_15 j hj hq

theorem leaf_49_49_20 (hp : 20 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 49 []).length)
    (hq : (normIsRep.getD 49 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 20 hp)
        (rowE2 (⟨49, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp))
        (rowE1 (⟨49, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨49, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨49, by decide⟩ (listedAt ⟨49, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp)) T49_49
      hfix49_49 hinj49_49 hcardT49_49
      (fun i => conj_mem_of_fixedPoints _ _ (T49_49 i) (hfix49_49 i) _)
      ⟨49, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨49, by decide⟩ (Q2.listedAt ⟨49, by decide⟩
        (alnCheck_rep ⟨49, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 20 hp) Q2.T49_49_2 Q2.hfix49_49_2 Q2.hinj49_49_2
      Q2.hcardT49_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T49_49_2 i) (Q2.hfix49_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨49, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T49_49 = colFn colCert_49_49_20.D (m := 25) from colCert_49_49_20.bind1,
    show colData2 (⟨49, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 20 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T49_49_2 = colFn colCert_49_49_20.D (m := 25) from colCert_49_49_20.bind2]
  exact alnAll_49_49_20 j hj hq

theorem leaf_50_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 50 []).length)
    (hq : (normIsRep.getD 50 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨50, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨50, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨50, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨50, by decide⟩ (listedAt ⟨50, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T50_12
      hfix50_12 hinj50_12 hcardT50_12
      (fun i => conj_mem_of_fixedPoints _ _ (T50_12 i) (hfix50_12 i) _)
      ⟨50, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨50, by decide⟩ (Q2.listedAt ⟨50, by decide⟩
        (alnCheck_rep ⟨50, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T50_12_2 Q2.hfix50_12_2 Q2.hinj50_12_2
      Q2.hcardT50_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T50_12_2 i) (Q2.hfix50_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨50, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T50_12 = colFn colCert_50_12_0.D (m := 125) from colCert_50_12_0.bind1,
    show colData2 (⟨50, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T50_12_2 = colFn colCert_50_12_0.D (m := 125) from colCert_50_12_0.bind2]
  exact alnAll_50_12_0 j hj hq

theorem leaf_50_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 50 []).length)
    (hq : (normIsRep.getD 50 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨50, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨50, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨50, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨50, by decide⟩ (listedAt ⟨50, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T50_12
      hfix50_12 hinj50_12 hcardT50_12
      (fun i => conj_mem_of_fixedPoints _ _ (T50_12 i) (hfix50_12 i) _)
      ⟨50, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨50, by decide⟩ (Q2.listedAt ⟨50, by decide⟩
        (alnCheck_rep ⟨50, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T50_12_2 Q2.hfix50_12_2 Q2.hinj50_12_2
      Q2.hcardT50_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T50_12_2 i) (Q2.hfix50_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨50, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T50_12 = colFn colCert_50_12_1.D (m := 125) from colCert_50_12_1.bind1,
    show colData2 (⟨50, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T50_12_2 = colFn colCert_50_12_1.D (m := 125) from colCert_50_12_1.bind2]
  exact alnAll_50_12_1 j hj hq

theorem leaf_50_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 50 []).length)
    (hq : (normIsRep.getD 50 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨50, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨50, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨50, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨50, by decide⟩ (listedAt ⟨50, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T50_12
      hfix50_12 hinj50_12 hcardT50_12
      (fun i => conj_mem_of_fixedPoints _ _ (T50_12 i) (hfix50_12 i) _)
      ⟨50, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨50, by decide⟩ (Q2.listedAt ⟨50, by decide⟩
        (alnCheck_rep ⟨50, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T50_12_2 Q2.hfix50_12_2 Q2.hinj50_12_2
      Q2.hcardT50_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T50_12_2 i) (Q2.hfix50_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨50, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T50_12 = colFn colCert_50_12_2.D (m := 125) from colCert_50_12_2.bind1,
    show colData2 (⟨50, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T50_12_2 = colFn colCert_50_12_2.D (m := 125) from colCert_50_12_2.bind2]
  exact alnAll_50_12_2 j hj hq

theorem leaf_50_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 50 []).length)
    (hq : (normIsRep.getD 50 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨50, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨50, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨50, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨50, by decide⟩ (listedAt ⟨50, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T50_12
      hfix50_12 hinj50_12 hcardT50_12
      (fun i => conj_mem_of_fixedPoints _ _ (T50_12 i) (hfix50_12 i) _)
      ⟨50, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨50, by decide⟩ (Q2.listedAt ⟨50, by decide⟩
        (alnCheck_rep ⟨50, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T50_12_2 Q2.hfix50_12_2 Q2.hinj50_12_2
      Q2.hcardT50_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T50_12_2 i) (Q2.hfix50_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨50, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T50_12 = colFn colCert_50_12_3.D (m := 125) from colCert_50_12_3.bind1,
    show colData2 (⟨50, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T50_12_2 = colFn colCert_50_12_3.D (m := 125) from colCert_50_12_3.bind2]
  exact alnAll_50_12_3 j hj hq

theorem leaf_50_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 50 []).length)
    (hq : (normIsRep.getD 50 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨50, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨50, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨50, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨50, by decide⟩ (listedAt ⟨50, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T50_12
      hfix50_12 hinj50_12 hcardT50_12
      (fun i => conj_mem_of_fixedPoints _ _ (T50_12 i) (hfix50_12 i) _)
      ⟨50, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨50, by decide⟩ (Q2.listedAt ⟨50, by decide⟩
        (alnCheck_rep ⟨50, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T50_12_2 Q2.hfix50_12_2 Q2.hinj50_12_2
      Q2.hcardT50_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T50_12_2 i) (Q2.hfix50_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨50, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T50_12 = colFn colCert_50_12_4.D (m := 125) from colCert_50_12_4.bind1,
    show colData2 (⟨50, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T50_12_2 = colFn colCert_50_12_4.D (m := 125) from colCert_50_12_4.bind2]
  exact alnAll_50_12_4 j hj hq

theorem leaf_50_50_0 (hp : 0 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 50 []).length)
    (hq : (normIsRep.getD 50 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 0 hp)
        (rowE2 (⟨50, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp))
        (rowE1 (⟨50, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨50, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨50, by decide⟩ (listedAt ⟨50, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp)) T50_50
      hfix50_50 hinj50_50 hcardT50_50
      (fun i => conj_mem_of_fixedPoints _ _ (T50_50 i) (hfix50_50 i) _)
      ⟨50, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨50, by decide⟩ (Q2.listedAt ⟨50, by decide⟩
        (alnCheck_rep ⟨50, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 0 hp) Q2.T50_50_2 Q2.hfix50_50_2 Q2.hinj50_50_2
      Q2.hcardT50_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T50_50_2 i) (Q2.hfix50_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨50, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T50_50 = colFn colCert_50_50_0.D (m := 25) from colCert_50_50_0.bind1,
    show colData2 (⟨50, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 0 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T50_50_2 = colFn colCert_50_50_0.D (m := 25) from colCert_50_50_0.bind2]
  exact alnAll_50_50_0 j hj hq

theorem leaf_50_50_1 (hp : 1 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 50 []).length)
    (hq : (normIsRep.getD 50 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 1 hp)
        (rowE2 (⟨50, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp))
        (rowE1 (⟨50, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨50, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨50, by decide⟩ (listedAt ⟨50, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp)) T50_50
      hfix50_50 hinj50_50 hcardT50_50
      (fun i => conj_mem_of_fixedPoints _ _ (T50_50 i) (hfix50_50 i) _)
      ⟨50, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨50, by decide⟩ (Q2.listedAt ⟨50, by decide⟩
        (alnCheck_rep ⟨50, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 1 hp) Q2.T50_50_2 Q2.hfix50_50_2 Q2.hinj50_50_2
      Q2.hcardT50_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T50_50_2 i) (Q2.hfix50_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨50, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T50_50 = colFn colCert_50_50_1.D (m := 25) from colCert_50_50_1.bind1,
    show colData2 (⟨50, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 1 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T50_50_2 = colFn colCert_50_50_1.D (m := 25) from colCert_50_50_1.bind2]
  exact alnAll_50_50_1 j hj hq

theorem leaf_50_50_2 (hp : 2 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 50 []).length)
    (hq : (normIsRep.getD 50 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 2 hp)
        (rowE2 (⟨50, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp))
        (rowE1 (⟨50, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨50, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨50, by decide⟩ (listedAt ⟨50, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp)) T50_50
      hfix50_50 hinj50_50 hcardT50_50
      (fun i => conj_mem_of_fixedPoints _ _ (T50_50 i) (hfix50_50 i) _)
      ⟨50, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨50, by decide⟩ (Q2.listedAt ⟨50, by decide⟩
        (alnCheck_rep ⟨50, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 2 hp) Q2.T50_50_2 Q2.hfix50_50_2 Q2.hinj50_50_2
      Q2.hcardT50_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T50_50_2 i) (Q2.hfix50_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨50, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T50_50 = colFn colCert_50_50_2.D (m := 25) from colCert_50_50_2.bind1,
    show colData2 (⟨50, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 2 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T50_50_2 = colFn colCert_50_50_2.D (m := 25) from colCert_50_50_2.bind2]
  exact alnAll_50_50_2 j hj hq

theorem leaf_50_50_3 (hp : 3 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 50 []).length)
    (hq : (normIsRep.getD 50 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 3 hp)
        (rowE2 (⟨50, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp))
        (rowE1 (⟨50, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨50, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨50, by decide⟩ (listedAt ⟨50, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp)) T50_50
      hfix50_50 hinj50_50 hcardT50_50
      (fun i => conj_mem_of_fixedPoints _ _ (T50_50 i) (hfix50_50 i) _)
      ⟨50, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨50, by decide⟩ (Q2.listedAt ⟨50, by decide⟩
        (alnCheck_rep ⟨50, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 3 hp) Q2.T50_50_2 Q2.hfix50_50_2 Q2.hinj50_50_2
      Q2.hcardT50_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T50_50_2 i) (Q2.hfix50_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨50, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T50_50 = colFn colCert_50_50_3.D (m := 25) from colCert_50_50_3.bind1,
    show colData2 (⟨50, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 3 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T50_50_2 = colFn colCert_50_50_3.D (m := 25) from colCert_50_50_3.bind2]
  exact alnAll_50_50_3 j hj hq

theorem leaf_50_50_4 (hp : 4 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 50 []).length)
    (hq : (normIsRep.getD 50 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 4 hp)
        (rowE2 (⟨50, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp))
        (rowE1 (⟨50, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨50, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨50, by decide⟩ (listedAt ⟨50, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp)) T50_50
      hfix50_50 hinj50_50 hcardT50_50
      (fun i => conj_mem_of_fixedPoints _ _ (T50_50 i) (hfix50_50 i) _)
      ⟨50, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨50, by decide⟩ (Q2.listedAt ⟨50, by decide⟩
        (alnCheck_rep ⟨50, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 4 hp) Q2.T50_50_2 Q2.hfix50_50_2 Q2.hinj50_50_2
      Q2.hcardT50_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T50_50_2 i) (Q2.hfix50_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨50, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T50_50 = colFn colCert_50_50_4.D (m := 25) from colCert_50_50_4.bind1,
    show colData2 (⟨50, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 4 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T50_50_2 = colFn colCert_50_50_4.D (m := 25) from colCert_50_50_4.bind2]
  exact alnAll_50_50_4 j hj hq

theorem leaf_50_50_5 (hp : 5 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 50 []).length)
    (hq : (normIsRep.getD 50 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 5 hp)
        (rowE2 (⟨50, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp))
        (rowE1 (⟨50, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨50, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨50, by decide⟩ (listedAt ⟨50, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp)) T50_50
      hfix50_50 hinj50_50 hcardT50_50
      (fun i => conj_mem_of_fixedPoints _ _ (T50_50 i) (hfix50_50 i) _)
      ⟨50, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨50, by decide⟩ (Q2.listedAt ⟨50, by decide⟩
        (alnCheck_rep ⟨50, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 5 hp) Q2.T50_50_2 Q2.hfix50_50_2 Q2.hinj50_50_2
      Q2.hcardT50_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T50_50_2 i) (Q2.hfix50_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨50, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T50_50 = colFn colCert_50_50_5.D (m := 25) from colCert_50_50_5.bind1,
    show colData2 (⟨50, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 5 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T50_50_2 = colFn colCert_50_50_5.D (m := 25) from colCert_50_50_5.bind2]
  exact alnAll_50_50_5 j hj hq

theorem leaf_50_50_10 (hp : 10 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 50 []).length)
    (hq : (normIsRep.getD 50 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 10 hp)
        (rowE2 (⟨50, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp))
        (rowE1 (⟨50, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨50, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨50, by decide⟩ (listedAt ⟨50, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp)) T50_50
      hfix50_50 hinj50_50 hcardT50_50
      (fun i => conj_mem_of_fixedPoints _ _ (T50_50 i) (hfix50_50 i) _)
      ⟨50, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨50, by decide⟩ (Q2.listedAt ⟨50, by decide⟩
        (alnCheck_rep ⟨50, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 10 hp) Q2.T50_50_2 Q2.hfix50_50_2 Q2.hinj50_50_2
      Q2.hcardT50_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T50_50_2 i) (Q2.hfix50_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨50, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T50_50 = colFn colCert_50_50_10.D (m := 25) from colCert_50_50_10.bind1,
    show colData2 (⟨50, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 10 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T50_50_2 = colFn colCert_50_50_10.D (m := 25) from colCert_50_50_10.bind2]
  exact alnAll_50_50_10 j hj hq

theorem leaf_50_50_15 (hp : 15 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 50 []).length)
    (hq : (normIsRep.getD 50 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 15 hp)
        (rowE2 (⟨50, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp))
        (rowE1 (⟨50, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨50, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨50, by decide⟩ (listedAt ⟨50, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp)) T50_50
      hfix50_50 hinj50_50 hcardT50_50
      (fun i => conj_mem_of_fixedPoints _ _ (T50_50 i) (hfix50_50 i) _)
      ⟨50, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨50, by decide⟩ (Q2.listedAt ⟨50, by decide⟩
        (alnCheck_rep ⟨50, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 15 hp) Q2.T50_50_2 Q2.hfix50_50_2 Q2.hinj50_50_2
      Q2.hcardT50_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T50_50_2 i) (Q2.hfix50_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨50, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T50_50 = colFn colCert_50_50_15.D (m := 25) from colCert_50_50_15.bind1,
    show colData2 (⟨50, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 15 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T50_50_2 = colFn colCert_50_50_15.D (m := 25) from colCert_50_50_15.bind2]
  exact alnAll_50_50_15 j hj hq

theorem leaf_50_50_20 (hp : 20 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 50 []).length)
    (hq : (normIsRep.getD 50 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 20 hp)
        (rowE2 (⟨50, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp))
        (rowE1 (⟨50, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨50, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨50, by decide⟩ (listedAt ⟨50, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp)) T50_50
      hfix50_50 hinj50_50 hcardT50_50
      (fun i => conj_mem_of_fixedPoints _ _ (T50_50 i) (hfix50_50 i) _)
      ⟨50, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨50, by decide⟩ (Q2.listedAt ⟨50, by decide⟩
        (alnCheck_rep ⟨50, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 20 hp) Q2.T50_50_2 Q2.hfix50_50_2 Q2.hinj50_50_2
      Q2.hcardT50_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T50_50_2 i) (Q2.hfix50_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨50, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T50_50 = colFn colCert_50_50_20.D (m := 25) from colCert_50_50_20.bind1,
    show colData2 (⟨50, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 20 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T50_50_2 = colFn colCert_50_50_20.D (m := 25) from colCert_50_50_20.bind2]
  exact alnAll_50_50_20 j hj hq

theorem leaf_51_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 51 []).length)
    (hq : (normIsRep.getD 51 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨51, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨51, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨51, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨51, by decide⟩ (listedAt ⟨51, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T51_12
      hfix51_12 hinj51_12 hcardT51_12
      (fun i => conj_mem_of_fixedPoints _ _ (T51_12 i) (hfix51_12 i) _)
      ⟨51, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨51, by decide⟩ (Q2.listedAt ⟨51, by decide⟩
        (alnCheck_rep ⟨51, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T51_12_2 Q2.hfix51_12_2 Q2.hinj51_12_2
      Q2.hcardT51_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T51_12_2 i) (Q2.hfix51_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨51, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T51_12 = colFn colCert_51_12_0.D (m := 125) from colCert_51_12_0.bind1,
    show colData2 (⟨51, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T51_12_2 = colFn colCert_51_12_0.D (m := 125) from colCert_51_12_0.bind2]
  exact alnAll_51_12_0 j hj hq

theorem leaf_51_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 51 []).length)
    (hq : (normIsRep.getD 51 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨51, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨51, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨51, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨51, by decide⟩ (listedAt ⟨51, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T51_12
      hfix51_12 hinj51_12 hcardT51_12
      (fun i => conj_mem_of_fixedPoints _ _ (T51_12 i) (hfix51_12 i) _)
      ⟨51, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨51, by decide⟩ (Q2.listedAt ⟨51, by decide⟩
        (alnCheck_rep ⟨51, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T51_12_2 Q2.hfix51_12_2 Q2.hinj51_12_2
      Q2.hcardT51_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T51_12_2 i) (Q2.hfix51_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨51, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T51_12 = colFn colCert_51_12_1.D (m := 125) from colCert_51_12_1.bind1,
    show colData2 (⟨51, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T51_12_2 = colFn colCert_51_12_1.D (m := 125) from colCert_51_12_1.bind2]
  exact alnAll_51_12_1 j hj hq

theorem leaf_51_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 51 []).length)
    (hq : (normIsRep.getD 51 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨51, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨51, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨51, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨51, by decide⟩ (listedAt ⟨51, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T51_12
      hfix51_12 hinj51_12 hcardT51_12
      (fun i => conj_mem_of_fixedPoints _ _ (T51_12 i) (hfix51_12 i) _)
      ⟨51, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨51, by decide⟩ (Q2.listedAt ⟨51, by decide⟩
        (alnCheck_rep ⟨51, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T51_12_2 Q2.hfix51_12_2 Q2.hinj51_12_2
      Q2.hcardT51_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T51_12_2 i) (Q2.hfix51_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨51, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T51_12 = colFn colCert_51_12_2.D (m := 125) from colCert_51_12_2.bind1,
    show colData2 (⟨51, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T51_12_2 = colFn colCert_51_12_2.D (m := 125) from colCert_51_12_2.bind2]
  exact alnAll_51_12_2 j hj hq

theorem leaf_51_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 51 []).length)
    (hq : (normIsRep.getD 51 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨51, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨51, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨51, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨51, by decide⟩ (listedAt ⟨51, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T51_12
      hfix51_12 hinj51_12 hcardT51_12
      (fun i => conj_mem_of_fixedPoints _ _ (T51_12 i) (hfix51_12 i) _)
      ⟨51, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨51, by decide⟩ (Q2.listedAt ⟨51, by decide⟩
        (alnCheck_rep ⟨51, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T51_12_2 Q2.hfix51_12_2 Q2.hinj51_12_2
      Q2.hcardT51_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T51_12_2 i) (Q2.hfix51_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨51, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T51_12 = colFn colCert_51_12_3.D (m := 125) from colCert_51_12_3.bind1,
    show colData2 (⟨51, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T51_12_2 = colFn colCert_51_12_3.D (m := 125) from colCert_51_12_3.bind2]
  exact alnAll_51_12_3 j hj hq

theorem leaf_51_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 51 []).length)
    (hq : (normIsRep.getD 51 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨51, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨51, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨51, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨51, by decide⟩ (listedAt ⟨51, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T51_12
      hfix51_12 hinj51_12 hcardT51_12
      (fun i => conj_mem_of_fixedPoints _ _ (T51_12 i) (hfix51_12 i) _)
      ⟨51, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨51, by decide⟩ (Q2.listedAt ⟨51, by decide⟩
        (alnCheck_rep ⟨51, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T51_12_2 Q2.hfix51_12_2 Q2.hinj51_12_2
      Q2.hcardT51_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T51_12_2 i) (Q2.hfix51_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨51, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T51_12 = colFn colCert_51_12_4.D (m := 125) from colCert_51_12_4.bind1,
    show colData2 (⟨51, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T51_12_2 = colFn colCert_51_12_4.D (m := 125) from colCert_51_12_4.bind2]
  exact alnAll_51_12_4 j hj hq

theorem leaf_51_51_0 (hp : 0 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 51 []).length)
    (hq : (normIsRep.getD 51 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 0 hp)
        (rowE2 (⟨51, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp))
        (rowE1 (⟨51, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨51, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨51, by decide⟩ (listedAt ⟨51, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp)) T51_51
      hfix51_51 hinj51_51 hcardT51_51
      (fun i => conj_mem_of_fixedPoints _ _ (T51_51 i) (hfix51_51 i) _)
      ⟨51, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨51, by decide⟩ (Q2.listedAt ⟨51, by decide⟩
        (alnCheck_rep ⟨51, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 0 hp) Q2.T51_51_2 Q2.hfix51_51_2 Q2.hinj51_51_2
      Q2.hcardT51_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T51_51_2 i) (Q2.hfix51_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨51, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T51_51 = colFn colCert_51_51_0.D (m := 25) from colCert_51_51_0.bind1,
    show colData2 (⟨51, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 0 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T51_51_2 = colFn colCert_51_51_0.D (m := 25) from colCert_51_51_0.bind2]
  exact alnAll_51_51_0 j hj hq

theorem leaf_51_51_1 (hp : 1 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 51 []).length)
    (hq : (normIsRep.getD 51 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 1 hp)
        (rowE2 (⟨51, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp))
        (rowE1 (⟨51, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨51, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨51, by decide⟩ (listedAt ⟨51, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp)) T51_51
      hfix51_51 hinj51_51 hcardT51_51
      (fun i => conj_mem_of_fixedPoints _ _ (T51_51 i) (hfix51_51 i) _)
      ⟨51, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨51, by decide⟩ (Q2.listedAt ⟨51, by decide⟩
        (alnCheck_rep ⟨51, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 1 hp) Q2.T51_51_2 Q2.hfix51_51_2 Q2.hinj51_51_2
      Q2.hcardT51_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T51_51_2 i) (Q2.hfix51_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨51, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T51_51 = colFn colCert_51_51_1.D (m := 25) from colCert_51_51_1.bind1,
    show colData2 (⟨51, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 1 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T51_51_2 = colFn colCert_51_51_1.D (m := 25) from colCert_51_51_1.bind2]
  exact alnAll_51_51_1 j hj hq

theorem leaf_51_51_2 (hp : 2 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 51 []).length)
    (hq : (normIsRep.getD 51 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 2 hp)
        (rowE2 (⟨51, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp))
        (rowE1 (⟨51, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨51, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨51, by decide⟩ (listedAt ⟨51, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp)) T51_51
      hfix51_51 hinj51_51 hcardT51_51
      (fun i => conj_mem_of_fixedPoints _ _ (T51_51 i) (hfix51_51 i) _)
      ⟨51, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨51, by decide⟩ (Q2.listedAt ⟨51, by decide⟩
        (alnCheck_rep ⟨51, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 2 hp) Q2.T51_51_2 Q2.hfix51_51_2 Q2.hinj51_51_2
      Q2.hcardT51_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T51_51_2 i) (Q2.hfix51_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨51, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T51_51 = colFn colCert_51_51_2.D (m := 25) from colCert_51_51_2.bind1,
    show colData2 (⟨51, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 2 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T51_51_2 = colFn colCert_51_51_2.D (m := 25) from colCert_51_51_2.bind2]
  exact alnAll_51_51_2 j hj hq

theorem leaf_51_51_3 (hp : 3 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 51 []).length)
    (hq : (normIsRep.getD 51 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 3 hp)
        (rowE2 (⟨51, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp))
        (rowE1 (⟨51, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨51, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨51, by decide⟩ (listedAt ⟨51, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp)) T51_51
      hfix51_51 hinj51_51 hcardT51_51
      (fun i => conj_mem_of_fixedPoints _ _ (T51_51 i) (hfix51_51 i) _)
      ⟨51, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨51, by decide⟩ (Q2.listedAt ⟨51, by decide⟩
        (alnCheck_rep ⟨51, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 3 hp) Q2.T51_51_2 Q2.hfix51_51_2 Q2.hinj51_51_2
      Q2.hcardT51_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T51_51_2 i) (Q2.hfix51_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨51, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T51_51 = colFn colCert_51_51_3.D (m := 25) from colCert_51_51_3.bind1,
    show colData2 (⟨51, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 3 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T51_51_2 = colFn colCert_51_51_3.D (m := 25) from colCert_51_51_3.bind2]
  exact alnAll_51_51_3 j hj hq

theorem leaf_51_51_4 (hp : 4 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 51 []).length)
    (hq : (normIsRep.getD 51 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 4 hp)
        (rowE2 (⟨51, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp))
        (rowE1 (⟨51, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨51, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨51, by decide⟩ (listedAt ⟨51, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp)) T51_51
      hfix51_51 hinj51_51 hcardT51_51
      (fun i => conj_mem_of_fixedPoints _ _ (T51_51 i) (hfix51_51 i) _)
      ⟨51, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨51, by decide⟩ (Q2.listedAt ⟨51, by decide⟩
        (alnCheck_rep ⟨51, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 4 hp) Q2.T51_51_2 Q2.hfix51_51_2 Q2.hinj51_51_2
      Q2.hcardT51_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T51_51_2 i) (Q2.hfix51_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨51, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T51_51 = colFn colCert_51_51_4.D (m := 25) from colCert_51_51_4.bind1,
    show colData2 (⟨51, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 4 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T51_51_2 = colFn colCert_51_51_4.D (m := 25) from colCert_51_51_4.bind2]
  exact alnAll_51_51_4 j hj hq

theorem leaf_51_51_5 (hp : 5 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 51 []).length)
    (hq : (normIsRep.getD 51 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 5 hp)
        (rowE2 (⟨51, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp))
        (rowE1 (⟨51, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨51, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨51, by decide⟩ (listedAt ⟨51, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp)) T51_51
      hfix51_51 hinj51_51 hcardT51_51
      (fun i => conj_mem_of_fixedPoints _ _ (T51_51 i) (hfix51_51 i) _)
      ⟨51, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨51, by decide⟩ (Q2.listedAt ⟨51, by decide⟩
        (alnCheck_rep ⟨51, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 5 hp) Q2.T51_51_2 Q2.hfix51_51_2 Q2.hinj51_51_2
      Q2.hcardT51_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T51_51_2 i) (Q2.hfix51_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨51, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T51_51 = colFn colCert_51_51_5.D (m := 25) from colCert_51_51_5.bind1,
    show colData2 (⟨51, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 5 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T51_51_2 = colFn colCert_51_51_5.D (m := 25) from colCert_51_51_5.bind2]
  exact alnAll_51_51_5 j hj hq

theorem leaf_51_51_10 (hp : 10 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 51 []).length)
    (hq : (normIsRep.getD 51 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 10 hp)
        (rowE2 (⟨51, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp))
        (rowE1 (⟨51, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨51, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨51, by decide⟩ (listedAt ⟨51, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp)) T51_51
      hfix51_51 hinj51_51 hcardT51_51
      (fun i => conj_mem_of_fixedPoints _ _ (T51_51 i) (hfix51_51 i) _)
      ⟨51, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨51, by decide⟩ (Q2.listedAt ⟨51, by decide⟩
        (alnCheck_rep ⟨51, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 10 hp) Q2.T51_51_2 Q2.hfix51_51_2 Q2.hinj51_51_2
      Q2.hcardT51_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T51_51_2 i) (Q2.hfix51_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨51, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T51_51 = colFn colCert_51_51_10.D (m := 25) from colCert_51_51_10.bind1,
    show colData2 (⟨51, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 10 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T51_51_2 = colFn colCert_51_51_10.D (m := 25) from colCert_51_51_10.bind2]
  exact alnAll_51_51_10 j hj hq

theorem leaf_51_51_15 (hp : 15 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 51 []).length)
    (hq : (normIsRep.getD 51 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 15 hp)
        (rowE2 (⟨51, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp))
        (rowE1 (⟨51, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨51, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨51, by decide⟩ (listedAt ⟨51, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp)) T51_51
      hfix51_51 hinj51_51 hcardT51_51
      (fun i => conj_mem_of_fixedPoints _ _ (T51_51 i) (hfix51_51 i) _)
      ⟨51, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨51, by decide⟩ (Q2.listedAt ⟨51, by decide⟩
        (alnCheck_rep ⟨51, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 15 hp) Q2.T51_51_2 Q2.hfix51_51_2 Q2.hinj51_51_2
      Q2.hcardT51_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T51_51_2 i) (Q2.hfix51_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨51, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T51_51 = colFn colCert_51_51_15.D (m := 25) from colCert_51_51_15.bind1,
    show colData2 (⟨51, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 15 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T51_51_2 = colFn colCert_51_51_15.D (m := 25) from colCert_51_51_15.bind2]
  exact alnAll_51_51_15 j hj hq

theorem leaf_51_51_20 (hp : 20 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 51 []).length)
    (hq : (normIsRep.getD 51 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 20 hp)
        (rowE2 (⟨51, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp))
        (rowE1 (⟨51, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨51, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨51, by decide⟩ (listedAt ⟨51, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp)) T51_51
      hfix51_51 hinj51_51 hcardT51_51
      (fun i => conj_mem_of_fixedPoints _ _ (T51_51 i) (hfix51_51 i) _)
      ⟨51, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨51, by decide⟩ (Q2.listedAt ⟨51, by decide⟩
        (alnCheck_rep ⟨51, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 20 hp) Q2.T51_51_2 Q2.hfix51_51_2 Q2.hinj51_51_2
      Q2.hcardT51_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T51_51_2 i) (Q2.hfix51_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨51, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T51_51 = colFn colCert_51_51_20.D (m := 25) from colCert_51_51_20.bind1,
    show colData2 (⟨51, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 20 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T51_51_2 = colFn colCert_51_51_20.D (m := 25) from colCert_51_51_20.bind2]
  exact alnAll_51_51_20 j hj hq

theorem leaf_52_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 52 []).length)
    (hq : (normIsRep.getD 52 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨52, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨52, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨52, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨52, by decide⟩ (listedAt ⟨52, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T52_12
      hfix52_12 hinj52_12 hcardT52_12
      (fun i => conj_mem_of_fixedPoints _ _ (T52_12 i) (hfix52_12 i) _)
      ⟨52, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨52, by decide⟩ (Q2.listedAt ⟨52, by decide⟩
        (alnCheck_rep ⟨52, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T52_12_2 Q2.hfix52_12_2 Q2.hinj52_12_2
      Q2.hcardT52_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T52_12_2 i) (Q2.hfix52_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨52, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T52_12 = colFn colCert_52_12_0.D (m := 125) from colCert_52_12_0.bind1,
    show colData2 (⟨52, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T52_12_2 = colFn colCert_52_12_0.D (m := 125) from colCert_52_12_0.bind2]
  exact alnAll_52_12_0 j hj hq

theorem leaf_52_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 52 []).length)
    (hq : (normIsRep.getD 52 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨52, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨52, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨52, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨52, by decide⟩ (listedAt ⟨52, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T52_12
      hfix52_12 hinj52_12 hcardT52_12
      (fun i => conj_mem_of_fixedPoints _ _ (T52_12 i) (hfix52_12 i) _)
      ⟨52, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨52, by decide⟩ (Q2.listedAt ⟨52, by decide⟩
        (alnCheck_rep ⟨52, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T52_12_2 Q2.hfix52_12_2 Q2.hinj52_12_2
      Q2.hcardT52_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T52_12_2 i) (Q2.hfix52_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨52, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T52_12 = colFn colCert_52_12_1.D (m := 125) from colCert_52_12_1.bind1,
    show colData2 (⟨52, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T52_12_2 = colFn colCert_52_12_1.D (m := 125) from colCert_52_12_1.bind2]
  exact alnAll_52_12_1 j hj hq

theorem leaf_52_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 52 []).length)
    (hq : (normIsRep.getD 52 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨52, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨52, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨52, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨52, by decide⟩ (listedAt ⟨52, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T52_12
      hfix52_12 hinj52_12 hcardT52_12
      (fun i => conj_mem_of_fixedPoints _ _ (T52_12 i) (hfix52_12 i) _)
      ⟨52, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨52, by decide⟩ (Q2.listedAt ⟨52, by decide⟩
        (alnCheck_rep ⟨52, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T52_12_2 Q2.hfix52_12_2 Q2.hinj52_12_2
      Q2.hcardT52_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T52_12_2 i) (Q2.hfix52_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨52, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T52_12 = colFn colCert_52_12_2.D (m := 125) from colCert_52_12_2.bind1,
    show colData2 (⟨52, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T52_12_2 = colFn colCert_52_12_2.D (m := 125) from colCert_52_12_2.bind2]
  exact alnAll_52_12_2 j hj hq

theorem leaf_52_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 52 []).length)
    (hq : (normIsRep.getD 52 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨52, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨52, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨52, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨52, by decide⟩ (listedAt ⟨52, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T52_12
      hfix52_12 hinj52_12 hcardT52_12
      (fun i => conj_mem_of_fixedPoints _ _ (T52_12 i) (hfix52_12 i) _)
      ⟨52, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨52, by decide⟩ (Q2.listedAt ⟨52, by decide⟩
        (alnCheck_rep ⟨52, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T52_12_2 Q2.hfix52_12_2 Q2.hinj52_12_2
      Q2.hcardT52_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T52_12_2 i) (Q2.hfix52_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨52, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T52_12 = colFn colCert_52_12_3.D (m := 125) from colCert_52_12_3.bind1,
    show colData2 (⟨52, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T52_12_2 = colFn colCert_52_12_3.D (m := 125) from colCert_52_12_3.bind2]
  exact alnAll_52_12_3 j hj hq

theorem leaf_52_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 52 []).length)
    (hq : (normIsRep.getD 52 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨52, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨52, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨52, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨52, by decide⟩ (listedAt ⟨52, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T52_12
      hfix52_12 hinj52_12 hcardT52_12
      (fun i => conj_mem_of_fixedPoints _ _ (T52_12 i) (hfix52_12 i) _)
      ⟨52, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨52, by decide⟩ (Q2.listedAt ⟨52, by decide⟩
        (alnCheck_rep ⟨52, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T52_12_2 Q2.hfix52_12_2 Q2.hinj52_12_2
      Q2.hcardT52_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T52_12_2 i) (Q2.hfix52_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨52, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T52_12 = colFn colCert_52_12_4.D (m := 125) from colCert_52_12_4.bind1,
    show colData2 (⟨52, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T52_12_2 = colFn colCert_52_12_4.D (m := 125) from colCert_52_12_4.bind2]
  exact alnAll_52_12_4 j hj hq

theorem leaf_52_52_0 (hp : 0 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 52 []).length)
    (hq : (normIsRep.getD 52 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 0 hp)
        (rowE2 (⟨52, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp))
        (rowE1 (⟨52, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨52, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨52, by decide⟩ (listedAt ⟨52, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp)) T52_52
      hfix52_52 hinj52_52 hcardT52_52
      (fun i => conj_mem_of_fixedPoints _ _ (T52_52 i) (hfix52_52 i) _)
      ⟨52, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨52, by decide⟩ (Q2.listedAt ⟨52, by decide⟩
        (alnCheck_rep ⟨52, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 0 hp) Q2.T52_52_2 Q2.hfix52_52_2 Q2.hinj52_52_2
      Q2.hcardT52_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T52_52_2 i) (Q2.hfix52_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨52, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T52_52 = colFn colCert_52_52_0.D (m := 25) from colCert_52_52_0.bind1,
    show colData2 (⟨52, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 0 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T52_52_2 = colFn colCert_52_52_0.D (m := 25) from colCert_52_52_0.bind2]
  exact alnAll_52_52_0 j hj hq

theorem leaf_52_52_1 (hp : 1 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 52 []).length)
    (hq : (normIsRep.getD 52 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 1 hp)
        (rowE2 (⟨52, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp))
        (rowE1 (⟨52, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨52, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨52, by decide⟩ (listedAt ⟨52, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp)) T52_52
      hfix52_52 hinj52_52 hcardT52_52
      (fun i => conj_mem_of_fixedPoints _ _ (T52_52 i) (hfix52_52 i) _)
      ⟨52, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨52, by decide⟩ (Q2.listedAt ⟨52, by decide⟩
        (alnCheck_rep ⟨52, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 1 hp) Q2.T52_52_2 Q2.hfix52_52_2 Q2.hinj52_52_2
      Q2.hcardT52_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T52_52_2 i) (Q2.hfix52_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨52, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T52_52 = colFn colCert_52_52_1.D (m := 25) from colCert_52_52_1.bind1,
    show colData2 (⟨52, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 1 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T52_52_2 = colFn colCert_52_52_1.D (m := 25) from colCert_52_52_1.bind2]
  exact alnAll_52_52_1 j hj hq

theorem leaf_52_52_2 (hp : 2 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 52 []).length)
    (hq : (normIsRep.getD 52 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 2 hp)
        (rowE2 (⟨52, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp))
        (rowE1 (⟨52, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨52, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨52, by decide⟩ (listedAt ⟨52, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp)) T52_52
      hfix52_52 hinj52_52 hcardT52_52
      (fun i => conj_mem_of_fixedPoints _ _ (T52_52 i) (hfix52_52 i) _)
      ⟨52, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨52, by decide⟩ (Q2.listedAt ⟨52, by decide⟩
        (alnCheck_rep ⟨52, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 2 hp) Q2.T52_52_2 Q2.hfix52_52_2 Q2.hinj52_52_2
      Q2.hcardT52_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T52_52_2 i) (Q2.hfix52_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨52, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T52_52 = colFn colCert_52_52_2.D (m := 25) from colCert_52_52_2.bind1,
    show colData2 (⟨52, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 2 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T52_52_2 = colFn colCert_52_52_2.D (m := 25) from colCert_52_52_2.bind2]
  exact alnAll_52_52_2 j hj hq

theorem leaf_52_52_3 (hp : 3 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 52 []).length)
    (hq : (normIsRep.getD 52 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 3 hp)
        (rowE2 (⟨52, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp))
        (rowE1 (⟨52, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨52, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨52, by decide⟩ (listedAt ⟨52, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp)) T52_52
      hfix52_52 hinj52_52 hcardT52_52
      (fun i => conj_mem_of_fixedPoints _ _ (T52_52 i) (hfix52_52 i) _)
      ⟨52, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨52, by decide⟩ (Q2.listedAt ⟨52, by decide⟩
        (alnCheck_rep ⟨52, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 3 hp) Q2.T52_52_2 Q2.hfix52_52_2 Q2.hinj52_52_2
      Q2.hcardT52_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T52_52_2 i) (Q2.hfix52_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨52, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T52_52 = colFn colCert_52_52_3.D (m := 25) from colCert_52_52_3.bind1,
    show colData2 (⟨52, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 3 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T52_52_2 = colFn colCert_52_52_3.D (m := 25) from colCert_52_52_3.bind2]
  exact alnAll_52_52_3 j hj hq

theorem leaf_52_52_4 (hp : 4 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 52 []).length)
    (hq : (normIsRep.getD 52 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 4 hp)
        (rowE2 (⟨52, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp))
        (rowE1 (⟨52, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨52, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨52, by decide⟩ (listedAt ⟨52, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp)) T52_52
      hfix52_52 hinj52_52 hcardT52_52
      (fun i => conj_mem_of_fixedPoints _ _ (T52_52 i) (hfix52_52 i) _)
      ⟨52, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨52, by decide⟩ (Q2.listedAt ⟨52, by decide⟩
        (alnCheck_rep ⟨52, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 4 hp) Q2.T52_52_2 Q2.hfix52_52_2 Q2.hinj52_52_2
      Q2.hcardT52_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T52_52_2 i) (Q2.hfix52_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨52, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T52_52 = colFn colCert_52_52_4.D (m := 25) from colCert_52_52_4.bind1,
    show colData2 (⟨52, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 4 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T52_52_2 = colFn colCert_52_52_4.D (m := 25) from colCert_52_52_4.bind2]
  exact alnAll_52_52_4 j hj hq

theorem leaf_52_52_5 (hp : 5 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 52 []).length)
    (hq : (normIsRep.getD 52 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 5 hp)
        (rowE2 (⟨52, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp))
        (rowE1 (⟨52, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨52, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨52, by decide⟩ (listedAt ⟨52, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp)) T52_52
      hfix52_52 hinj52_52 hcardT52_52
      (fun i => conj_mem_of_fixedPoints _ _ (T52_52 i) (hfix52_52 i) _)
      ⟨52, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨52, by decide⟩ (Q2.listedAt ⟨52, by decide⟩
        (alnCheck_rep ⟨52, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 5 hp) Q2.T52_52_2 Q2.hfix52_52_2 Q2.hinj52_52_2
      Q2.hcardT52_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T52_52_2 i) (Q2.hfix52_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨52, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T52_52 = colFn colCert_52_52_5.D (m := 25) from colCert_52_52_5.bind1,
    show colData2 (⟨52, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 5 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T52_52_2 = colFn colCert_52_52_5.D (m := 25) from colCert_52_52_5.bind2]
  exact alnAll_52_52_5 j hj hq

theorem leaf_52_52_10 (hp : 10 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 52 []).length)
    (hq : (normIsRep.getD 52 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 10 hp)
        (rowE2 (⟨52, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp))
        (rowE1 (⟨52, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨52, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨52, by decide⟩ (listedAt ⟨52, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp)) T52_52
      hfix52_52 hinj52_52 hcardT52_52
      (fun i => conj_mem_of_fixedPoints _ _ (T52_52 i) (hfix52_52 i) _)
      ⟨52, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨52, by decide⟩ (Q2.listedAt ⟨52, by decide⟩
        (alnCheck_rep ⟨52, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 10 hp) Q2.T52_52_2 Q2.hfix52_52_2 Q2.hinj52_52_2
      Q2.hcardT52_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T52_52_2 i) (Q2.hfix52_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨52, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T52_52 = colFn colCert_52_52_10.D (m := 25) from colCert_52_52_10.bind1,
    show colData2 (⟨52, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 10 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T52_52_2 = colFn colCert_52_52_10.D (m := 25) from colCert_52_52_10.bind2]
  exact alnAll_52_52_10 j hj hq

theorem leaf_52_52_15 (hp : 15 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 52 []).length)
    (hq : (normIsRep.getD 52 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 15 hp)
        (rowE2 (⟨52, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp))
        (rowE1 (⟨52, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨52, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨52, by decide⟩ (listedAt ⟨52, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp)) T52_52
      hfix52_52 hinj52_52 hcardT52_52
      (fun i => conj_mem_of_fixedPoints _ _ (T52_52 i) (hfix52_52 i) _)
      ⟨52, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨52, by decide⟩ (Q2.listedAt ⟨52, by decide⟩
        (alnCheck_rep ⟨52, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 15 hp) Q2.T52_52_2 Q2.hfix52_52_2 Q2.hinj52_52_2
      Q2.hcardT52_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T52_52_2 i) (Q2.hfix52_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨52, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T52_52 = colFn colCert_52_52_15.D (m := 25) from colCert_52_52_15.bind1,
    show colData2 (⟨52, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 15 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T52_52_2 = colFn colCert_52_52_15.D (m := 25) from colCert_52_52_15.bind2]
  exact alnAll_52_52_15 j hj hq

theorem leaf_52_52_20 (hp : 20 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 52 []).length)
    (hq : (normIsRep.getD 52 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 20 hp)
        (rowE2 (⟨52, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp))
        (rowE1 (⟨52, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨52, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨52, by decide⟩ (listedAt ⟨52, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp)) T52_52
      hfix52_52 hinj52_52 hcardT52_52
      (fun i => conj_mem_of_fixedPoints _ _ (T52_52 i) (hfix52_52 i) _)
      ⟨52, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨52, by decide⟩ (Q2.listedAt ⟨52, by decide⟩
        (alnCheck_rep ⟨52, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 20 hp) Q2.T52_52_2 Q2.hfix52_52_2 Q2.hinj52_52_2
      Q2.hcardT52_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T52_52_2 i) (Q2.hfix52_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨52, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T52_52 = colFn colCert_52_52_20.D (m := 25) from colCert_52_52_20.bind1,
    show colData2 (⟨52, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 20 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T52_52_2 = colFn colCert_52_52_20.D (m := 25) from colCert_52_52_20.bind2]
  exact alnAll_52_52_20 j hj hq

theorem leaf_53_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 53 []).length)
    (hq : (normIsRep.getD 53 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨53, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨53, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨53, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨53, by decide⟩ (listedAt ⟨53, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T53_10
      hfix53_10 hinj53_10 hcardT53_10
      (fun i => conj_mem_of_fixedPoints _ _ (T53_10 i) (hfix53_10 i) _)
      ⟨53, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨53, by decide⟩ (Q2.listedAt ⟨53, by decide⟩
        (alnCheck_rep ⟨53, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T53_10_2 Q2.hfix53_10_2 Q2.hinj53_10_2
      Q2.hcardT53_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T53_10_2 i) (Q2.hfix53_10_2 i) _)
      colCert_53_10_0.hD ?_).symm
  rw [alnId_53 j hj]


theorem leaf_53_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 53 []).length)
    (hq : (normIsRep.getD 53 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨53, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨53, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨53, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨53, by decide⟩ (listedAt ⟨53, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T53_10
      hfix53_10 hinj53_10 hcardT53_10
      (fun i => conj_mem_of_fixedPoints _ _ (T53_10 i) (hfix53_10 i) _)
      ⟨53, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨53, by decide⟩ (Q2.listedAt ⟨53, by decide⟩
        (alnCheck_rep ⟨53, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T53_10_2 Q2.hfix53_10_2 Q2.hinj53_10_2
      Q2.hcardT53_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T53_10_2 i) (Q2.hfix53_10_2 i) _)
      colCert_53_10_1.hD ?_).symm
  rw [alnId_53 j hj]


theorem leaf_53_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 53 []).length)
    (hq : (normIsRep.getD 53 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨53, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨53, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨53, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨53, by decide⟩ (listedAt ⟨53, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T53_10
      hfix53_10 hinj53_10 hcardT53_10
      (fun i => conj_mem_of_fixedPoints _ _ (T53_10 i) (hfix53_10 i) _)
      ⟨53, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨53, by decide⟩ (Q2.listedAt ⟨53, by decide⟩
        (alnCheck_rep ⟨53, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T53_10_2 Q2.hfix53_10_2 Q2.hinj53_10_2
      Q2.hcardT53_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T53_10_2 i) (Q2.hfix53_10_2 i) _)
      colCert_53_10_2.hD ?_).symm
  rw [alnId_53 j hj]


theorem leaf_53_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 53 []).length)
    (hq : (normIsRep.getD 53 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨53, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨53, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨53, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨53, by decide⟩ (listedAt ⟨53, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T53_10
      hfix53_10 hinj53_10 hcardT53_10
      (fun i => conj_mem_of_fixedPoints _ _ (T53_10 i) (hfix53_10 i) _)
      ⟨53, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨53, by decide⟩ (Q2.listedAt ⟨53, by decide⟩
        (alnCheck_rep ⟨53, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T53_10_2 Q2.hfix53_10_2 Q2.hinj53_10_2
      Q2.hcardT53_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T53_10_2 i) (Q2.hfix53_10_2 i) _)
      colCert_53_10_3.hD ?_).symm
  rw [alnId_53 j hj]


theorem leaf_53_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 53 []).length)
    (hq : (normIsRep.getD 53 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨53, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨53, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨53, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨53, by decide⟩ (listedAt ⟨53, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T53_10
      hfix53_10 hinj53_10 hcardT53_10
      (fun i => conj_mem_of_fixedPoints _ _ (T53_10 i) (hfix53_10 i) _)
      ⟨53, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨53, by decide⟩ (Q2.listedAt ⟨53, by decide⟩
        (alnCheck_rep ⟨53, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T53_10_2 Q2.hfix53_10_2 Q2.hinj53_10_2
      Q2.hcardT53_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T53_10_2 i) (Q2.hfix53_10_2 i) _)
      colCert_53_10_4.hD ?_).symm
  rw [alnId_53 j hj]


theorem leaf_53_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 53 []).length)
    (hq : (normIsRep.getD 53 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨53, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨53, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨53, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨53, by decide⟩ (listedAt ⟨53, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T53_12
      hfix53_12 hinj53_12 hcardT53_12
      (fun i => conj_mem_of_fixedPoints _ _ (T53_12 i) (hfix53_12 i) _)
      ⟨53, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨53, by decide⟩ (Q2.listedAt ⟨53, by decide⟩
        (alnCheck_rep ⟨53, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T53_12_2 Q2.hfix53_12_2 Q2.hinj53_12_2
      Q2.hcardT53_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T53_12_2 i) (Q2.hfix53_12_2 i) _)
      colCert_53_12_0.hD ?_).symm
  rw [alnId_53 j hj]


theorem leaf_53_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 53 []).length)
    (hq : (normIsRep.getD 53 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨53, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨53, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨53, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨53, by decide⟩ (listedAt ⟨53, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T53_12
      hfix53_12 hinj53_12 hcardT53_12
      (fun i => conj_mem_of_fixedPoints _ _ (T53_12 i) (hfix53_12 i) _)
      ⟨53, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨53, by decide⟩ (Q2.listedAt ⟨53, by decide⟩
        (alnCheck_rep ⟨53, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T53_12_2 Q2.hfix53_12_2 Q2.hinj53_12_2
      Q2.hcardT53_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T53_12_2 i) (Q2.hfix53_12_2 i) _)
      colCert_53_12_1.hD ?_).symm
  rw [alnId_53 j hj]


theorem leaf_53_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 53 []).length)
    (hq : (normIsRep.getD 53 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨53, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨53, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨53, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨53, by decide⟩ (listedAt ⟨53, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T53_12
      hfix53_12 hinj53_12 hcardT53_12
      (fun i => conj_mem_of_fixedPoints _ _ (T53_12 i) (hfix53_12 i) _)
      ⟨53, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨53, by decide⟩ (Q2.listedAt ⟨53, by decide⟩
        (alnCheck_rep ⟨53, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T53_12_2 Q2.hfix53_12_2 Q2.hinj53_12_2
      Q2.hcardT53_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T53_12_2 i) (Q2.hfix53_12_2 i) _)
      colCert_53_12_2.hD ?_).symm
  rw [alnId_53 j hj]


theorem leaf_53_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 53 []).length)
    (hq : (normIsRep.getD 53 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨53, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨53, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨53, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨53, by decide⟩ (listedAt ⟨53, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T53_12
      hfix53_12 hinj53_12 hcardT53_12
      (fun i => conj_mem_of_fixedPoints _ _ (T53_12 i) (hfix53_12 i) _)
      ⟨53, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨53, by decide⟩ (Q2.listedAt ⟨53, by decide⟩
        (alnCheck_rep ⟨53, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T53_12_2 Q2.hfix53_12_2 Q2.hinj53_12_2
      Q2.hcardT53_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T53_12_2 i) (Q2.hfix53_12_2 i) _)
      colCert_53_12_3.hD ?_).symm
  rw [alnId_53 j hj]


theorem leaf_53_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 53 []).length)
    (hq : (normIsRep.getD 53 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨53, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨53, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨53, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨53, by decide⟩ (listedAt ⟨53, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T53_12
      hfix53_12 hinj53_12 hcardT53_12
      (fun i => conj_mem_of_fixedPoints _ _ (T53_12 i) (hfix53_12 i) _)
      ⟨53, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨53, by decide⟩ (Q2.listedAt ⟨53, by decide⟩
        (alnCheck_rep ⟨53, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T53_12_2 Q2.hfix53_12_2 Q2.hinj53_12_2
      Q2.hcardT53_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T53_12_2 i) (Q2.hfix53_12_2 i) _)
      colCert_53_12_4.hD ?_).symm
  rw [alnId_53 j hj]


theorem leaf_53_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 53 []).length)
    (hq : (normIsRep.getD 53 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨53, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨53, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨53, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨53, by decide⟩ (listedAt ⟨53, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T53_53
      hfix53_53 hinj53_53 hcardT53_53
      (fun i => conj_mem_of_fixedPoints _ _ (T53_53 i) (hfix53_53 i) _)
      ⟨53, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨53, by decide⟩ (Q2.listedAt ⟨53, by decide⟩
        (alnCheck_rep ⟨53, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T53_53_2 Q2.hfix53_53_2 Q2.hinj53_53_2
      Q2.hcardT53_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T53_53_2 i) (Q2.hfix53_53_2 i) _)
      colCert_53_53_0.hD ?_).symm
  rw [alnId_53 j hj]


theorem leaf_53_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 53 []).length)
    (hq : (normIsRep.getD 53 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨53, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨53, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨53, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨53, by decide⟩ (listedAt ⟨53, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T53_53
      hfix53_53 hinj53_53 hcardT53_53
      (fun i => conj_mem_of_fixedPoints _ _ (T53_53 i) (hfix53_53 i) _)
      ⟨53, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨53, by decide⟩ (Q2.listedAt ⟨53, by decide⟩
        (alnCheck_rep ⟨53, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T53_53_2 Q2.hfix53_53_2 Q2.hinj53_53_2
      Q2.hcardT53_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T53_53_2 i) (Q2.hfix53_53_2 i) _)
      colCert_53_53_1.hD ?_).symm
  rw [alnId_53 j hj]


theorem leaf_53_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 53 []).length)
    (hq : (normIsRep.getD 53 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨53, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨53, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨53, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨53, by decide⟩ (listedAt ⟨53, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T53_53
      hfix53_53 hinj53_53 hcardT53_53
      (fun i => conj_mem_of_fixedPoints _ _ (T53_53 i) (hfix53_53 i) _)
      ⟨53, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨53, by decide⟩ (Q2.listedAt ⟨53, by decide⟩
        (alnCheck_rep ⟨53, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T53_53_2 Q2.hfix53_53_2 Q2.hinj53_53_2
      Q2.hcardT53_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T53_53_2 i) (Q2.hfix53_53_2 i) _)
      colCert_53_53_2.hD ?_).symm
  rw [alnId_53 j hj]


theorem leaf_53_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 53 []).length)
    (hq : (normIsRep.getD 53 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨53, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨53, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨53, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨53, by decide⟩ (listedAt ⟨53, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T53_53
      hfix53_53 hinj53_53 hcardT53_53
      (fun i => conj_mem_of_fixedPoints _ _ (T53_53 i) (hfix53_53 i) _)
      ⟨53, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨53, by decide⟩ (Q2.listedAt ⟨53, by decide⟩
        (alnCheck_rep ⟨53, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T53_53_2 Q2.hfix53_53_2 Q2.hinj53_53_2
      Q2.hcardT53_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T53_53_2 i) (Q2.hfix53_53_2 i) _)
      colCert_53_53_3.hD ?_).symm
  rw [alnId_53 j hj]


theorem leaf_53_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 53 []).length)
    (hq : (normIsRep.getD 53 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨53, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨53, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨53, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨53, by decide⟩ (listedAt ⟨53, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T53_53
      hfix53_53 hinj53_53 hcardT53_53
      (fun i => conj_mem_of_fixedPoints _ _ (T53_53 i) (hfix53_53 i) _)
      ⟨53, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨53, by decide⟩ (Q2.listedAt ⟨53, by decide⟩
        (alnCheck_rep ⟨53, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T53_53_2 Q2.hfix53_53_2 Q2.hinj53_53_2
      Q2.hcardT53_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T53_53_2 i) (Q2.hfix53_53_2 i) _)
      colCert_53_53_4.hD ?_).symm
  rw [alnId_53 j hj]


theorem leaf_53_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 53 []).length)
    (hq : (normIsRep.getD 53 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨53, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨53, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨53, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨53, by decide⟩ (listedAt ⟨53, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T53_53
      hfix53_53 hinj53_53 hcardT53_53
      (fun i => conj_mem_of_fixedPoints _ _ (T53_53 i) (hfix53_53 i) _)
      ⟨53, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨53, by decide⟩ (Q2.listedAt ⟨53, by decide⟩
        (alnCheck_rep ⟨53, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T53_53_2 Q2.hfix53_53_2 Q2.hinj53_53_2
      Q2.hcardT53_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T53_53_2 i) (Q2.hfix53_53_2 i) _)
      colCert_53_53_5.hD ?_).symm
  rw [alnId_53 j hj]


theorem leaf_53_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 53 []).length)
    (hq : (normIsRep.getD 53 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨53, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨53, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨53, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨53, by decide⟩ (listedAt ⟨53, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T53_53
      hfix53_53 hinj53_53 hcardT53_53
      (fun i => conj_mem_of_fixedPoints _ _ (T53_53 i) (hfix53_53 i) _)
      ⟨53, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨53, by decide⟩ (Q2.listedAt ⟨53, by decide⟩
        (alnCheck_rep ⟨53, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T53_53_2 Q2.hfix53_53_2 Q2.hinj53_53_2
      Q2.hcardT53_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T53_53_2 i) (Q2.hfix53_53_2 i) _)
      colCert_53_53_10.hD ?_).symm
  rw [alnId_53 j hj]


theorem leaf_53_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 53 []).length)
    (hq : (normIsRep.getD 53 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨53, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨53, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨53, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨53, by decide⟩ (listedAt ⟨53, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T53_53
      hfix53_53 hinj53_53 hcardT53_53
      (fun i => conj_mem_of_fixedPoints _ _ (T53_53 i) (hfix53_53 i) _)
      ⟨53, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨53, by decide⟩ (Q2.listedAt ⟨53, by decide⟩
        (alnCheck_rep ⟨53, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T53_53_2 Q2.hfix53_53_2 Q2.hinj53_53_2
      Q2.hcardT53_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T53_53_2 i) (Q2.hfix53_53_2 i) _)
      colCert_53_53_15.hD ?_).symm
  rw [alnId_53 j hj]


theorem leaf_53_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 53 []).length)
    (hq : (normIsRep.getD 53 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨53, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨53, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨53, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨53, by decide⟩ (listedAt ⟨53, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T53_53
      hfix53_53 hinj53_53 hcardT53_53
      (fun i => conj_mem_of_fixedPoints _ _ (T53_53 i) (hfix53_53 i) _)
      ⟨53, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨53, by decide⟩ (Q2.listedAt ⟨53, by decide⟩
        (alnCheck_rep ⟨53, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T53_53_2 Q2.hfix53_53_2 Q2.hinj53_53_2
      Q2.hcardT53_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T53_53_2 i) (Q2.hfix53_53_2 i) _)
      colCert_53_53_20.hD ?_).symm
  rw [alnId_53 j hj]


theorem leaf_54_11_0 (hp : 0 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 54 []).length)
    (hq : (normIsRep.getD 54 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 0 hp)
        (rowE2 (⟨54, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp))
        (rowE1 (⟨54, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨54, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨54, by decide⟩ (listedAt ⟨54, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp)) T54_11
      hfix54_11 hinj54_11 hcardT54_11
      (fun i => conj_mem_of_fixedPoints _ _ (T54_11 i) (hfix54_11 i) _)
      ⟨54, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨54, by decide⟩ (Q2.listedAt ⟨54, by decide⟩
        (alnCheck_rep ⟨54, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 0 hp) Q2.T54_11_2 Q2.hfix54_11_2 Q2.hinj54_11_2
      Q2.hcardT54_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T54_11_2 i) (Q2.hfix54_11_2 i) _)
      colCert_54_11_0.hD ?_).symm
  rw [alnId_54 j hj]


theorem leaf_54_11_1 (hp : 1 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 54 []).length)
    (hq : (normIsRep.getD 54 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 1 hp)
        (rowE2 (⟨54, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp))
        (rowE1 (⟨54, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨54, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨54, by decide⟩ (listedAt ⟨54, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp)) T54_11
      hfix54_11 hinj54_11 hcardT54_11
      (fun i => conj_mem_of_fixedPoints _ _ (T54_11 i) (hfix54_11 i) _)
      ⟨54, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨54, by decide⟩ (Q2.listedAt ⟨54, by decide⟩
        (alnCheck_rep ⟨54, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 1 hp) Q2.T54_11_2 Q2.hfix54_11_2 Q2.hinj54_11_2
      Q2.hcardT54_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T54_11_2 i) (Q2.hfix54_11_2 i) _)
      colCert_54_11_1.hD ?_).symm
  rw [alnId_54 j hj]


theorem leaf_54_11_2 (hp : 2 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 54 []).length)
    (hq : (normIsRep.getD 54 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 2 hp)
        (rowE2 (⟨54, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp))
        (rowE1 (⟨54, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨54, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨54, by decide⟩ (listedAt ⟨54, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp)) T54_11
      hfix54_11 hinj54_11 hcardT54_11
      (fun i => conj_mem_of_fixedPoints _ _ (T54_11 i) (hfix54_11 i) _)
      ⟨54, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨54, by decide⟩ (Q2.listedAt ⟨54, by decide⟩
        (alnCheck_rep ⟨54, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 2 hp) Q2.T54_11_2 Q2.hfix54_11_2 Q2.hinj54_11_2
      Q2.hcardT54_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T54_11_2 i) (Q2.hfix54_11_2 i) _)
      colCert_54_11_2.hD ?_).symm
  rw [alnId_54 j hj]


theorem leaf_54_11_3 (hp : 3 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 54 []).length)
    (hq : (normIsRep.getD 54 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 3 hp)
        (rowE2 (⟨54, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp))
        (rowE1 (⟨54, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨54, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨54, by decide⟩ (listedAt ⟨54, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp)) T54_11
      hfix54_11 hinj54_11 hcardT54_11
      (fun i => conj_mem_of_fixedPoints _ _ (T54_11 i) (hfix54_11 i) _)
      ⟨54, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨54, by decide⟩ (Q2.listedAt ⟨54, by decide⟩
        (alnCheck_rep ⟨54, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 3 hp) Q2.T54_11_2 Q2.hfix54_11_2 Q2.hinj54_11_2
      Q2.hcardT54_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T54_11_2 i) (Q2.hfix54_11_2 i) _)
      colCert_54_11_3.hD ?_).symm
  rw [alnId_54 j hj]


theorem leaf_54_11_4 (hp : 4 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 54 []).length)
    (hq : (normIsRep.getD 54 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 4 hp)
        (rowE2 (⟨54, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp))
        (rowE1 (⟨54, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨54, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨54, by decide⟩ (listedAt ⟨54, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp)) T54_11
      hfix54_11 hinj54_11 hcardT54_11
      (fun i => conj_mem_of_fixedPoints _ _ (T54_11 i) (hfix54_11 i) _)
      ⟨54, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨54, by decide⟩ (Q2.listedAt ⟨54, by decide⟩
        (alnCheck_rep ⟨54, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 4 hp) Q2.T54_11_2 Q2.hfix54_11_2 Q2.hinj54_11_2
      Q2.hcardT54_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T54_11_2 i) (Q2.hfix54_11_2 i) _)
      colCert_54_11_4.hD ?_).symm
  rw [alnId_54 j hj]


theorem leaf_54_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 54 []).length)
    (hq : (normIsRep.getD 54 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨54, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨54, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨54, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨54, by decide⟩ (listedAt ⟨54, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T54_12
      hfix54_12 hinj54_12 hcardT54_12
      (fun i => conj_mem_of_fixedPoints _ _ (T54_12 i) (hfix54_12 i) _)
      ⟨54, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨54, by decide⟩ (Q2.listedAt ⟨54, by decide⟩
        (alnCheck_rep ⟨54, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T54_12_2 Q2.hfix54_12_2 Q2.hinj54_12_2
      Q2.hcardT54_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T54_12_2 i) (Q2.hfix54_12_2 i) _)
      colCert_54_12_0.hD ?_).symm
  rw [alnId_54 j hj]


theorem leaf_54_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 54 []).length)
    (hq : (normIsRep.getD 54 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨54, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨54, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨54, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨54, by decide⟩ (listedAt ⟨54, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T54_12
      hfix54_12 hinj54_12 hcardT54_12
      (fun i => conj_mem_of_fixedPoints _ _ (T54_12 i) (hfix54_12 i) _)
      ⟨54, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨54, by decide⟩ (Q2.listedAt ⟨54, by decide⟩
        (alnCheck_rep ⟨54, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T54_12_2 Q2.hfix54_12_2 Q2.hinj54_12_2
      Q2.hcardT54_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T54_12_2 i) (Q2.hfix54_12_2 i) _)
      colCert_54_12_1.hD ?_).symm
  rw [alnId_54 j hj]


theorem leaf_54_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 54 []).length)
    (hq : (normIsRep.getD 54 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨54, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨54, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨54, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨54, by decide⟩ (listedAt ⟨54, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T54_12
      hfix54_12 hinj54_12 hcardT54_12
      (fun i => conj_mem_of_fixedPoints _ _ (T54_12 i) (hfix54_12 i) _)
      ⟨54, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨54, by decide⟩ (Q2.listedAt ⟨54, by decide⟩
        (alnCheck_rep ⟨54, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T54_12_2 Q2.hfix54_12_2 Q2.hinj54_12_2
      Q2.hcardT54_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T54_12_2 i) (Q2.hfix54_12_2 i) _)
      colCert_54_12_2.hD ?_).symm
  rw [alnId_54 j hj]


theorem leaf_54_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 54 []).length)
    (hq : (normIsRep.getD 54 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨54, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨54, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨54, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨54, by decide⟩ (listedAt ⟨54, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T54_12
      hfix54_12 hinj54_12 hcardT54_12
      (fun i => conj_mem_of_fixedPoints _ _ (T54_12 i) (hfix54_12 i) _)
      ⟨54, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨54, by decide⟩ (Q2.listedAt ⟨54, by decide⟩
        (alnCheck_rep ⟨54, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T54_12_2 Q2.hfix54_12_2 Q2.hinj54_12_2
      Q2.hcardT54_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T54_12_2 i) (Q2.hfix54_12_2 i) _)
      colCert_54_12_3.hD ?_).symm
  rw [alnId_54 j hj]


theorem leaf_54_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 54 []).length)
    (hq : (normIsRep.getD 54 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨54, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨54, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨54, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨54, by decide⟩ (listedAt ⟨54, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T54_12
      hfix54_12 hinj54_12 hcardT54_12
      (fun i => conj_mem_of_fixedPoints _ _ (T54_12 i) (hfix54_12 i) _)
      ⟨54, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨54, by decide⟩ (Q2.listedAt ⟨54, by decide⟩
        (alnCheck_rep ⟨54, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T54_12_2 Q2.hfix54_12_2 Q2.hinj54_12_2
      Q2.hcardT54_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T54_12_2 i) (Q2.hfix54_12_2 i) _)
      colCert_54_12_4.hD ?_).symm
  rw [alnId_54 j hj]


theorem leaf_54_54_0 (hp : 0 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 54 []).length)
    (hq : (normIsRep.getD 54 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 0 hp)
        (rowE2 (⟨54, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 0 (transLenTr ⟨54, by decide⟩ 0 hp))
        (rowE1 (⟨54, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨54, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨54, by decide⟩ (listedAt ⟨54, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 0 (transLenTr ⟨54, by decide⟩ 0 hp)) T54_54
      hfix54_54 hinj54_54 hcardT54_54
      (fun i => conj_mem_of_fixedPoints _ _ (T54_54 i) (hfix54_54 i) _)
      ⟨54, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨54, by decide⟩ (Q2.listedAt ⟨54, by decide⟩
        (alnCheck_rep ⟨54, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 0 hp) Q2.T54_54_2 Q2.hfix54_54_2 Q2.hinj54_54_2
      Q2.hcardT54_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T54_54_2 i) (Q2.hfix54_54_2 i) _)
      colCert_54_54_0.hD ?_).symm
  rw [alnId_54 j hj]


theorem leaf_54_54_1 (hp : 1 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 54 []).length)
    (hq : (normIsRep.getD 54 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 1 hp)
        (rowE2 (⟨54, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 1 (transLenTr ⟨54, by decide⟩ 1 hp))
        (rowE1 (⟨54, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨54, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨54, by decide⟩ (listedAt ⟨54, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 1 (transLenTr ⟨54, by decide⟩ 1 hp)) T54_54
      hfix54_54 hinj54_54 hcardT54_54
      (fun i => conj_mem_of_fixedPoints _ _ (T54_54 i) (hfix54_54 i) _)
      ⟨54, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨54, by decide⟩ (Q2.listedAt ⟨54, by decide⟩
        (alnCheck_rep ⟨54, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 1 hp) Q2.T54_54_2 Q2.hfix54_54_2 Q2.hinj54_54_2
      Q2.hcardT54_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T54_54_2 i) (Q2.hfix54_54_2 i) _)
      colCert_54_54_1.hD ?_).symm
  rw [alnId_54 j hj]


theorem leaf_54_54_2 (hp : 2 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 54 []).length)
    (hq : (normIsRep.getD 54 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 2 hp)
        (rowE2 (⟨54, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 2 (transLenTr ⟨54, by decide⟩ 2 hp))
        (rowE1 (⟨54, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨54, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨54, by decide⟩ (listedAt ⟨54, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 2 (transLenTr ⟨54, by decide⟩ 2 hp)) T54_54
      hfix54_54 hinj54_54 hcardT54_54
      (fun i => conj_mem_of_fixedPoints _ _ (T54_54 i) (hfix54_54 i) _)
      ⟨54, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨54, by decide⟩ (Q2.listedAt ⟨54, by decide⟩
        (alnCheck_rep ⟨54, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 2 hp) Q2.T54_54_2 Q2.hfix54_54_2 Q2.hinj54_54_2
      Q2.hcardT54_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T54_54_2 i) (Q2.hfix54_54_2 i) _)
      colCert_54_54_2.hD ?_).symm
  rw [alnId_54 j hj]


theorem leaf_54_54_3 (hp : 3 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 54 []).length)
    (hq : (normIsRep.getD 54 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 3 hp)
        (rowE2 (⟨54, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 3 (transLenTr ⟨54, by decide⟩ 3 hp))
        (rowE1 (⟨54, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨54, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨54, by decide⟩ (listedAt ⟨54, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 3 (transLenTr ⟨54, by decide⟩ 3 hp)) T54_54
      hfix54_54 hinj54_54 hcardT54_54
      (fun i => conj_mem_of_fixedPoints _ _ (T54_54 i) (hfix54_54 i) _)
      ⟨54, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨54, by decide⟩ (Q2.listedAt ⟨54, by decide⟩
        (alnCheck_rep ⟨54, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 3 hp) Q2.T54_54_2 Q2.hfix54_54_2 Q2.hinj54_54_2
      Q2.hcardT54_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T54_54_2 i) (Q2.hfix54_54_2 i) _)
      colCert_54_54_3.hD ?_).symm
  rw [alnId_54 j hj]


theorem leaf_54_54_4 (hp : 4 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 54 []).length)
    (hq : (normIsRep.getD 54 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 4 hp)
        (rowE2 (⟨54, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 4 (transLenTr ⟨54, by decide⟩ 4 hp))
        (rowE1 (⟨54, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨54, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨54, by decide⟩ (listedAt ⟨54, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 4 (transLenTr ⟨54, by decide⟩ 4 hp)) T54_54
      hfix54_54 hinj54_54 hcardT54_54
      (fun i => conj_mem_of_fixedPoints _ _ (T54_54 i) (hfix54_54 i) _)
      ⟨54, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨54, by decide⟩ (Q2.listedAt ⟨54, by decide⟩
        (alnCheck_rep ⟨54, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 4 hp) Q2.T54_54_2 Q2.hfix54_54_2 Q2.hinj54_54_2
      Q2.hcardT54_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T54_54_2 i) (Q2.hfix54_54_2 i) _)
      colCert_54_54_4.hD ?_).symm
  rw [alnId_54 j hj]


theorem leaf_54_54_5 (hp : 5 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 54 []).length)
    (hq : (normIsRep.getD 54 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 5 hp)
        (rowE2 (⟨54, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 5 (transLenTr ⟨54, by decide⟩ 5 hp))
        (rowE1 (⟨54, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨54, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨54, by decide⟩ (listedAt ⟨54, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 5 (transLenTr ⟨54, by decide⟩ 5 hp)) T54_54
      hfix54_54 hinj54_54 hcardT54_54
      (fun i => conj_mem_of_fixedPoints _ _ (T54_54 i) (hfix54_54 i) _)
      ⟨54, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨54, by decide⟩ (Q2.listedAt ⟨54, by decide⟩
        (alnCheck_rep ⟨54, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 5 hp) Q2.T54_54_2 Q2.hfix54_54_2 Q2.hinj54_54_2
      Q2.hcardT54_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T54_54_2 i) (Q2.hfix54_54_2 i) _)
      colCert_54_54_5.hD ?_).symm
  rw [alnId_54 j hj]


theorem leaf_54_54_10 (hp : 10 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 54 []).length)
    (hq : (normIsRep.getD 54 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 10 hp)
        (rowE2 (⟨54, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 10 (transLenTr ⟨54, by decide⟩ 10 hp))
        (rowE1 (⟨54, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨54, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨54, by decide⟩ (listedAt ⟨54, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 10 (transLenTr ⟨54, by decide⟩ 10 hp)) T54_54
      hfix54_54 hinj54_54 hcardT54_54
      (fun i => conj_mem_of_fixedPoints _ _ (T54_54 i) (hfix54_54 i) _)
      ⟨54, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨54, by decide⟩ (Q2.listedAt ⟨54, by decide⟩
        (alnCheck_rep ⟨54, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 10 hp) Q2.T54_54_2 Q2.hfix54_54_2 Q2.hinj54_54_2
      Q2.hcardT54_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T54_54_2 i) (Q2.hfix54_54_2 i) _)
      colCert_54_54_10.hD ?_).symm
  rw [alnId_54 j hj]


theorem leaf_54_54_15 (hp : 15 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 54 []).length)
    (hq : (normIsRep.getD 54 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 15 hp)
        (rowE2 (⟨54, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 15 (transLenTr ⟨54, by decide⟩ 15 hp))
        (rowE1 (⟨54, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨54, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨54, by decide⟩ (listedAt ⟨54, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 15 (transLenTr ⟨54, by decide⟩ 15 hp)) T54_54
      hfix54_54 hinj54_54 hcardT54_54
      (fun i => conj_mem_of_fixedPoints _ _ (T54_54 i) (hfix54_54 i) _)
      ⟨54, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨54, by decide⟩ (Q2.listedAt ⟨54, by decide⟩
        (alnCheck_rep ⟨54, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 15 hp) Q2.T54_54_2 Q2.hfix54_54_2 Q2.hinj54_54_2
      Q2.hcardT54_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T54_54_2 i) (Q2.hfix54_54_2 i) _)
      colCert_54_54_15.hD ?_).symm
  rw [alnId_54 j hj]


theorem leaf_54_54_20 (hp : 20 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 54 []).length)
    (hq : (normIsRep.getD 54 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 20 hp)
        (rowE2 (⟨54, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 20 (transLenTr ⟨54, by decide⟩ 20 hp))
        (rowE1 (⟨54, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨54, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨54, by decide⟩ (listedAt ⟨54, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 20 (transLenTr ⟨54, by decide⟩ 20 hp)) T54_54
      hfix54_54 hinj54_54 hcardT54_54
      (fun i => conj_mem_of_fixedPoints _ _ (T54_54 i) (hfix54_54 i) _)
      ⟨54, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨54, by decide⟩ (Q2.listedAt ⟨54, by decide⟩
        (alnCheck_rep ⟨54, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 20 hp) Q2.T54_54_2 Q2.hfix54_54_2 Q2.hinj54_54_2
      Q2.hcardT54_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T54_54_2 i) (Q2.hfix54_54_2 i) _)
      colCert_54_54_20.hD ?_).symm
  rw [alnId_54 j hj]


theorem leaf_55_9_0 (hp : 0 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 0 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp)) T55_9
      hfix55_9 hinj55_9 hcardT55_9
      (fun i => conj_mem_of_fixedPoints _ _ (T55_9 i) (hfix55_9 i) _)
      ⟨55, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 0 hp) Q2.T55_9_2 Q2.hfix55_9_2 Q2.hinj55_9_2
      Q2.hcardT55_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_9_2 i) (Q2.hfix55_9_2 i) _)
      colCert_55_9_0.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_9_1 (hp : 1 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 1 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp)) T55_9
      hfix55_9 hinj55_9 hcardT55_9
      (fun i => conj_mem_of_fixedPoints _ _ (T55_9 i) (hfix55_9 i) _)
      ⟨55, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 1 hp) Q2.T55_9_2 Q2.hfix55_9_2 Q2.hinj55_9_2
      Q2.hcardT55_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_9_2 i) (Q2.hfix55_9_2 i) _)
      colCert_55_9_1.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_9_2 (hp : 2 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 2 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp)) T55_9
      hfix55_9 hinj55_9 hcardT55_9
      (fun i => conj_mem_of_fixedPoints _ _ (T55_9 i) (hfix55_9 i) _)
      ⟨55, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 2 hp) Q2.T55_9_2 Q2.hfix55_9_2 Q2.hinj55_9_2
      Q2.hcardT55_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_9_2 i) (Q2.hfix55_9_2 i) _)
      colCert_55_9_2.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_9_3 (hp : 3 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 3 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp)) T55_9
      hfix55_9 hinj55_9 hcardT55_9
      (fun i => conj_mem_of_fixedPoints _ _ (T55_9 i) (hfix55_9 i) _)
      ⟨55, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 3 hp) Q2.T55_9_2 Q2.hfix55_9_2 Q2.hinj55_9_2
      Q2.hcardT55_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_9_2 i) (Q2.hfix55_9_2 i) _)
      colCert_55_9_3.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_9_4 (hp : 4 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 4 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp)) T55_9
      hfix55_9 hinj55_9 hcardT55_9
      (fun i => conj_mem_of_fixedPoints _ _ (T55_9 i) (hfix55_9 i) _)
      ⟨55, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 4 hp) Q2.T55_9_2 Q2.hfix55_9_2 Q2.hinj55_9_2
      Q2.hcardT55_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_9_2 i) (Q2.hfix55_9_2 i) _)
      colCert_55_9_4.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T55_12
      hfix55_12 hinj55_12 hcardT55_12
      (fun i => conj_mem_of_fixedPoints _ _ (T55_12 i) (hfix55_12 i) _)
      ⟨55, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T55_12_2 Q2.hfix55_12_2 Q2.hinj55_12_2
      Q2.hcardT55_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_12_2 i) (Q2.hfix55_12_2 i) _)
      colCert_55_12_0.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T55_12
      hfix55_12 hinj55_12 hcardT55_12
      (fun i => conj_mem_of_fixedPoints _ _ (T55_12 i) (hfix55_12 i) _)
      ⟨55, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T55_12_2 Q2.hfix55_12_2 Q2.hinj55_12_2
      Q2.hcardT55_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_12_2 i) (Q2.hfix55_12_2 i) _)
      colCert_55_12_1.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T55_12
      hfix55_12 hinj55_12 hcardT55_12
      (fun i => conj_mem_of_fixedPoints _ _ (T55_12 i) (hfix55_12 i) _)
      ⟨55, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T55_12_2 Q2.hfix55_12_2 Q2.hinj55_12_2
      Q2.hcardT55_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_12_2 i) (Q2.hfix55_12_2 i) _)
      colCert_55_12_2.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T55_12
      hfix55_12 hinj55_12 hcardT55_12
      (fun i => conj_mem_of_fixedPoints _ _ (T55_12 i) (hfix55_12 i) _)
      ⟨55, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T55_12_2 Q2.hfix55_12_2 Q2.hinj55_12_2
      Q2.hcardT55_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_12_2 i) (Q2.hfix55_12_2 i) _)
      colCert_55_12_3.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T55_12
      hfix55_12 hinj55_12 hcardT55_12
      (fun i => conj_mem_of_fixedPoints _ _ (T55_12 i) (hfix55_12 i) _)
      ⟨55, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T55_12_2 Q2.hfix55_12_2 Q2.hinj55_12_2
      Q2.hcardT55_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_12_2 i) (Q2.hfix55_12_2 i) _)
      colCert_55_12_4.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_27_0 (hp : 0 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 0 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp)) T55_27
      hfix55_27 hinj55_27 hcardT55_27
      (fun i => conj_mem_of_fixedPoints _ _ (T55_27 i) (hfix55_27 i) _)
      ⟨55, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 0 hp) Q2.T55_27_2 Q2.hfix55_27_2 Q2.hinj55_27_2
      Q2.hcardT55_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_27_2 i) (Q2.hfix55_27_2 i) _)
      colCert_55_27_0.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_27_1 (hp : 1 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 1 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp)) T55_27
      hfix55_27 hinj55_27 hcardT55_27
      (fun i => conj_mem_of_fixedPoints _ _ (T55_27 i) (hfix55_27 i) _)
      ⟨55, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 1 hp) Q2.T55_27_2 Q2.hfix55_27_2 Q2.hinj55_27_2
      Q2.hcardT55_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_27_2 i) (Q2.hfix55_27_2 i) _)
      colCert_55_27_1.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_27_2 (hp : 2 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 2 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp)) T55_27
      hfix55_27 hinj55_27 hcardT55_27
      (fun i => conj_mem_of_fixedPoints _ _ (T55_27 i) (hfix55_27 i) _)
      ⟨55, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 2 hp) Q2.T55_27_2 Q2.hfix55_27_2 Q2.hinj55_27_2
      Q2.hcardT55_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_27_2 i) (Q2.hfix55_27_2 i) _)
      colCert_55_27_2.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_27_3 (hp : 3 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 3 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp)) T55_27
      hfix55_27 hinj55_27 hcardT55_27
      (fun i => conj_mem_of_fixedPoints _ _ (T55_27 i) (hfix55_27 i) _)
      ⟨55, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 3 hp) Q2.T55_27_2 Q2.hfix55_27_2 Q2.hinj55_27_2
      Q2.hcardT55_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_27_2 i) (Q2.hfix55_27_2 i) _)
      colCert_55_27_3.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_27_4 (hp : 4 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 4 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp)) T55_27
      hfix55_27 hinj55_27 hcardT55_27
      (fun i => conj_mem_of_fixedPoints _ _ (T55_27 i) (hfix55_27 i) _)
      ⟨55, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 4 hp) Q2.T55_27_2 Q2.hfix55_27_2 Q2.hinj55_27_2
      Q2.hcardT55_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_27_2 i) (Q2.hfix55_27_2 i) _)
      colCert_55_27_4.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_27_5 (hp : 5 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 5 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp)) T55_27
      hfix55_27 hinj55_27 hcardT55_27
      (fun i => conj_mem_of_fixedPoints _ _ (T55_27 i) (hfix55_27 i) _)
      ⟨55, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 5 hp) Q2.T55_27_2 Q2.hfix55_27_2 Q2.hinj55_27_2
      Q2.hcardT55_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_27_2 i) (Q2.hfix55_27_2 i) _)
      colCert_55_27_5.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_27_10 (hp : 10 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 10 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp)) T55_27
      hfix55_27 hinj55_27 hcardT55_27
      (fun i => conj_mem_of_fixedPoints _ _ (T55_27 i) (hfix55_27 i) _)
      ⟨55, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 10 hp) Q2.T55_27_2 Q2.hfix55_27_2 Q2.hinj55_27_2
      Q2.hcardT55_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_27_2 i) (Q2.hfix55_27_2 i) _)
      colCert_55_27_10.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_27_15 (hp : 15 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 15 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp)) T55_27
      hfix55_27 hinj55_27 hcardT55_27
      (fun i => conj_mem_of_fixedPoints _ _ (T55_27 i) (hfix55_27 i) _)
      ⟨55, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 15 hp) Q2.T55_27_2 Q2.hfix55_27_2 Q2.hinj55_27_2
      Q2.hcardT55_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_27_2 i) (Q2.hfix55_27_2 i) _)
      colCert_55_27_15.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_27_20 (hp : 20 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 20 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp)) T55_27
      hfix55_27 hinj55_27 hcardT55_27
      (fun i => conj_mem_of_fixedPoints _ _ (T55_27 i) (hfix55_27 i) _)
      ⟨55, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 20 hp) Q2.T55_27_2 Q2.hfix55_27_2 Q2.hinj55_27_2
      Q2.hcardT55_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_27_2 i) (Q2.hfix55_27_2 i) _)
      colCert_55_27_20.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_28_0 (hp : 0 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 0 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp)) T55_28
      hfix55_28 hinj55_28 hcardT55_28
      (fun i => conj_mem_of_fixedPoints _ _ (T55_28 i) (hfix55_28 i) _)
      ⟨55, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 0 hp) Q2.T55_28_2 Q2.hfix55_28_2 Q2.hinj55_28_2
      Q2.hcardT55_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_28_2 i) (Q2.hfix55_28_2 i) _)
      colCert_55_28_0.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_28_1 (hp : 1 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 1 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp)) T55_28
      hfix55_28 hinj55_28 hcardT55_28
      (fun i => conj_mem_of_fixedPoints _ _ (T55_28 i) (hfix55_28 i) _)
      ⟨55, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 1 hp) Q2.T55_28_2 Q2.hfix55_28_2 Q2.hinj55_28_2
      Q2.hcardT55_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_28_2 i) (Q2.hfix55_28_2 i) _)
      colCert_55_28_1.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_28_2 (hp : 2 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 2 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp)) T55_28
      hfix55_28 hinj55_28 hcardT55_28
      (fun i => conj_mem_of_fixedPoints _ _ (T55_28 i) (hfix55_28 i) _)
      ⟨55, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 2 hp) Q2.T55_28_2 Q2.hfix55_28_2 Q2.hinj55_28_2
      Q2.hcardT55_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_28_2 i) (Q2.hfix55_28_2 i) _)
      colCert_55_28_2.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_28_3 (hp : 3 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 3 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp)) T55_28
      hfix55_28 hinj55_28 hcardT55_28
      (fun i => conj_mem_of_fixedPoints _ _ (T55_28 i) (hfix55_28 i) _)
      ⟨55, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 3 hp) Q2.T55_28_2 Q2.hfix55_28_2 Q2.hinj55_28_2
      Q2.hcardT55_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_28_2 i) (Q2.hfix55_28_2 i) _)
      colCert_55_28_3.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_28_4 (hp : 4 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 4 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp)) T55_28
      hfix55_28 hinj55_28 hcardT55_28
      (fun i => conj_mem_of_fixedPoints _ _ (T55_28 i) (hfix55_28 i) _)
      ⟨55, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 4 hp) Q2.T55_28_2 Q2.hfix55_28_2 Q2.hinj55_28_2
      Q2.hcardT55_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_28_2 i) (Q2.hfix55_28_2 i) _)
      colCert_55_28_4.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_28_5 (hp : 5 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 5 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp)) T55_28
      hfix55_28 hinj55_28 hcardT55_28
      (fun i => conj_mem_of_fixedPoints _ _ (T55_28 i) (hfix55_28 i) _)
      ⟨55, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 5 hp) Q2.T55_28_2 Q2.hfix55_28_2 Q2.hinj55_28_2
      Q2.hcardT55_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_28_2 i) (Q2.hfix55_28_2 i) _)
      colCert_55_28_5.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_28_10 (hp : 10 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 10 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp)) T55_28
      hfix55_28 hinj55_28 hcardT55_28
      (fun i => conj_mem_of_fixedPoints _ _ (T55_28 i) (hfix55_28 i) _)
      ⟨55, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 10 hp) Q2.T55_28_2 Q2.hfix55_28_2 Q2.hinj55_28_2
      Q2.hcardT55_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_28_2 i) (Q2.hfix55_28_2 i) _)
      colCert_55_28_10.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_28_15 (hp : 15 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 15 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp)) T55_28
      hfix55_28 hinj55_28 hcardT55_28
      (fun i => conj_mem_of_fixedPoints _ _ (T55_28 i) (hfix55_28 i) _)
      ⟨55, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 15 hp) Q2.T55_28_2 Q2.hfix55_28_2 Q2.hinj55_28_2
      Q2.hcardT55_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_28_2 i) (Q2.hfix55_28_2 i) _)
      colCert_55_28_15.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_28_20 (hp : 20 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 20 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp)) T55_28
      hfix55_28 hinj55_28 hcardT55_28
      (fun i => conj_mem_of_fixedPoints _ _ (T55_28 i) (hfix55_28 i) _)
      ⟨55, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 20 hp) Q2.T55_28_2 Q2.hfix55_28_2 Q2.hinj55_28_2
      Q2.hcardT55_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_28_2 i) (Q2.hfix55_28_2 i) _)
      colCert_55_28_20.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_33_0 (hp : 0 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 0 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp)) T55_33
      hfix55_33 hinj55_33 hcardT55_33
      (fun i => conj_mem_of_fixedPoints _ _ (T55_33 i) (hfix55_33 i) _)
      ⟨55, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 0 hp) Q2.T55_33_2 Q2.hfix55_33_2 Q2.hinj55_33_2
      Q2.hcardT55_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_33_2 i) (Q2.hfix55_33_2 i) _)
      colCert_55_33_0.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_33_1 (hp : 1 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 1 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp)) T55_33
      hfix55_33 hinj55_33 hcardT55_33
      (fun i => conj_mem_of_fixedPoints _ _ (T55_33 i) (hfix55_33 i) _)
      ⟨55, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 1 hp) Q2.T55_33_2 Q2.hfix55_33_2 Q2.hinj55_33_2
      Q2.hcardT55_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_33_2 i) (Q2.hfix55_33_2 i) _)
      colCert_55_33_1.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_33_2 (hp : 2 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 2 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp)) T55_33
      hfix55_33 hinj55_33 hcardT55_33
      (fun i => conj_mem_of_fixedPoints _ _ (T55_33 i) (hfix55_33 i) _)
      ⟨55, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 2 hp) Q2.T55_33_2 Q2.hfix55_33_2 Q2.hinj55_33_2
      Q2.hcardT55_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_33_2 i) (Q2.hfix55_33_2 i) _)
      colCert_55_33_2.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_33_3 (hp : 3 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 3 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp)) T55_33
      hfix55_33 hinj55_33 hcardT55_33
      (fun i => conj_mem_of_fixedPoints _ _ (T55_33 i) (hfix55_33 i) _)
      ⟨55, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 3 hp) Q2.T55_33_2 Q2.hfix55_33_2 Q2.hinj55_33_2
      Q2.hcardT55_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_33_2 i) (Q2.hfix55_33_2 i) _)
      colCert_55_33_3.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_33_4 (hp : 4 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 4 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp)) T55_33
      hfix55_33 hinj55_33 hcardT55_33
      (fun i => conj_mem_of_fixedPoints _ _ (T55_33 i) (hfix55_33 i) _)
      ⟨55, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 4 hp) Q2.T55_33_2 Q2.hfix55_33_2 Q2.hinj55_33_2
      Q2.hcardT55_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_33_2 i) (Q2.hfix55_33_2 i) _)
      colCert_55_33_4.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_33_5 (hp : 5 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 5 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp)) T55_33
      hfix55_33 hinj55_33 hcardT55_33
      (fun i => conj_mem_of_fixedPoints _ _ (T55_33 i) (hfix55_33 i) _)
      ⟨55, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 5 hp) Q2.T55_33_2 Q2.hfix55_33_2 Q2.hinj55_33_2
      Q2.hcardT55_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_33_2 i) (Q2.hfix55_33_2 i) _)
      colCert_55_33_5.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_33_10 (hp : 10 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 10 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp)) T55_33
      hfix55_33 hinj55_33 hcardT55_33
      (fun i => conj_mem_of_fixedPoints _ _ (T55_33 i) (hfix55_33 i) _)
      ⟨55, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 10 hp) Q2.T55_33_2 Q2.hfix55_33_2 Q2.hinj55_33_2
      Q2.hcardT55_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_33_2 i) (Q2.hfix55_33_2 i) _)
      colCert_55_33_10.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_33_15 (hp : 15 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 15 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp)) T55_33
      hfix55_33 hinj55_33 hcardT55_33
      (fun i => conj_mem_of_fixedPoints _ _ (T55_33 i) (hfix55_33 i) _)
      ⟨55, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 15 hp) Q2.T55_33_2 Q2.hfix55_33_2 Q2.hinj55_33_2
      Q2.hcardT55_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_33_2 i) (Q2.hfix55_33_2 i) _)
      colCert_55_33_15.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_33_20 (hp : 20 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 20 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp)) T55_33
      hfix55_33 hinj55_33 hcardT55_33
      (fun i => conj_mem_of_fixedPoints _ _ (T55_33 i) (hfix55_33 i) _)
      ⟨55, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 20 hp) Q2.T55_33_2 Q2.hfix55_33_2 Q2.hinj55_33_2
      Q2.hcardT55_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_33_2 i) (Q2.hfix55_33_2 i) _)
      colCert_55_33_20.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_38_0 (hp : 0 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 0 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp)) T55_38
      hfix55_38 hinj55_38 hcardT55_38
      (fun i => conj_mem_of_fixedPoints _ _ (T55_38 i) (hfix55_38 i) _)
      ⟨55, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 0 hp) Q2.T55_38_2 Q2.hfix55_38_2 Q2.hinj55_38_2
      Q2.hcardT55_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_38_2 i) (Q2.hfix55_38_2 i) _)
      colCert_55_38_0.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_38_1 (hp : 1 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 1 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp)) T55_38
      hfix55_38 hinj55_38 hcardT55_38
      (fun i => conj_mem_of_fixedPoints _ _ (T55_38 i) (hfix55_38 i) _)
      ⟨55, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 1 hp) Q2.T55_38_2 Q2.hfix55_38_2 Q2.hinj55_38_2
      Q2.hcardT55_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_38_2 i) (Q2.hfix55_38_2 i) _)
      colCert_55_38_1.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_38_2 (hp : 2 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 2 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp)) T55_38
      hfix55_38 hinj55_38 hcardT55_38
      (fun i => conj_mem_of_fixedPoints _ _ (T55_38 i) (hfix55_38 i) _)
      ⟨55, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 2 hp) Q2.T55_38_2 Q2.hfix55_38_2 Q2.hinj55_38_2
      Q2.hcardT55_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_38_2 i) (Q2.hfix55_38_2 i) _)
      colCert_55_38_2.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_38_3 (hp : 3 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 3 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp)) T55_38
      hfix55_38 hinj55_38 hcardT55_38
      (fun i => conj_mem_of_fixedPoints _ _ (T55_38 i) (hfix55_38 i) _)
      ⟨55, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 3 hp) Q2.T55_38_2 Q2.hfix55_38_2 Q2.hinj55_38_2
      Q2.hcardT55_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_38_2 i) (Q2.hfix55_38_2 i) _)
      colCert_55_38_3.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_38_4 (hp : 4 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 4 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp)) T55_38
      hfix55_38 hinj55_38 hcardT55_38
      (fun i => conj_mem_of_fixedPoints _ _ (T55_38 i) (hfix55_38 i) _)
      ⟨55, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 4 hp) Q2.T55_38_2 Q2.hfix55_38_2 Q2.hinj55_38_2
      Q2.hcardT55_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_38_2 i) (Q2.hfix55_38_2 i) _)
      colCert_55_38_4.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_38_5 (hp : 5 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 5 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp)) T55_38
      hfix55_38 hinj55_38 hcardT55_38
      (fun i => conj_mem_of_fixedPoints _ _ (T55_38 i) (hfix55_38 i) _)
      ⟨55, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 5 hp) Q2.T55_38_2 Q2.hfix55_38_2 Q2.hinj55_38_2
      Q2.hcardT55_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_38_2 i) (Q2.hfix55_38_2 i) _)
      colCert_55_38_5.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_38_10 (hp : 10 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 10 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp)) T55_38
      hfix55_38 hinj55_38 hcardT55_38
      (fun i => conj_mem_of_fixedPoints _ _ (T55_38 i) (hfix55_38 i) _)
      ⟨55, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 10 hp) Q2.T55_38_2 Q2.hfix55_38_2 Q2.hinj55_38_2
      Q2.hcardT55_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_38_2 i) (Q2.hfix55_38_2 i) _)
      colCert_55_38_10.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_38_15 (hp : 15 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 15 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp)) T55_38
      hfix55_38 hinj55_38 hcardT55_38
      (fun i => conj_mem_of_fixedPoints _ _ (T55_38 i) (hfix55_38 i) _)
      ⟨55, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 15 hp) Q2.T55_38_2 Q2.hfix55_38_2 Q2.hinj55_38_2
      Q2.hcardT55_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_38_2 i) (Q2.hfix55_38_2 i) _)
      colCert_55_38_15.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_38_20 (hp : 20 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 20 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp)) T55_38
      hfix55_38 hinj55_38 hcardT55_38
      (fun i => conj_mem_of_fixedPoints _ _ (T55_38 i) (hfix55_38 i) _)
      ⟨55, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 20 hp) Q2.T55_38_2 Q2.hfix55_38_2 Q2.hinj55_38_2
      Q2.hcardT55_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_38_2 i) (Q2.hfix55_38_2 i) _)
      colCert_55_38_20.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_43_0 (hp : 0 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 0 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp)) T55_43
      hfix55_43 hinj55_43 hcardT55_43
      (fun i => conj_mem_of_fixedPoints _ _ (T55_43 i) (hfix55_43 i) _)
      ⟨55, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 0 hp) Q2.T55_43_2 Q2.hfix55_43_2 Q2.hinj55_43_2
      Q2.hcardT55_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_43_2 i) (Q2.hfix55_43_2 i) _)
      colCert_55_43_0.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_43_1 (hp : 1 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 1 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp)) T55_43
      hfix55_43 hinj55_43 hcardT55_43
      (fun i => conj_mem_of_fixedPoints _ _ (T55_43 i) (hfix55_43 i) _)
      ⟨55, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 1 hp) Q2.T55_43_2 Q2.hfix55_43_2 Q2.hinj55_43_2
      Q2.hcardT55_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_43_2 i) (Q2.hfix55_43_2 i) _)
      colCert_55_43_1.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_43_2 (hp : 2 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 2 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp)) T55_43
      hfix55_43 hinj55_43 hcardT55_43
      (fun i => conj_mem_of_fixedPoints _ _ (T55_43 i) (hfix55_43 i) _)
      ⟨55, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 2 hp) Q2.T55_43_2 Q2.hfix55_43_2 Q2.hinj55_43_2
      Q2.hcardT55_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_43_2 i) (Q2.hfix55_43_2 i) _)
      colCert_55_43_2.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_43_3 (hp : 3 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 3 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp)) T55_43
      hfix55_43 hinj55_43 hcardT55_43
      (fun i => conj_mem_of_fixedPoints _ _ (T55_43 i) (hfix55_43 i) _)
      ⟨55, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 3 hp) Q2.T55_43_2 Q2.hfix55_43_2 Q2.hinj55_43_2
      Q2.hcardT55_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_43_2 i) (Q2.hfix55_43_2 i) _)
      colCert_55_43_3.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_43_4 (hp : 4 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 4 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp)) T55_43
      hfix55_43 hinj55_43 hcardT55_43
      (fun i => conj_mem_of_fixedPoints _ _ (T55_43 i) (hfix55_43 i) _)
      ⟨55, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 4 hp) Q2.T55_43_2 Q2.hfix55_43_2 Q2.hinj55_43_2
      Q2.hcardT55_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_43_2 i) (Q2.hfix55_43_2 i) _)
      colCert_55_43_4.hD ?_).symm
  rw [alnId_55 j hj]


end LeanDring.P5Presentation
