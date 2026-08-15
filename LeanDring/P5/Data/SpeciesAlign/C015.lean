/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharAlign
import LeanDring.P5.Data.ColCdd.C038
import LeanDring.P5.Data.ColCdd.C039
import LeanDring.P5.Data.ColRestCheap.C156

/-!
# Species-table cells, α-paired residual decides, chunk 14

For the 34 subgroup classes whose q1/q2 character SETS differ, σ pairs a q1
orbit-representative vector with a different q2 vector; this chunk certifies the
cyclotomic-value equality of the two fast codes at those pairs, over the already
kernel-bound column data.  Auto-emitted by `python/p5_alignmatch_emit.py`.
-/

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem alnAll_67_25_0 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_25_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_25_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_25_1 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_25_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_25_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_25_2 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_25_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_25_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_25_3 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_25_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_25_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_25_4 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_25_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_25_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_25_5 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_25_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_25_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_25_10 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_25_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_25_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_25_15 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_25_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_25_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_25_20 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_25_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_25_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_30_0 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_30_0.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_30_0.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_30_1 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_30_1.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_30_1.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_30_2 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_30_2.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_30_2.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_30_3 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_30_3.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_30_3.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_30_4 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_30_4.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_30_4.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_30_5 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_30_5.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_30_5.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_30_10 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_30_10.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_30_10.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_30_15 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_30_15.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_30_15.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_30_20 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_30_20.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_30_20.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_35_0 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_35_0.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_35_0.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_35_1 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_35_1.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_35_1.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_35_2 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_35_2.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_35_2.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_35_3 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_35_3.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_35_3.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_35_4 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_35_4.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_35_4.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_35_5 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_35_5.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_35_5.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_35_10 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_35_10.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_35_10.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_35_15 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_35_15.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_35_15.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_35_20 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_35_20.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_35_20.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_40_0 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_40_0.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_40_0.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_40_1 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_40_1.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_40_1.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_40_2 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_40_2.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_40_2.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_40_3 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_40_3.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_40_3.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_40_4 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_40_4.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_40_4.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_40_5 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_40_5.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_40_5.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_40_10 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_40_10.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_40_10.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_40_15 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_40_15.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_40_15.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

end LeanDring.P5Presentation
