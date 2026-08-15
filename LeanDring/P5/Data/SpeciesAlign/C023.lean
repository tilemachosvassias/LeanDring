/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharAlign
import LeanDring.P5.Data.ColCdd.C041
import LeanDring.P5.Data.ColRestCheap.C191
import LeanDring.P5.Data.ColRestCheap.C194

/-!
# Species-table cells, α-paired residual decides, chunk 22

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

theorem alnAll_90_28_5 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_90_28_5.D1 (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_90_28_5.D2 (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_28_10 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_90_28_10.D1 (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_90_28_10.D2 (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_28_15 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_90_28_15.D1 (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_90_28_15.D2 (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_28_20 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_90_28_20.D1 (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_90_28_20.D2 (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_53_0 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_53_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_53_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_53_1 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_53_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_53_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_53_2 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_53_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_53_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_53_3 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_53_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_53_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_53_4 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_53_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_53_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_53_5 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_53_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_53_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_53_10 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_53_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_53_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_53_15 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_53_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_53_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_53_20 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_53_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_53_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_90_0 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_90_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_90_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_90_1 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_90_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_90_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_90_2 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_90_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_90_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_90_3 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_90_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_90_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_90_4 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_90_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_90_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_90_5 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_90_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_90_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_90_10 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_90_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_90_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_90_15 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_90_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_90_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_90_20 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_90_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_90_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_90_25 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_90_25.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_90_25.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_90_50 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_90_50.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_90_50.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_90_75 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_90_75.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_90_75.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_90_100 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_90_100.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_90_100.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_95_0_0 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_0_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_0_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_10_0 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_10_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_10_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_10_1 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_10_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_10_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_10_2 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_10_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_10_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_10_3 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_10_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_10_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_10_4 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_10_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_10_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_12_0 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_12_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_12_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_12_1 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_12_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_12_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_12_2 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_12_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_12_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_12_3 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_12_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_12_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_12_4 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_12_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_12_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_33_0 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_33_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_33_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_33_1 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_33_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_33_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_33_2 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_33_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_33_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_33_3 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_33_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_33_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_33_4 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_33_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_33_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_33_5 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_95_33_5.D1 (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_95_33_5.D2 (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_33_10 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_95_33_10.D1 (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_95_33_10.D2 (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_33_15 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_95_33_15.D1 (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_95_33_15.D2 (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_33_20 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_95_33_20.D1 (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_95_33_20.D2 (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_53_0 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_53_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_53_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_53_1 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_53_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_53_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_53_2 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_53_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_53_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_53_3 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_53_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_53_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_53_4 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_53_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_53_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_53_5 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_53_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_53_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_53_10 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_53_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_53_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_53_15 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_53_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_53_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_53_20 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_53_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_53_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_95_0 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_95_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_95_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

end LeanDring.P5Presentation
