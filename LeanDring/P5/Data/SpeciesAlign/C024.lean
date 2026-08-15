/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharAlign
import LeanDring.P5.Data.ColCdd.C041
import LeanDring.P5.Data.ColRestCheap.C011
import LeanDring.P5.Data.ColRestCheap.C194
import LeanDring.P5.Data.ColRestCheap.C197

/-!
# Species-table cells, α-paired residual decides, chunk 23

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

theorem alnAll_95_95_1 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_95_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_95_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_95_2 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_95_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_95_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_95_3 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_95_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_95_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_95_4 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_95_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_95_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_95_5 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_95_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_95_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_95_10 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_95_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_95_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_95_15 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_95_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_95_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_95_20 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_95_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_95_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_95_25 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_95_25.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_95_25.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_95_50 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_95_50.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_95_50.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_95_75 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_95_75.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_95_75.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_95_95_100 : ∀ j, j < (repChars.getD 95 []).length →
    (normIsRep.getD 95 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_95_100.D (m := 25))
        (List.map ZMod.val ((repChars.getD 95 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_95_95_100.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 95 []).getD ((alnPos.getD 95 []).getD j 0) []))) := by decide

theorem alnAll_100_0_0 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_0_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_0_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_10_0 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_10_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_10_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_10_1 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_10_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_10_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_10_2 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_10_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_10_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_10_3 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_10_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_10_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_10_4 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_10_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_10_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_12_0 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_12_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_12_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_12_1 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_12_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_12_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_12_2 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_12_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_12_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_12_3 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_12_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_12_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_12_4 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_12_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_12_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_38_0 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_38_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_38_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_38_1 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_38_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_38_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_38_2 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_38_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_38_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_38_3 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_38_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_38_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_38_4 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_38_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_38_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_38_5 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_100_38_5.D1 (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_100_38_5.D2 (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_38_10 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_100_38_10.D1 (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_100_38_10.D2 (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_38_15 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_100_38_15.D1 (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_100_38_15.D2 (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_38_20 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_100_38_20.D1 (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_100_38_20.D2 (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_53_0 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_53_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_53_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_53_1 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_53_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_53_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_53_2 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_53_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_53_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_53_3 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_53_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_53_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_53_4 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_53_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_53_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_53_5 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_53_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_53_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_53_10 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_53_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_53_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_53_15 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_53_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_53_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_53_20 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_53_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_53_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_100_0 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_100_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_100_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_100_1 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_100_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_100_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_100_2 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_100_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_100_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_100_3 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_100_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_100_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_100_4 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_100_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_100_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_100_5 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_100_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_100_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_100_10 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_100_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_100_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_100_15 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_100_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_100_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_100_20 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_100_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_100_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_100_25 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_100_25.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_100_25.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_100_50 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_100_50.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_100_50.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_100_75 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_100_75.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_100_75.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_100_100_100 : ∀ j, j < (repChars.getD 100 []).length →
    (normIsRep.getD 100 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_100_100.D (m := 25))
        (List.map ZMod.val ((repChars.getD 100 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_100_100_100.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 100 []).getD ((alnPos.getD 100 []).getD j 0) []))) := by decide

theorem alnAll_105_0_0 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_0_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_0_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_10_0 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_10_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_10_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

end LeanDring.P5Presentation
