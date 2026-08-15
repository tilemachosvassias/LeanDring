/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharAlign
import LeanDring.P5.Data.ColRestCheap.C152
import LeanDring.P5.Data.ColRestCheap.C153
import LeanDring.P5.Data.ColRestCheap.C156

/-!
# Species-table cells, α-paired residual decides, chunk 13

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

theorem alnAll_64_64_40 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_40.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_40.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_45 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_45.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_45.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_50 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_50.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_50.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_55 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_55.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_55.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_60 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_60.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_60.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_65 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_65.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_65.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_70 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_70.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_70.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_75 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_75.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_75.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_80 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_80.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_80.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_85 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_85.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_85.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_90 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_90.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_90.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_95 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_95.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_95.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_100 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_100.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_100.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_105 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_105.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_105.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_110 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_110.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_110.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_115 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_115.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_115.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_120 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_120.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_120.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_67_0_0 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_0_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_0_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_7_0 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_7_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_7_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_7_1 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_7_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_7_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_7_2 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_7_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_7_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_7_3 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_7_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_7_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_7_4 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_7_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_7_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_12_0 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_12_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_12_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_12_1 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_12_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_12_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_12_2 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_12_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_12_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_12_3 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_12_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_12_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_12_4 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_12_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_12_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

end LeanDring.P5Presentation
