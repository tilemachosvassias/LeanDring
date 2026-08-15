/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharAlign
import LeanDring.P5.Data.ColRestCheap.C157
import LeanDring.P5.Data.ColRestCheap.C164
import LeanDring.P5.Data.ColRestCheap.C165

/-!
# Species-table cells, α-paired residual decides, chunk 16

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

theorem alnAll_67_67_95 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_95.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_95.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_100 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_100.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_100.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_105 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_105.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_105.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_110 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_110.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_110.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_115 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_115.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_115.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_120 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_120.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_120.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_73_0_0 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_0_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_0_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_6_0 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_6_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_6_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_6_1 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_6_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_6_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_6_2 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_6_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_6_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_6_3 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_6_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_6_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_6_4 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_6_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_6_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_12_0 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_12_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_12_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_12_1 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_12_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_12_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_12_2 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_12_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_12_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_12_3 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_12_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_12_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_12_4 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_12_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_12_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_24_0 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_24_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_24_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_24_1 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_24_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_24_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_24_2 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_24_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_24_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

end LeanDring.P5Presentation
