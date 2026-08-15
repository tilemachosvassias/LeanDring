/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharAlign
import LeanDring.P5.Data.ColRestCheap.C007
import LeanDring.P5.Data.ColRestHeavy.C029
import LeanDring.P5.Data.ColRestHeavy.C030
import LeanDring.P5.Data.ColRestHeavy.C031

/-!
# Species-table cells, α-paired residual decides, chunk 7

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

theorem alnAll_44_12_4 : ∀ j, j < (repChars.getD 44 []).length →
    (normIsRep.getD 44 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_12_4.D (m := 125))
        (List.map ZMod.val ((repChars.getD 44 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_12_4.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 44 []).getD ((alnPos.getD 44 []).getD j 0) []))) := by decide

theorem alnAll_44_44_0 : ∀ j, j < (repChars.getD 44 []).length →
    (normIsRep.getD 44 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_44_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 44 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_44_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 44 []).getD ((alnPos.getD 44 []).getD j 0) []))) := by decide

theorem alnAll_44_44_1 : ∀ j, j < (repChars.getD 44 []).length →
    (normIsRep.getD 44 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_44_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 44 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_44_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 44 []).getD ((alnPos.getD 44 []).getD j 0) []))) := by decide

theorem alnAll_44_44_2 : ∀ j, j < (repChars.getD 44 []).length →
    (normIsRep.getD 44 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_44_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 44 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_44_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 44 []).getD ((alnPos.getD 44 []).getD j 0) []))) := by decide

theorem alnAll_44_44_3 : ∀ j, j < (repChars.getD 44 []).length →
    (normIsRep.getD 44 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_44_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 44 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_44_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 44 []).getD ((alnPos.getD 44 []).getD j 0) []))) := by decide

theorem alnAll_44_44_4 : ∀ j, j < (repChars.getD 44 []).length →
    (normIsRep.getD 44 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_44_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 44 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_44_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 44 []).getD ((alnPos.getD 44 []).getD j 0) []))) := by decide

theorem alnAll_44_44_5 : ∀ j, j < (repChars.getD 44 []).length →
    (normIsRep.getD 44 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_44_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 44 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_44_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 44 []).getD ((alnPos.getD 44 []).getD j 0) []))) := by decide

theorem alnAll_44_44_10 : ∀ j, j < (repChars.getD 44 []).length →
    (normIsRep.getD 44 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_44_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 44 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_44_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 44 []).getD ((alnPos.getD 44 []).getD j 0) []))) := by decide

theorem alnAll_44_44_15 : ∀ j, j < (repChars.getD 44 []).length →
    (normIsRep.getD 44 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_44_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 44 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_44_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 44 []).getD ((alnPos.getD 44 []).getD j 0) []))) := by decide

theorem alnAll_44_44_20 : ∀ j, j < (repChars.getD 44 []).length →
    (normIsRep.getD 44 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_44_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 44 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_44_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 44 []).getD ((alnPos.getD 44 []).getD j 0) []))) := by decide

theorem alnAll_45_0_0 : ∀ j, j < (repChars.getD 45 []).length →
    (normIsRep.getD 45 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_0_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 45 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_0_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 45 []).getD ((alnPos.getD 45 []).getD j 0) []))) := by decide

theorem alnAll_45_12_0 : ∀ j, j < (repChars.getD 45 []).length →
    (normIsRep.getD 45 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_12_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 45 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_12_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 45 []).getD ((alnPos.getD 45 []).getD j 0) []))) := by decide

theorem alnAll_45_12_1 : ∀ j, j < (repChars.getD 45 []).length →
    (normIsRep.getD 45 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_12_1.D (m := 125))
        (List.map ZMod.val ((repChars.getD 45 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_12_1.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 45 []).getD ((alnPos.getD 45 []).getD j 0) []))) := by decide

theorem alnAll_45_12_2 : ∀ j, j < (repChars.getD 45 []).length →
    (normIsRep.getD 45 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_12_2.D (m := 125))
        (List.map ZMod.val ((repChars.getD 45 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_12_2.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 45 []).getD ((alnPos.getD 45 []).getD j 0) []))) := by decide

theorem alnAll_45_12_3 : ∀ j, j < (repChars.getD 45 []).length →
    (normIsRep.getD 45 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_12_3.D (m := 125))
        (List.map ZMod.val ((repChars.getD 45 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_12_3.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 45 []).getD ((alnPos.getD 45 []).getD j 0) []))) := by decide

theorem alnAll_45_12_4 : ∀ j, j < (repChars.getD 45 []).length →
    (normIsRep.getD 45 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_12_4.D (m := 125))
        (List.map ZMod.val ((repChars.getD 45 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_12_4.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 45 []).getD ((alnPos.getD 45 []).getD j 0) []))) := by decide

theorem alnAll_45_45_0 : ∀ j, j < (repChars.getD 45 []).length →
    (normIsRep.getD 45 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_45_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 45 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_45_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 45 []).getD ((alnPos.getD 45 []).getD j 0) []))) := by decide

theorem alnAll_45_45_1 : ∀ j, j < (repChars.getD 45 []).length →
    (normIsRep.getD 45 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_45_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 45 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_45_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 45 []).getD ((alnPos.getD 45 []).getD j 0) []))) := by decide

theorem alnAll_45_45_2 : ∀ j, j < (repChars.getD 45 []).length →
    (normIsRep.getD 45 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_45_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 45 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_45_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 45 []).getD ((alnPos.getD 45 []).getD j 0) []))) := by decide

theorem alnAll_45_45_3 : ∀ j, j < (repChars.getD 45 []).length →
    (normIsRep.getD 45 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_45_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 45 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_45_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 45 []).getD ((alnPos.getD 45 []).getD j 0) []))) := by decide

theorem alnAll_45_45_4 : ∀ j, j < (repChars.getD 45 []).length →
    (normIsRep.getD 45 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_45_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 45 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_45_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 45 []).getD ((alnPos.getD 45 []).getD j 0) []))) := by decide

theorem alnAll_45_45_5 : ∀ j, j < (repChars.getD 45 []).length →
    (normIsRep.getD 45 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_45_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 45 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_45_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 45 []).getD ((alnPos.getD 45 []).getD j 0) []))) := by decide

theorem alnAll_45_45_10 : ∀ j, j < (repChars.getD 45 []).length →
    (normIsRep.getD 45 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_45_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 45 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_45_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 45 []).getD ((alnPos.getD 45 []).getD j 0) []))) := by decide

theorem alnAll_45_45_15 : ∀ j, j < (repChars.getD 45 []).length →
    (normIsRep.getD 45 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_45_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 45 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_45_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 45 []).getD ((alnPos.getD 45 []).getD j 0) []))) := by decide

theorem alnAll_45_45_20 : ∀ j, j < (repChars.getD 45 []).length →
    (normIsRep.getD 45 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_45_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 45 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_45_45_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 45 []).getD ((alnPos.getD 45 []).getD j 0) []))) := by decide

theorem alnAll_46_0_0 : ∀ j, j < (repChars.getD 46 []).length →
    (normIsRep.getD 46 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_0_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 46 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_0_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 46 []).getD ((alnPos.getD 46 []).getD j 0) []))) := by decide

theorem alnAll_46_12_0 : ∀ j, j < (repChars.getD 46 []).length →
    (normIsRep.getD 46 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_12_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 46 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_12_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 46 []).getD ((alnPos.getD 46 []).getD j 0) []))) := by decide

theorem alnAll_46_12_1 : ∀ j, j < (repChars.getD 46 []).length →
    (normIsRep.getD 46 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_12_1.D (m := 125))
        (List.map ZMod.val ((repChars.getD 46 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_12_1.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 46 []).getD ((alnPos.getD 46 []).getD j 0) []))) := by decide

theorem alnAll_46_12_2 : ∀ j, j < (repChars.getD 46 []).length →
    (normIsRep.getD 46 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_12_2.D (m := 125))
        (List.map ZMod.val ((repChars.getD 46 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_12_2.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 46 []).getD ((alnPos.getD 46 []).getD j 0) []))) := by decide

theorem alnAll_46_12_3 : ∀ j, j < (repChars.getD 46 []).length →
    (normIsRep.getD 46 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_12_3.D (m := 125))
        (List.map ZMod.val ((repChars.getD 46 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_12_3.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 46 []).getD ((alnPos.getD 46 []).getD j 0) []))) := by decide

theorem alnAll_46_12_4 : ∀ j, j < (repChars.getD 46 []).length →
    (normIsRep.getD 46 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_12_4.D (m := 125))
        (List.map ZMod.val ((repChars.getD 46 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_12_4.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 46 []).getD ((alnPos.getD 46 []).getD j 0) []))) := by decide

theorem alnAll_46_46_0 : ∀ j, j < (repChars.getD 46 []).length →
    (normIsRep.getD 46 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_46_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 46 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_46_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 46 []).getD ((alnPos.getD 46 []).getD j 0) []))) := by decide

theorem alnAll_46_46_1 : ∀ j, j < (repChars.getD 46 []).length →
    (normIsRep.getD 46 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_46_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 46 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_46_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 46 []).getD ((alnPos.getD 46 []).getD j 0) []))) := by decide

theorem alnAll_46_46_2 : ∀ j, j < (repChars.getD 46 []).length →
    (normIsRep.getD 46 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_46_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 46 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_46_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 46 []).getD ((alnPos.getD 46 []).getD j 0) []))) := by decide

theorem alnAll_46_46_3 : ∀ j, j < (repChars.getD 46 []).length →
    (normIsRep.getD 46 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_46_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 46 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_46_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 46 []).getD ((alnPos.getD 46 []).getD j 0) []))) := by decide

theorem alnAll_46_46_4 : ∀ j, j < (repChars.getD 46 []).length →
    (normIsRep.getD 46 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_46_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 46 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_46_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 46 []).getD ((alnPos.getD 46 []).getD j 0) []))) := by decide

theorem alnAll_46_46_5 : ∀ j, j < (repChars.getD 46 []).length →
    (normIsRep.getD 46 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_46_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 46 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_46_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 46 []).getD ((alnPos.getD 46 []).getD j 0) []))) := by decide

theorem alnAll_46_46_10 : ∀ j, j < (repChars.getD 46 []).length →
    (normIsRep.getD 46 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_46_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 46 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_46_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 46 []).getD ((alnPos.getD 46 []).getD j 0) []))) := by decide

theorem alnAll_46_46_15 : ∀ j, j < (repChars.getD 46 []).length →
    (normIsRep.getD 46 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_46_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 46 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_46_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 46 []).getD ((alnPos.getD 46 []).getD j 0) []))) := by decide

theorem alnAll_46_46_20 : ∀ j, j < (repChars.getD 46 []).length →
    (normIsRep.getD 46 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_46_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 46 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_46_46_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 46 []).getD ((alnPos.getD 46 []).getD j 0) []))) := by decide

end LeanDring.P5Presentation
