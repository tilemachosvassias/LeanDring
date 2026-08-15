/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharAlign
import LeanDring.P5.Data.ColRestCheap.C005
import LeanDring.P5.Data.ColRestHeavy.C016
import LeanDring.P5.Data.ColRestHeavy.C017
import LeanDring.P5.Data.ColRestHeavy.C018

/-!
# Species-table cells, α-paired residual decides, chunk 0

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

theorem alnAll_28_0_0 : ∀ j, j < (repChars.getD 28 []).length →
    (normIsRep.getD 28 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_0_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 28 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_0_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 28 []).getD ((alnPos.getD 28 []).getD j 0) []))) := by decide

theorem alnAll_28_12_0 : ∀ j, j < (repChars.getD 28 []).length →
    (normIsRep.getD 28 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_12_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 28 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_12_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 28 []).getD ((alnPos.getD 28 []).getD j 0) []))) := by decide

theorem alnAll_28_12_1 : ∀ j, j < (repChars.getD 28 []).length →
    (normIsRep.getD 28 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_12_1.D (m := 125))
        (List.map ZMod.val ((repChars.getD 28 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_12_1.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 28 []).getD ((alnPos.getD 28 []).getD j 0) []))) := by decide

theorem alnAll_28_12_2 : ∀ j, j < (repChars.getD 28 []).length →
    (normIsRep.getD 28 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_12_2.D (m := 125))
        (List.map ZMod.val ((repChars.getD 28 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_12_2.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 28 []).getD ((alnPos.getD 28 []).getD j 0) []))) := by decide

theorem alnAll_28_12_3 : ∀ j, j < (repChars.getD 28 []).length →
    (normIsRep.getD 28 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_12_3.D (m := 125))
        (List.map ZMod.val ((repChars.getD 28 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_12_3.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 28 []).getD ((alnPos.getD 28 []).getD j 0) []))) := by decide

theorem alnAll_28_12_4 : ∀ j, j < (repChars.getD 28 []).length →
    (normIsRep.getD 28 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_12_4.D (m := 125))
        (List.map ZMod.val ((repChars.getD 28 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_12_4.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 28 []).getD ((alnPos.getD 28 []).getD j 0) []))) := by decide

theorem alnAll_28_28_0 : ∀ j, j < (repChars.getD 28 []).length →
    (normIsRep.getD 28 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_28_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 28 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_28_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 28 []).getD ((alnPos.getD 28 []).getD j 0) []))) := by decide

theorem alnAll_28_28_1 : ∀ j, j < (repChars.getD 28 []).length →
    (normIsRep.getD 28 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_28_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 28 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_28_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 28 []).getD ((alnPos.getD 28 []).getD j 0) []))) := by decide

theorem alnAll_28_28_2 : ∀ j, j < (repChars.getD 28 []).length →
    (normIsRep.getD 28 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_28_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 28 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_28_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 28 []).getD ((alnPos.getD 28 []).getD j 0) []))) := by decide

theorem alnAll_28_28_3 : ∀ j, j < (repChars.getD 28 []).length →
    (normIsRep.getD 28 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_28_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 28 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_28_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 28 []).getD ((alnPos.getD 28 []).getD j 0) []))) := by decide

theorem alnAll_28_28_4 : ∀ j, j < (repChars.getD 28 []).length →
    (normIsRep.getD 28 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_28_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 28 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_28_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 28 []).getD ((alnPos.getD 28 []).getD j 0) []))) := by decide

theorem alnAll_28_28_5 : ∀ j, j < (repChars.getD 28 []).length →
    (normIsRep.getD 28 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_28_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 28 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_28_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 28 []).getD ((alnPos.getD 28 []).getD j 0) []))) := by decide

theorem alnAll_28_28_10 : ∀ j, j < (repChars.getD 28 []).length →
    (normIsRep.getD 28 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_28_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 28 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_28_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 28 []).getD ((alnPos.getD 28 []).getD j 0) []))) := by decide

theorem alnAll_28_28_15 : ∀ j, j < (repChars.getD 28 []).length →
    (normIsRep.getD 28 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_28_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 28 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_28_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 28 []).getD ((alnPos.getD 28 []).getD j 0) []))) := by decide

theorem alnAll_28_28_20 : ∀ j, j < (repChars.getD 28 []).length →
    (normIsRep.getD 28 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_28_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 28 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_28_28_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 28 []).getD ((alnPos.getD 28 []).getD j 0) []))) := by decide

theorem alnAll_29_0_0 : ∀ j, j < (repChars.getD 29 []).length →
    (normIsRep.getD 29 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_0_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 29 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_0_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 29 []).getD ((alnPos.getD 29 []).getD j 0) []))) := by decide

theorem alnAll_29_12_0 : ∀ j, j < (repChars.getD 29 []).length →
    (normIsRep.getD 29 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_12_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 29 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_12_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 29 []).getD ((alnPos.getD 29 []).getD j 0) []))) := by decide

theorem alnAll_29_12_1 : ∀ j, j < (repChars.getD 29 []).length →
    (normIsRep.getD 29 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_12_1.D (m := 125))
        (List.map ZMod.val ((repChars.getD 29 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_12_1.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 29 []).getD ((alnPos.getD 29 []).getD j 0) []))) := by decide

theorem alnAll_29_12_2 : ∀ j, j < (repChars.getD 29 []).length →
    (normIsRep.getD 29 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_12_2.D (m := 125))
        (List.map ZMod.val ((repChars.getD 29 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_12_2.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 29 []).getD ((alnPos.getD 29 []).getD j 0) []))) := by decide

theorem alnAll_29_12_3 : ∀ j, j < (repChars.getD 29 []).length →
    (normIsRep.getD 29 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_12_3.D (m := 125))
        (List.map ZMod.val ((repChars.getD 29 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_12_3.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 29 []).getD ((alnPos.getD 29 []).getD j 0) []))) := by decide

theorem alnAll_29_12_4 : ∀ j, j < (repChars.getD 29 []).length →
    (normIsRep.getD 29 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_12_4.D (m := 125))
        (List.map ZMod.val ((repChars.getD 29 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_12_4.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 29 []).getD ((alnPos.getD 29 []).getD j 0) []))) := by decide

theorem alnAll_29_29_0 : ∀ j, j < (repChars.getD 29 []).length →
    (normIsRep.getD 29 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_29_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 29 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_29_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 29 []).getD ((alnPos.getD 29 []).getD j 0) []))) := by decide

theorem alnAll_29_29_1 : ∀ j, j < (repChars.getD 29 []).length →
    (normIsRep.getD 29 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_29_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 29 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_29_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 29 []).getD ((alnPos.getD 29 []).getD j 0) []))) := by decide

theorem alnAll_29_29_2 : ∀ j, j < (repChars.getD 29 []).length →
    (normIsRep.getD 29 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_29_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 29 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_29_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 29 []).getD ((alnPos.getD 29 []).getD j 0) []))) := by decide

theorem alnAll_29_29_3 : ∀ j, j < (repChars.getD 29 []).length →
    (normIsRep.getD 29 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_29_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 29 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_29_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 29 []).getD ((alnPos.getD 29 []).getD j 0) []))) := by decide

theorem alnAll_29_29_4 : ∀ j, j < (repChars.getD 29 []).length →
    (normIsRep.getD 29 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_29_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 29 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_29_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 29 []).getD ((alnPos.getD 29 []).getD j 0) []))) := by decide

theorem alnAll_29_29_5 : ∀ j, j < (repChars.getD 29 []).length →
    (normIsRep.getD 29 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_29_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 29 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_29_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 29 []).getD ((alnPos.getD 29 []).getD j 0) []))) := by decide

theorem alnAll_29_29_10 : ∀ j, j < (repChars.getD 29 []).length →
    (normIsRep.getD 29 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_29_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 29 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_29_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 29 []).getD ((alnPos.getD 29 []).getD j 0) []))) := by decide

theorem alnAll_29_29_15 : ∀ j, j < (repChars.getD 29 []).length →
    (normIsRep.getD 29 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_29_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 29 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_29_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 29 []).getD ((alnPos.getD 29 []).getD j 0) []))) := by decide

theorem alnAll_29_29_20 : ∀ j, j < (repChars.getD 29 []).length →
    (normIsRep.getD 29 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_29_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 29 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_29_29_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 29 []).getD ((alnPos.getD 29 []).getD j 0) []))) := by decide

theorem alnAll_30_0_0 : ∀ j, j < (repChars.getD 30 []).length →
    (normIsRep.getD 30 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_0_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 30 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_0_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 30 []).getD ((alnPos.getD 30 []).getD j 0) []))) := by decide

theorem alnAll_30_12_0 : ∀ j, j < (repChars.getD 30 []).length →
    (normIsRep.getD 30 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_12_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 30 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_12_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 30 []).getD ((alnPos.getD 30 []).getD j 0) []))) := by decide

theorem alnAll_30_12_1 : ∀ j, j < (repChars.getD 30 []).length →
    (normIsRep.getD 30 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_12_1.D (m := 125))
        (List.map ZMod.val ((repChars.getD 30 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_12_1.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 30 []).getD ((alnPos.getD 30 []).getD j 0) []))) := by decide

end LeanDring.P5Presentation
