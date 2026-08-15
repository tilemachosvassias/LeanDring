/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharAlign
import LeanDring.P5.Data.ColRestCheap.C151

/-!
# Species-table cells, α-paired residual decides, chunk 11

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

theorem alnAll_64_12_2 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_12_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_12_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_12_3 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_12_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_12_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_12_4 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_12_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_12_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_26_0 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_26_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_26_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_26_1 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_26_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_26_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_26_2 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_26_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_26_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_26_3 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_26_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_26_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_26_4 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_26_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_26_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_26_5 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_26_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_26_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_26_10 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_26_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_26_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_26_15 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_26_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_26_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_26_20 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_26_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_26_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_29_0 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_29_0.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_29_0.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_29_1 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_29_1.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_29_1.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_29_2 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_29_2.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_29_2.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_29_3 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_29_3.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_29_3.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_29_4 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_29_4.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_29_4.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_29_5 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_29_5.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_29_5.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_29_10 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_29_10.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_29_10.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_29_15 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_29_15.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_29_15.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_29_20 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_29_20.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_29_20.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_34_0 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_34_0.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_34_0.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_34_1 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_34_1.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_34_1.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_34_2 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_34_2.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_34_2.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_34_3 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_34_3.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_34_3.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_34_4 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_34_4.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_34_4.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_34_5 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_34_5.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_34_5.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

end LeanDring.P5Presentation
