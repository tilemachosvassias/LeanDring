/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharAlign
import LeanDring.P5.Data.ColRestCheap.C151
import LeanDring.P5.Data.ColRestCheap.C152

/-!
# Species-table cells, α-paired residual decides, chunk 12

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

theorem alnAll_64_34_10 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_34_10.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_34_10.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_34_15 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_34_15.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_34_15.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_34_20 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_34_20.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_34_20.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_39_0 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_39_0.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_39_0.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_39_1 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_39_1.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_39_1.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_39_2 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_39_2.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_39_2.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_39_3 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_39_3.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_39_3.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_39_4 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_39_4.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_39_4.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_39_5 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_39_5.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_39_5.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_39_10 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_39_10.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_39_10.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_39_15 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_39_15.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_39_15.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_39_20 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_39_20.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_39_20.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_44_0 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_44_0.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_44_0.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_44_1 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_44_1.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_44_1.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_44_2 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_44_2.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_44_2.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_44_3 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_44_3.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_44_3.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_44_4 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_44_4.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_44_4.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_44_5 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_44_5.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_44_5.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_44_10 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_44_10.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_44_10.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_44_15 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_44_15.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_44_15.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_44_20 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_44_20.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_44_20.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_49_0 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_49_0.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_49_0.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_49_1 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_49_1.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_49_1.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_49_2 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_49_2.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_49_2.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_49_3 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_49_3.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_49_3.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_49_4 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_49_4.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_49_4.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_49_5 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_49_5.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_49_5.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_49_10 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_49_10.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_49_10.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_49_15 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_49_15.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_49_15.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_49_20 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_49_20.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_49_20.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_0 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_0.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_0.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_1 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_1.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_1.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_2 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_2.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_2.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_3 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_3.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_3.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_4 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_4.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_4.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_5 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_5.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_5.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_6 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_6.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_6.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_7 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_7.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_7.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_8 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_8.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_8.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_9 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_9.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_9.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_10 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_10.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_10.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_11 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_11.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_11.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_12 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_12.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_12.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_13 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_13.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_13.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_14 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_14.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_14.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_15 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_15.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_15.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_16 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_16.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_16.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_17 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_17.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_17.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_18 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_18.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_18.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_19 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_19.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_19.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_20 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_20.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_20.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_21 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_21.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_21.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_22 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_22.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_22.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_23 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_23.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_23.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_24 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_24.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_24.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_25 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_25.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_25.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_30 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_30.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_30.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_64_35 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_35.D (m := 5))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_64_35.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

end LeanDring.P5Presentation
