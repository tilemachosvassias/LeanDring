/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharAlign
import LeanDring.P5.Data.ColRestCheap.C170
import LeanDring.P5.Data.ColRestCheap.C191

/-!
# Species-table cells, α-paired residual decides, chunk 21

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

theorem alnAll_76_76_3 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_3.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_3.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_4 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_4.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_4.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_5 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_5.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_5.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_6 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_6.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_6.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_7 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_7.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_7.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_8 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_8.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_8.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_9 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_9.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_9.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_10 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_10.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_10.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_11 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_11.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_11.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_12 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_12.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_12.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_13 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_13.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_13.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_14 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_14.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_14.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_15 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_15.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_15.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_16 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_16.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_16.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_17 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_17.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_17.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_18 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_18.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_18.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_19 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_19.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_19.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_20 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_20.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_20.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_21 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_21.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_21.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_22 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_22.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_22.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_23 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_23.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_23.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_24 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_24.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_24.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_25 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_25.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_25.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_30 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_30.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_30.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_35 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_35.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_35.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_40 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_40.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_40.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_45 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_45.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_45.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_50 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_50.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_50.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_55 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_55.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_55.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_60 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_60.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_60.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_65 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_65.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_65.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_70 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_70.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_70.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_75 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_75.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_75.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_80 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_80.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_80.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_85 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_85.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_85.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_90 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_90.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_90.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_95 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_95.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_95.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_100 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_100.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_100.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_105 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_105.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_105.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_110 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_110.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_110.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_115 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_115.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_115.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_120 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_120.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_120.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_90_0_0 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_0_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_0_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_10_0 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_10_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_10_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_10_1 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_10_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_10_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_10_2 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_10_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_10_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_10_3 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_10_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_10_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_10_4 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_10_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_10_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_12_0 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_12_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_12_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_12_1 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_12_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_12_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_12_2 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_12_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_12_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_12_3 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_12_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_12_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_12_4 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_12_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_12_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_28_0 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_28_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_28_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_28_1 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_28_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_28_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_28_2 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_28_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_28_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_28_3 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_28_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_28_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

theorem alnAll_90_28_4 : ∀ j, j < (repChars.getD 90 []).length →
    (normIsRep.getD 90 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_28_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 90 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_90_28_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 90 []).getD ((alnPos.getD 90 []).getD j 0) []))) := by decide

end LeanDring.P5Presentation
