/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharAlign
import LeanDring.P5.Data.ColRestCheap.C006
import LeanDring.P5.Data.ColRestCheap.C007
import LeanDring.P5.Data.ColRestHeavy.C025
import LeanDring.P5.Data.ColRestHeavy.C026
import LeanDring.P5.Data.ColRestHeavy.C027

/-!
# Species-table cells, α-paired residual decides, chunk 5

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

theorem alnAll_39_39_10 : ∀ j, j < (repChars.getD 39 []).length →
    (normIsRep.getD 39 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_39_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 39 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_39_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 39 []).getD ((alnPos.getD 39 []).getD j 0) []))) := by decide

theorem alnAll_39_39_15 : ∀ j, j < (repChars.getD 39 []).length →
    (normIsRep.getD 39 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_39_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 39 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_39_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 39 []).getD ((alnPos.getD 39 []).getD j 0) []))) := by decide

theorem alnAll_39_39_20 : ∀ j, j < (repChars.getD 39 []).length →
    (normIsRep.getD 39 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_39_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 39 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_39_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 39 []).getD ((alnPos.getD 39 []).getD j 0) []))) := by decide

theorem alnAll_40_0_0 : ∀ j, j < (repChars.getD 40 []).length →
    (normIsRep.getD 40 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_0_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 40 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_0_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 40 []).getD ((alnPos.getD 40 []).getD j 0) []))) := by decide

theorem alnAll_40_12_0 : ∀ j, j < (repChars.getD 40 []).length →
    (normIsRep.getD 40 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_12_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 40 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_12_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 40 []).getD ((alnPos.getD 40 []).getD j 0) []))) := by decide

theorem alnAll_40_12_1 : ∀ j, j < (repChars.getD 40 []).length →
    (normIsRep.getD 40 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_12_1.D (m := 125))
        (List.map ZMod.val ((repChars.getD 40 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_12_1.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 40 []).getD ((alnPos.getD 40 []).getD j 0) []))) := by decide

theorem alnAll_40_12_2 : ∀ j, j < (repChars.getD 40 []).length →
    (normIsRep.getD 40 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_12_2.D (m := 125))
        (List.map ZMod.val ((repChars.getD 40 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_12_2.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 40 []).getD ((alnPos.getD 40 []).getD j 0) []))) := by decide

theorem alnAll_40_12_3 : ∀ j, j < (repChars.getD 40 []).length →
    (normIsRep.getD 40 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_12_3.D (m := 125))
        (List.map ZMod.val ((repChars.getD 40 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_12_3.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 40 []).getD ((alnPos.getD 40 []).getD j 0) []))) := by decide

theorem alnAll_40_12_4 : ∀ j, j < (repChars.getD 40 []).length →
    (normIsRep.getD 40 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_12_4.D (m := 125))
        (List.map ZMod.val ((repChars.getD 40 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_12_4.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 40 []).getD ((alnPos.getD 40 []).getD j 0) []))) := by decide

theorem alnAll_40_40_0 : ∀ j, j < (repChars.getD 40 []).length →
    (normIsRep.getD 40 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_40_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 40 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_40_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 40 []).getD ((alnPos.getD 40 []).getD j 0) []))) := by decide

theorem alnAll_40_40_1 : ∀ j, j < (repChars.getD 40 []).length →
    (normIsRep.getD 40 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_40_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 40 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_40_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 40 []).getD ((alnPos.getD 40 []).getD j 0) []))) := by decide

theorem alnAll_40_40_2 : ∀ j, j < (repChars.getD 40 []).length →
    (normIsRep.getD 40 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_40_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 40 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_40_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 40 []).getD ((alnPos.getD 40 []).getD j 0) []))) := by decide

theorem alnAll_40_40_3 : ∀ j, j < (repChars.getD 40 []).length →
    (normIsRep.getD 40 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_40_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 40 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_40_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 40 []).getD ((alnPos.getD 40 []).getD j 0) []))) := by decide

theorem alnAll_40_40_4 : ∀ j, j < (repChars.getD 40 []).length →
    (normIsRep.getD 40 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_40_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 40 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_40_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 40 []).getD ((alnPos.getD 40 []).getD j 0) []))) := by decide

theorem alnAll_40_40_5 : ∀ j, j < (repChars.getD 40 []).length →
    (normIsRep.getD 40 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_40_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 40 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_40_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 40 []).getD ((alnPos.getD 40 []).getD j 0) []))) := by decide

theorem alnAll_40_40_10 : ∀ j, j < (repChars.getD 40 []).length →
    (normIsRep.getD 40 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_40_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 40 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_40_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 40 []).getD ((alnPos.getD 40 []).getD j 0) []))) := by decide

theorem alnAll_40_40_15 : ∀ j, j < (repChars.getD 40 []).length →
    (normIsRep.getD 40 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_40_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 40 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_40_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 40 []).getD ((alnPos.getD 40 []).getD j 0) []))) := by decide

theorem alnAll_40_40_20 : ∀ j, j < (repChars.getD 40 []).length →
    (normIsRep.getD 40 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_40_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 40 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_40_40_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 40 []).getD ((alnPos.getD 40 []).getD j 0) []))) := by decide

theorem alnAll_41_0_0 : ∀ j, j < (repChars.getD 41 []).length →
    (normIsRep.getD 41 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_0_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 41 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_0_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 41 []).getD ((alnPos.getD 41 []).getD j 0) []))) := by decide

theorem alnAll_41_12_0 : ∀ j, j < (repChars.getD 41 []).length →
    (normIsRep.getD 41 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_12_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 41 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_12_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 41 []).getD ((alnPos.getD 41 []).getD j 0) []))) := by decide

theorem alnAll_41_12_1 : ∀ j, j < (repChars.getD 41 []).length →
    (normIsRep.getD 41 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_12_1.D (m := 125))
        (List.map ZMod.val ((repChars.getD 41 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_12_1.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 41 []).getD ((alnPos.getD 41 []).getD j 0) []))) := by decide

theorem alnAll_41_12_2 : ∀ j, j < (repChars.getD 41 []).length →
    (normIsRep.getD 41 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_12_2.D (m := 125))
        (List.map ZMod.val ((repChars.getD 41 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_12_2.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 41 []).getD ((alnPos.getD 41 []).getD j 0) []))) := by decide

theorem alnAll_41_12_3 : ∀ j, j < (repChars.getD 41 []).length →
    (normIsRep.getD 41 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_12_3.D (m := 125))
        (List.map ZMod.val ((repChars.getD 41 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_12_3.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 41 []).getD ((alnPos.getD 41 []).getD j 0) []))) := by decide

theorem alnAll_41_12_4 : ∀ j, j < (repChars.getD 41 []).length →
    (normIsRep.getD 41 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_12_4.D (m := 125))
        (List.map ZMod.val ((repChars.getD 41 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_12_4.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 41 []).getD ((alnPos.getD 41 []).getD j 0) []))) := by decide

theorem alnAll_41_41_0 : ∀ j, j < (repChars.getD 41 []).length →
    (normIsRep.getD 41 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_41_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 41 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_41_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 41 []).getD ((alnPos.getD 41 []).getD j 0) []))) := by decide

theorem alnAll_41_41_1 : ∀ j, j < (repChars.getD 41 []).length →
    (normIsRep.getD 41 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_41_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 41 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_41_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 41 []).getD ((alnPos.getD 41 []).getD j 0) []))) := by decide

theorem alnAll_41_41_2 : ∀ j, j < (repChars.getD 41 []).length →
    (normIsRep.getD 41 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_41_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 41 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_41_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 41 []).getD ((alnPos.getD 41 []).getD j 0) []))) := by decide

theorem alnAll_41_41_3 : ∀ j, j < (repChars.getD 41 []).length →
    (normIsRep.getD 41 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_41_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 41 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_41_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 41 []).getD ((alnPos.getD 41 []).getD j 0) []))) := by decide

theorem alnAll_41_41_4 : ∀ j, j < (repChars.getD 41 []).length →
    (normIsRep.getD 41 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_41_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 41 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_41_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 41 []).getD ((alnPos.getD 41 []).getD j 0) []))) := by decide

theorem alnAll_41_41_5 : ∀ j, j < (repChars.getD 41 []).length →
    (normIsRep.getD 41 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_41_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 41 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_41_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 41 []).getD ((alnPos.getD 41 []).getD j 0) []))) := by decide

theorem alnAll_41_41_10 : ∀ j, j < (repChars.getD 41 []).length →
    (normIsRep.getD 41 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_41_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 41 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_41_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 41 []).getD ((alnPos.getD 41 []).getD j 0) []))) := by decide

theorem alnAll_41_41_15 : ∀ j, j < (repChars.getD 41 []).length →
    (normIsRep.getD 41 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_41_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 41 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_41_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 41 []).getD ((alnPos.getD 41 []).getD j 0) []))) := by decide

theorem alnAll_41_41_20 : ∀ j, j < (repChars.getD 41 []).length →
    (normIsRep.getD 41 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_41_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 41 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_41_41_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 41 []).getD ((alnPos.getD 41 []).getD j 0) []))) := by decide

theorem alnAll_42_0_0 : ∀ j, j < (repChars.getD 42 []).length →
    (normIsRep.getD 42 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_0_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 42 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_0_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 42 []).getD ((alnPos.getD 42 []).getD j 0) []))) := by decide

theorem alnAll_42_12_0 : ∀ j, j < (repChars.getD 42 []).length →
    (normIsRep.getD 42 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_12_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 42 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_12_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 42 []).getD ((alnPos.getD 42 []).getD j 0) []))) := by decide

end LeanDring.P5Presentation
