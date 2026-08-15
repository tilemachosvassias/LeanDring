/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharAlign
import LeanDring.P5.Data.ColRestCheap.C006
import LeanDring.P5.Data.ColRestHeavy.C024
import LeanDring.P5.Data.ColRestHeavy.C025

/-!
# Species-table cells, α-paired residual decides, chunk 4

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

theorem alnAll_37_12_3 : ∀ j, j < (repChars.getD 37 []).length →
    (normIsRep.getD 37 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_12_3.D (m := 125))
        (List.map ZMod.val ((repChars.getD 37 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_12_3.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 37 []).getD ((alnPos.getD 37 []).getD j 0) []))) := by decide

theorem alnAll_37_12_4 : ∀ j, j < (repChars.getD 37 []).length →
    (normIsRep.getD 37 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_12_4.D (m := 125))
        (List.map ZMod.val ((repChars.getD 37 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_12_4.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 37 []).getD ((alnPos.getD 37 []).getD j 0) []))) := by decide

theorem alnAll_37_37_0 : ∀ j, j < (repChars.getD 37 []).length →
    (normIsRep.getD 37 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_37_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 37 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_37_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 37 []).getD ((alnPos.getD 37 []).getD j 0) []))) := by decide

theorem alnAll_37_37_1 : ∀ j, j < (repChars.getD 37 []).length →
    (normIsRep.getD 37 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_37_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 37 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_37_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 37 []).getD ((alnPos.getD 37 []).getD j 0) []))) := by decide

theorem alnAll_37_37_2 : ∀ j, j < (repChars.getD 37 []).length →
    (normIsRep.getD 37 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_37_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 37 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_37_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 37 []).getD ((alnPos.getD 37 []).getD j 0) []))) := by decide

theorem alnAll_37_37_3 : ∀ j, j < (repChars.getD 37 []).length →
    (normIsRep.getD 37 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_37_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 37 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_37_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 37 []).getD ((alnPos.getD 37 []).getD j 0) []))) := by decide

theorem alnAll_37_37_4 : ∀ j, j < (repChars.getD 37 []).length →
    (normIsRep.getD 37 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_37_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 37 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_37_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 37 []).getD ((alnPos.getD 37 []).getD j 0) []))) := by decide

theorem alnAll_37_37_5 : ∀ j, j < (repChars.getD 37 []).length →
    (normIsRep.getD 37 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_37_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 37 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_37_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 37 []).getD ((alnPos.getD 37 []).getD j 0) []))) := by decide

theorem alnAll_37_37_10 : ∀ j, j < (repChars.getD 37 []).length →
    (normIsRep.getD 37 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_37_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 37 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_37_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 37 []).getD ((alnPos.getD 37 []).getD j 0) []))) := by decide

theorem alnAll_37_37_15 : ∀ j, j < (repChars.getD 37 []).length →
    (normIsRep.getD 37 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_37_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 37 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_37_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 37 []).getD ((alnPos.getD 37 []).getD j 0) []))) := by decide

theorem alnAll_37_37_20 : ∀ j, j < (repChars.getD 37 []).length →
    (normIsRep.getD 37 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_37_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 37 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_37_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 37 []).getD ((alnPos.getD 37 []).getD j 0) []))) := by decide

theorem alnAll_38_0_0 : ∀ j, j < (repChars.getD 38 []).length →
    (normIsRep.getD 38 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_0_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 38 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_0_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 38 []).getD ((alnPos.getD 38 []).getD j 0) []))) := by decide

theorem alnAll_38_12_0 : ∀ j, j < (repChars.getD 38 []).length →
    (normIsRep.getD 38 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_12_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 38 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_12_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 38 []).getD ((alnPos.getD 38 []).getD j 0) []))) := by decide

theorem alnAll_38_12_1 : ∀ j, j < (repChars.getD 38 []).length →
    (normIsRep.getD 38 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_12_1.D (m := 125))
        (List.map ZMod.val ((repChars.getD 38 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_12_1.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 38 []).getD ((alnPos.getD 38 []).getD j 0) []))) := by decide

theorem alnAll_38_12_2 : ∀ j, j < (repChars.getD 38 []).length →
    (normIsRep.getD 38 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_12_2.D (m := 125))
        (List.map ZMod.val ((repChars.getD 38 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_12_2.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 38 []).getD ((alnPos.getD 38 []).getD j 0) []))) := by decide

theorem alnAll_38_12_3 : ∀ j, j < (repChars.getD 38 []).length →
    (normIsRep.getD 38 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_12_3.D (m := 125))
        (List.map ZMod.val ((repChars.getD 38 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_12_3.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 38 []).getD ((alnPos.getD 38 []).getD j 0) []))) := by decide

theorem alnAll_38_12_4 : ∀ j, j < (repChars.getD 38 []).length →
    (normIsRep.getD 38 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_12_4.D (m := 125))
        (List.map ZMod.val ((repChars.getD 38 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_12_4.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 38 []).getD ((alnPos.getD 38 []).getD j 0) []))) := by decide

theorem alnAll_38_38_0 : ∀ j, j < (repChars.getD 38 []).length →
    (normIsRep.getD 38 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_38_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 38 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_38_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 38 []).getD ((alnPos.getD 38 []).getD j 0) []))) := by decide

theorem alnAll_38_38_1 : ∀ j, j < (repChars.getD 38 []).length →
    (normIsRep.getD 38 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_38_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 38 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_38_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 38 []).getD ((alnPos.getD 38 []).getD j 0) []))) := by decide

theorem alnAll_38_38_2 : ∀ j, j < (repChars.getD 38 []).length →
    (normIsRep.getD 38 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_38_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 38 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_38_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 38 []).getD ((alnPos.getD 38 []).getD j 0) []))) := by decide

theorem alnAll_38_38_3 : ∀ j, j < (repChars.getD 38 []).length →
    (normIsRep.getD 38 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_38_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 38 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_38_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 38 []).getD ((alnPos.getD 38 []).getD j 0) []))) := by decide

theorem alnAll_38_38_4 : ∀ j, j < (repChars.getD 38 []).length →
    (normIsRep.getD 38 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_38_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 38 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_38_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 38 []).getD ((alnPos.getD 38 []).getD j 0) []))) := by decide

theorem alnAll_38_38_5 : ∀ j, j < (repChars.getD 38 []).length →
    (normIsRep.getD 38 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_38_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 38 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_38_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 38 []).getD ((alnPos.getD 38 []).getD j 0) []))) := by decide

theorem alnAll_38_38_10 : ∀ j, j < (repChars.getD 38 []).length →
    (normIsRep.getD 38 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_38_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 38 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_38_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 38 []).getD ((alnPos.getD 38 []).getD j 0) []))) := by decide

theorem alnAll_38_38_15 : ∀ j, j < (repChars.getD 38 []).length →
    (normIsRep.getD 38 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_38_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 38 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_38_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 38 []).getD ((alnPos.getD 38 []).getD j 0) []))) := by decide

theorem alnAll_38_38_20 : ∀ j, j < (repChars.getD 38 []).length →
    (normIsRep.getD 38 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_38_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 38 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_38_38_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 38 []).getD ((alnPos.getD 38 []).getD j 0) []))) := by decide

theorem alnAll_39_0_0 : ∀ j, j < (repChars.getD 39 []).length →
    (normIsRep.getD 39 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_0_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 39 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_0_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 39 []).getD ((alnPos.getD 39 []).getD j 0) []))) := by decide

theorem alnAll_39_12_0 : ∀ j, j < (repChars.getD 39 []).length →
    (normIsRep.getD 39 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_12_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 39 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_12_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 39 []).getD ((alnPos.getD 39 []).getD j 0) []))) := by decide

theorem alnAll_39_12_1 : ∀ j, j < (repChars.getD 39 []).length →
    (normIsRep.getD 39 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_12_1.D (m := 125))
        (List.map ZMod.val ((repChars.getD 39 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_12_1.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 39 []).getD ((alnPos.getD 39 []).getD j 0) []))) := by decide

theorem alnAll_39_12_2 : ∀ j, j < (repChars.getD 39 []).length →
    (normIsRep.getD 39 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_12_2.D (m := 125))
        (List.map ZMod.val ((repChars.getD 39 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_12_2.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 39 []).getD ((alnPos.getD 39 []).getD j 0) []))) := by decide

theorem alnAll_39_12_3 : ∀ j, j < (repChars.getD 39 []).length →
    (normIsRep.getD 39 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_12_3.D (m := 125))
        (List.map ZMod.val ((repChars.getD 39 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_12_3.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 39 []).getD ((alnPos.getD 39 []).getD j 0) []))) := by decide

theorem alnAll_39_12_4 : ∀ j, j < (repChars.getD 39 []).length →
    (normIsRep.getD 39 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_12_4.D (m := 125))
        (List.map ZMod.val ((repChars.getD 39 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_12_4.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 39 []).getD ((alnPos.getD 39 []).getD j 0) []))) := by decide

theorem alnAll_39_39_0 : ∀ j, j < (repChars.getD 39 []).length →
    (normIsRep.getD 39 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_39_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 39 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_39_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 39 []).getD ((alnPos.getD 39 []).getD j 0) []))) := by decide

theorem alnAll_39_39_1 : ∀ j, j < (repChars.getD 39 []).length →
    (normIsRep.getD 39 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_39_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 39 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_39_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 39 []).getD ((alnPos.getD 39 []).getD j 0) []))) := by decide

theorem alnAll_39_39_2 : ∀ j, j < (repChars.getD 39 []).length →
    (normIsRep.getD 39 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_39_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 39 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_39_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 39 []).getD ((alnPos.getD 39 []).getD j 0) []))) := by decide

theorem alnAll_39_39_3 : ∀ j, j < (repChars.getD 39 []).length →
    (normIsRep.getD 39 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_39_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 39 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_39_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 39 []).getD ((alnPos.getD 39 []).getD j 0) []))) := by decide

theorem alnAll_39_39_4 : ∀ j, j < (repChars.getD 39 []).length →
    (normIsRep.getD 39 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_39_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 39 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_39_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 39 []).getD ((alnPos.getD 39 []).getD j 0) []))) := by decide

theorem alnAll_39_39_5 : ∀ j, j < (repChars.getD 39 []).length →
    (normIsRep.getD 39 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_39_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 39 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_39_39_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 39 []).getD ((alnPos.getD 39 []).getD j 0) []))) := by decide

end LeanDring.P5Presentation
