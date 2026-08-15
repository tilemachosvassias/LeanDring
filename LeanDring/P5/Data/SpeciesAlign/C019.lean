/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharAlign
import LeanDring.P5.Data.ColCdd.C039
import LeanDring.P5.Data.ColRestCheap.C165
import LeanDring.P5.Data.ColRestCheap.C166
import LeanDring.P5.Data.ColRestCheap.C168

/-!
# Species-table cells, α-paired residual decides, chunk 18

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

theorem alnAll_73_51_1 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_51_1.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_51_1.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_51_2 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_51_2.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_51_2.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_51_3 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_51_3.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_51_3.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_51_4 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_51_4.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_51_4.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_51_5 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_51_5.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_51_5.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_51_10 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_51_10.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_51_10.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_51_15 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_51_15.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_51_15.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_51_20 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_51_20.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_51_20.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_0 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_0.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_0.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_1 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_1.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_1.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_2 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_2.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_2.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_3 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_3.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_3.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_4 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_4.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_4.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_5 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_5.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_5.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_6 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_6.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_6.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_7 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_7.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_7.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_8 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_8.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_8.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_9 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_9.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_9.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_10 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_10.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_10.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_11 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_11.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_11.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_12 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_12.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_12.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_13 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_13.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_13.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_14 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_14.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_14.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_15 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_15.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_15.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_16 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_16.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_16.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_17 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_17.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_17.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_18 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_18.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_18.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_19 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_19.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_19.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_20 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_20.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_20.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_21 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_21.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_21.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_22 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_22.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_22.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_23 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_23.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_23.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_24 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_24.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_24.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_25 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_25.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_25.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_30 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_30.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_30.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_35 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_35.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_35.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_40 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_40.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_40.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_45 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_45.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_45.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_50 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_50.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_50.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_55 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_55.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_55.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_60 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_60.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_60.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_65 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_65.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_65.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_70 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_70.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_70.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_75 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_75.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_75.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_80 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_80.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_80.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_85 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_85.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_85.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_90 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_90.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_90.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_95 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_95.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_95.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_100 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_100.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_100.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_105 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_105.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_105.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_110 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_110.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_110.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_115 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_115.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_115.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_73_120 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_120.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_73_120.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_76_0_0 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_0_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_0_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

end LeanDring.P5Presentation
