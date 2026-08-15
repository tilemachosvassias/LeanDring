/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntrySupport
import LeanDring.P5.Certificate.Characters.Twin1.CharAssembly
import LeanDring.P5.Certificate.Characters.Twin2.CharAssembly
import LeanDring.P5.Data.ColCdd.C004
import LeanDring.P5.Data.ColCdd.C031

/-!
# Species-table cells, stages 3-4 — residual real-decide certificates (divergent columns).
Auto-emitted by python/p5_stage34_emit.py. Chunk 40: 45 columns.
Each theorem: for every character vector of the row class, the two twins'
fast codes have equal cyclotomic value (identity row matching). Fed to
`species_eq_of_fastcode_eq` at stage-5 assembly.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem colCertDiv_118_66_15_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_66_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_66_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_66_16_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_66_16.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_66_16.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_66_17_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_66_17.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_66_17.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_66_18_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_66_18.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_66_18.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_66_19_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_66_19.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_66_19.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_66_20_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_66_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_66_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_66_21_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_66_21.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_66_21.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_66_22_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_66_22.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_66_22.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_66_23_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_66_23.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_66_23.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_66_24_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_66_24.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_66_24.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_68_5_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_68_6_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_6.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_6.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_68_7_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_7.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_7.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_68_8_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_8.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_8.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_68_9_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_9.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_9.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_68_10_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_68_11_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_11.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_11.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_68_12_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_12.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_12.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_68_13_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_13.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_13.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_68_14_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_14.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_14.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_68_15_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_68_16_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_16.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_16.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_68_17_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_17.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_17.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_68_18_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_18.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_18.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_68_23_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_23.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_23.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_68_24_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_24.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_24.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_78_11_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_11.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_11.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_78_12_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_12.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_12.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_78_13_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_13.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_13.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_78_14_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_14.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_14.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_78_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_78_16_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_16.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_16.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_78_17_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_17.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_17.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_78_18_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_18.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_18.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_78_19_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_19.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_19.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_78_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_78_21_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_21.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_21.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_78_22_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_22.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_22.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_78_23_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_23.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_23.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_78_24_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_24.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_24.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_91_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_91_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_91_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_91_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_91_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_91_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_91_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_91_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_91_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_92_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_92_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_92_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_92_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_92_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_92_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

end LeanDring.P5Presentation
