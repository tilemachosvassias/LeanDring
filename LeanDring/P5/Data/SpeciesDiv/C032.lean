/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntrySupport
import LeanDring.P5.Certificate.Characters.Twin1.CharAssembly
import LeanDring.P5.Certificate.Characters.Twin2.CharAssembly
import LeanDring.P5.Data.ColCdd.C003

/-!
# Species-table cells, stages 3-4 — residual real-decide certificates (divergent columns).
Auto-emitted by python/p5_stage34_emit.py. Chunk 31: 28 columns.
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

theorem colCertDiv_116_58_18_match :
    ((Q2.charsAt2 ⟨116, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_116_58_18.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_116_58_18.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_116_58_19_match :
    ((Q2.charsAt2 ⟨116, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_116_58_19.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_116_58_19.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_116_58_20_match :
    ((Q2.charsAt2 ⟨116, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_116_58_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_116_58_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_116_58_21_match :
    ((Q2.charsAt2 ⟨116, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_116_58_21.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_116_58_21.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_116_58_22_match :
    ((Q2.charsAt2 ⟨116, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_116_58_22.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_116_58_22.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_116_58_23_match :
    ((Q2.charsAt2 ⟨116, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_116_58_23.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_116_58_23.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_116_58_24_match :
    ((Q2.charsAt2 ⟨116, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_116_58_24.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_116_58_24.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_117_63_5_match :
    ((Q2.charsAt2 ⟨117, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_117_63_6_match :
    ((Q2.charsAt2 ⟨117, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_6.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_6.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_117_63_7_match :
    ((Q2.charsAt2 ⟨117, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_7.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_7.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_117_63_8_match :
    ((Q2.charsAt2 ⟨117, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_8.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_8.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_117_63_9_match :
    ((Q2.charsAt2 ⟨117, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_9.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_9.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_117_63_10_match :
    ((Q2.charsAt2 ⟨117, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_117_63_11_match :
    ((Q2.charsAt2 ⟨117, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_11.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_11.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_117_63_12_match :
    ((Q2.charsAt2 ⟨117, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_12.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_12.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_117_63_13_match :
    ((Q2.charsAt2 ⟨117, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_13.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_13.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_117_63_14_match :
    ((Q2.charsAt2 ⟨117, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_14.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_14.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_117_63_15_match :
    ((Q2.charsAt2 ⟨117, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_117_63_16_match :
    ((Q2.charsAt2 ⟨117, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_16.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_16.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_117_63_17_match :
    ((Q2.charsAt2 ⟨117, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_17.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_17.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_117_63_18_match :
    ((Q2.charsAt2 ⟨117, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_18.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_18.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_117_63_19_match :
    ((Q2.charsAt2 ⟨117, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_19.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_19.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_117_63_20_match :
    ((Q2.charsAt2 ⟨117, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_117_63_21_match :
    ((Q2.charsAt2 ⟨117, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_21.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_21.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_117_63_22_match :
    ((Q2.charsAt2 ⟨117, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_22.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_22.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_117_63_23_match :
    ((Q2.charsAt2 ⟨117, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_23.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_23.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_117_63_24_match :
    ((Q2.charsAt2 ⟨117, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_24.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_63_24.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_30_5_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_30_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_30_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

end LeanDring.P5Presentation
