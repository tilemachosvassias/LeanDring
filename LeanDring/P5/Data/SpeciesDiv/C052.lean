/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntrySupport
import LeanDring.P5.Certificate.Characters.Twin1.CharAssembly
import LeanDring.P5.Certificate.Characters.Twin2.CharAssembly
import LeanDring.P5.Data.ColCdd.C005

/-!
# Species-table cells, stages 3-4 — residual real-decide certificates (divergent columns).
Auto-emitted by python/p5_stage34_emit.py. Chunk 51: 28 columns.
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

theorem colCertDiv_119_70_15_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_70_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_70_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_70_16_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_70_16.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_70_16.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_70_17_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_70_17.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_70_17.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_70_18_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_70_18.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_70_18.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_70_19_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_70_19.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_70_19.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_70_20_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_70_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_70_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_70_21_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_70_21.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_70_21.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_70_22_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_70_22.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_70_22.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_70_23_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_70_23.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_70_23.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_70_24_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_70_24.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_70_24.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_71_5_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_71_6_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_6.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_6.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_71_7_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_7.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_7.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_71_8_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_8.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_8.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_71_9_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_9.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_9.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_71_10_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_71_11_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_11.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_11.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_71_12_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_12.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_12.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_71_13_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_13.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_13.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_71_14_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_14.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_14.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_71_15_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_71_16_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_16.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_16.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_71_17_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_17.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_17.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_71_18_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_18.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_18.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_71_19_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_19.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_19.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_71_20_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_71_21_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_21.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_21.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_71_22_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_22.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_71_22.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

end LeanDring.P5Presentation
