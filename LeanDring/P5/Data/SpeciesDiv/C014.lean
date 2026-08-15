/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntrySupport
import LeanDring.P5.Certificate.Characters.Twin1.CharAssembly
import LeanDring.P5.Certificate.Characters.Twin2.CharAssembly
import LeanDring.P5.Data.ColCdd.C012
import LeanDring.P5.Data.ColCdd.C013

/-!
# Species-table cells, stages 3-4 — residual real-decide certificates (divergent columns).
Auto-emitted by python/p5_stage34_emit.py. Chunk 13: 28 columns.
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

theorem colCertDiv_128_90_75_match :
    ((Q2.charsAt2 ⟨128, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_128_90_75.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_128_90_75.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_128_90_100_match :
    ((Q2.charsAt2 ⟨128, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_128_90_100.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_128_90_100.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_128_96_5_match :
    ((Q2.charsAt2 ⟨128, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_128_96_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_128_96_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_128_96_10_match :
    ((Q2.charsAt2 ⟨128, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_128_96_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_128_96_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_128_96_15_match :
    ((Q2.charsAt2 ⟨128, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_128_96_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_128_96_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_128_96_20_match :
    ((Q2.charsAt2 ⟨128, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_128_96_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_128_96_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_128_103_5_match :
    ((Q2.charsAt2 ⟨128, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_128_103_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_128_103_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_128_103_15_match :
    ((Q2.charsAt2 ⟨128, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_128_103_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_128_103_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_128_109_5_match :
    ((Q2.charsAt2 ⟨128, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_128_109_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_128_109_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_128_109_10_match :
    ((Q2.charsAt2 ⟨128, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_128_109_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_128_109_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_128_109_15_match :
    ((Q2.charsAt2 ⟨128, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_128_109_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_128_109_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_128_109_20_match :
    ((Q2.charsAt2 ⟨128, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_128_109_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_128_109_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_128_112_15_match :
    ((Q2.charsAt2 ⟨128, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_128_112_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_128_112_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_128_112_20_match :
    ((Q2.charsAt2 ⟨128, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_128_112_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_128_112_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_129_29_10_match :
    ((Q2.charsAt2 ⟨129, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_129_29_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_129_29_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_129_29_15_match :
    ((Q2.charsAt2 ⟨129, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_129_29_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_129_29_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_129_29_20_match :
    ((Q2.charsAt2 ⟨129, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_129_29_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_129_29_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_129_35_5_match :
    ((Q2.charsAt2 ⟨129, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_129_35_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_129_35_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_129_35_10_match :
    ((Q2.charsAt2 ⟨129, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_129_35_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_129_35_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_129_35_15_match :
    ((Q2.charsAt2 ⟨129, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_129_35_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_129_35_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_129_35_20_match :
    ((Q2.charsAt2 ⟨129, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_129_35_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_129_35_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_129_42_5_match :
    ((Q2.charsAt2 ⟨129, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_129_42_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_129_42_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_129_42_10_match :
    ((Q2.charsAt2 ⟨129, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_129_42_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_129_42_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_129_42_15_match :
    ((Q2.charsAt2 ⟨129, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_129_42_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_129_42_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_129_42_20_match :
    ((Q2.charsAt2 ⟨129, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_129_42_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_129_42_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_129_43_5_match :
    ((Q2.charsAt2 ⟨129, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_129_43_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_129_43_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_129_43_10_match :
    ((Q2.charsAt2 ⟨129, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_129_43_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_129_43_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_129_43_15_match :
    ((Q2.charsAt2 ⟨129, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_129_43_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_129_43_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

end LeanDring.P5Presentation
