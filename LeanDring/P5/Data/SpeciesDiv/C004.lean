/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntrySupport
import LeanDring.P5.Certificate.Characters.Twin1.CharAssembly
import LeanDring.P5.Certificate.Characters.Twin2.CharAssembly
import LeanDring.P5.Data.ColCdd.C001

/-!
# Species-table cells, stages 3-4 — residual real-decide certificates (divergent columns).
Auto-emitted by python/p5_stage34_emit.py. Chunk 3: 7 columns.
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

theorem colCertDiv_108_46_10_match :
    ((Q2.charsAt2 ⟨108, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_108_46_10.D2 (m := 25)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_108_46_10.D1 (m := 25)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_108_46_15_match :
    ((Q2.charsAt2 ⟨108, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_108_46_15.D2 (m := 25)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_108_46_15.D1 (m := 25)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_108_46_20_match :
    ((Q2.charsAt2 ⟨108, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_108_46_20.D2 (m := 25)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_108_46_20.D1 (m := 25)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_109_47_5_match :
    ((Q2.charsAt2 ⟨109, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_109_47_5.D2 (m := 25)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_109_47_5.D1 (m := 25)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_109_47_10_match :
    ((Q2.charsAt2 ⟨109, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_109_47_10.D2 (m := 25)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_109_47_10.D1 (m := 25)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_109_47_15_match :
    ((Q2.charsAt2 ⟨109, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_109_47_15.D2 (m := 25)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_109_47_15.D1 (m := 25)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_109_47_20_match :
    ((Q2.charsAt2 ⟨109, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_109_47_20.D2 (m := 25)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_109_47_20.D1 (m := 25)) (e.map ZMod.val))))).all id = true := by decide

end LeanDring.P5Presentation
