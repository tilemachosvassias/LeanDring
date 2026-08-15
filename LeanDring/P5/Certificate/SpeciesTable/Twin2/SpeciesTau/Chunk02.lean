/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntrySupport
import LeanDring.P5.Certificate.Characters.Twin1.CharAssembly
import LeanDring.P5.Certificate.Characters.Twin2.CharAssembly
import LeanDring.P5.Data.ColTau.C001
import LeanDring.P5.Data.ColTau.C004

/-!
# Species-table cells, stage 2 endgame — the τ-family (γ-moved) column certificates.
Auto-emitted by python/p5_tau_emit.py. Chunk 1: 32 columns.
The 28 γ-moved columns of the twin species table, over every on-support
row class (108 `ColCertDiv` objects, `P5ColDataTau*`).  Each theorem: for
every character vector of the row class, the q1 column data and the q2
column data of the RESOLVED column pairing have equal cyclotomic value
(same-`e`, hence σ-robust).  Fed to `species_eq_of_fastcode_eq` at stage-5.

Resolved pairing.  GAP's γ column
permutation is NOT the pairing Lean needs — GAP forced `rhoA = id` on rows
and compensated on columns; Lean aligns rows per class instead.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem colCertDiv_85_85_110_tau_match :
    ((Q2.charsAt2 ⟨85, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_85_85_110.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_85_85_110.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_85_85_115_tau_match :
    ((Q2.charsAt2 ⟨85, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_85_85_115.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_85_85_115.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_85_85_120_tau_match :
    ((Q2.charsAt2 ⟨85, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_85_85_120.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_85_85_120.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_86_86_0_tau_match :
    ((Q2.charsAt2 ⟨86, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_86_86_0.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_86_86_0.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_86_86_1_tau_match :
    ((Q2.charsAt2 ⟨86, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_86_86_1.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_86_86_1.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_86_86_2_tau_match :
    ((Q2.charsAt2 ⟨86, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_86_86_2.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_86_86_2.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_86_86_3_tau_match :
    ((Q2.charsAt2 ⟨86, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_86_86_3.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_86_86_3.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_86_86_4_tau_match :
    ((Q2.charsAt2 ⟨86, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_86_86_4.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_86_86_4.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_116_13_5_tau_match :
    ((Q2.charsAt2 ⟨116, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_116_13_5.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_116_13_5.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_116_13_6_tau_match :
    ((Q2.charsAt2 ⟨116, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_116_13_6.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_116_13_6.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_116_13_7_tau_match :
    ((Q2.charsAt2 ⟨116, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_116_13_7.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_116_13_7.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_116_13_8_tau_match :
    ((Q2.charsAt2 ⟨116, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_116_13_8.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_116_13_8.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_117_13_5_tau_match :
    ((Q2.charsAt2 ⟨117, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_13_5.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_13_5.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_117_13_6_tau_match :
    ((Q2.charsAt2 ⟨117, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_13_6.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_13_6.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_117_13_7_tau_match :
    ((Q2.charsAt2 ⟨117, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_13_7.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_13_7.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_117_13_8_tau_match :
    ((Q2.charsAt2 ⟨117, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_13_8.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_117_13_8.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_13_5_tau_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_13_5.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_13_5.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_13_6_tau_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_13_6.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_13_6.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_13_7_tau_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_13_7.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_13_7.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_13_8_tau_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_13_8.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_13_8.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_68_19_tau_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_19.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_19.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_68_20_tau_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_20.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_20.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_68_21_tau_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_21.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_21.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_68_22_tau_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_22.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_68_22.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_13_5_tau_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_13_5.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_13_5.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_13_6_tau_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_13_6.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_13_6.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_13_7_tau_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_13_7.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_13_7.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_119_13_8_tau_match :
    ((Q2.charsAt2 ⟨119, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_13_8.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_119_13_8.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_120_13_5_tau_match :
    ((Q2.charsAt2 ⟨120, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_120_13_5.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_120_13_5.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_120_13_6_tau_match :
    ((Q2.charsAt2 ⟨120, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_120_13_6.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_120_13_6.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_120_13_7_tau_match :
    ((Q2.charsAt2 ⟨120, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_120_13_7.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_120_13_7.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_120_13_8_tau_match :
    ((Q2.charsAt2 ⟨120, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_120_13_8.D1 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_120_13_8.D2 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

end LeanDring.P5Presentation
