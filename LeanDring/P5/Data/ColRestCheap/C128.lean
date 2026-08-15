/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C044

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 127: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_147_116_40 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,1,3,0,0)
  h2 := (0,1,3,0,0)
  D := [[0, 1, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_45 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,1,4,0,0)
  h2 := (0,1,4,0,0)
  D := [[0, 1, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_50 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,2,0,0,0)
  h2 := (0,2,0,0,0)
  D := [[0, 2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_55 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,2,1,0,0)
  h2 := (0,2,1,0,0)
  D := [[0, 2, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_60 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,2,2,0,0)
  h2 := (0,2,2,0,0)
  D := [[0, 2, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_65 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,2,3,0,0)
  h2 := (0,2,3,0,0)
  D := [[0, 2, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_70 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,2,4,0,0)
  h2 := (0,2,4,0,0)
  D := [[0, 2, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_75 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,3,0,0,0)
  h2 := (0,3,0,0,0)
  D := [[0, 3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_80 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,3,1,0,0)
  h2 := (0,3,1,0,0)
  D := [[0, 3, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_85 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,3,2,0,0)
  h2 := (0,3,2,0,0)
  D := [[0, 3, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_90 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,3,3,0,0)
  h2 := (0,3,3,0,0)
  D := [[0, 3, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_95 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,3,4,0,0)
  h2 := (0,3,4,0,0)
  D := [[0, 3, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_100 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,4,0,0,0)
  h2 := (0,4,0,0,0)
  D := [[0, 4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_105 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,4,1,0,0)
  h2 := (0,4,1,0,0)
  D := [[0, 4, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_110 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,4,2,0,0)
  h2 := (0,4,2,0,0)
  D := [[0, 4, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_115 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,4,3,0,0)
  h2 := (0,4,3,0,0)
  D := [[0, 4, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_120 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,4,4,0,0)
  h2 := (0,4,4,0,0)
  D := [[0, 4, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 0, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 0, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 0, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 0, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_11 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 0, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_12 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 0, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_13 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 0, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_14 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 0, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_16 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 0, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_17 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 0, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_18 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 0, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_19 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 0, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_21 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 0, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_22 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (0,0,4,2,0)
  h2 := (0,0,4,2,0)
  D := [[0, 0, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 0, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 0, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_25 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (1,4,0,4,0)
  h2 := (1,4,0,4,0)
  D := [[1, 4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_30 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (1,4,1,4,0)
  h2 := (1,4,1,4,0)
  D := [[1, 4, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_35 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (1,4,2,4,0)
  h2 := (1,4,2,4,0)
  D := [[1, 4, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_40 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (1,4,3,4,0)
  h2 := (1,4,3,4,0)
  D := [[1, 4, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_117_45 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (1,4,4,4,0)
  h2 := (1,4,4,4,0)
  D := [[1, 4, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 0, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 0, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 0, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 0, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_11 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 0, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_12 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 0, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
