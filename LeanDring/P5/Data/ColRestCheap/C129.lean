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
rest tier, chunk 128: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_147_118_13 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 0, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_14 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 0, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_16 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 0, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_17 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 0, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_18 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 0, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_19 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 0, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_21 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 0, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_22 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (0,0,4,2,0)
  h2 := (0,0,4,2,0)
  D := [[0, 0, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 0, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 0, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_25 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (1,2,0,3,3)
  h2 := (1,2,0,3,3)
  D := [[1, 2, 0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_30 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (1,2,1,3,3)
  h2 := (1,2,1,3,3)
  D := [[1, 2, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_35 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (1,2,2,3,3)
  h2 := (1,2,2,3,3)
  D := [[1, 2, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_40 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (1,2,3,3,3)
  h2 := (1,2,3,3,3)
  D := [[1, 2, 3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_45 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (1,2,4,3,3)
  h2 := (1,2,4,3,3)
  D := [[1, 2, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_50 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (2,4,0,3,4)
  h2 := (2,4,0,3,4)
  D := [[2, 4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_55 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (2,4,1,3,4)
  h2 := (2,4,1,3,4)
  D := [[2, 4, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_60 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (2,4,2,3,4)
  h2 := (2,4,2,3,4)
  D := [[2, 4, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_65 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (2,4,3,3,4)
  h2 := (2,4,3,3,4)
  D := [[2, 4, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_118_70 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨118, by decide⟩
  m := 1
  T1 := T147_118
  T2 := Q2.T147_118_2
  h1 := (2,4,4,3,4)
  h2 := (2,4,4,3,4)
  D := [[2, 4, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 0, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 0, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 0, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 0, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_11 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 0, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_12 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 0, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_13 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 0, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_14 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 0, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_16 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 0, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_17 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 0, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_18 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 0, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_19 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 0, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_21 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 0, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_22 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (0,0,4,2,0)
  h2 := (0,0,4,2,0)
  D := [[0, 0, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 0, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 0, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_25 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (1,3,0,1,2)
  h2 := (1,3,0,1,2)
  D := [[1, 3, 0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_30 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (1,3,1,1,2)
  h2 := (1,3,1,1,2)
  D := [[1, 3, 1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_35 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (1,3,2,1,2)
  h2 := (1,3,2,1,2)
  D := [[1, 3, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_40 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (1,3,3,1,2)
  h2 := (1,3,3,1,2)
  D := [[1, 3, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_119_45 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨119, by decide⟩
  m := 1
  T1 := T147_119
  T2 := Q2.T147_119_2
  h1 := (1,3,4,1,2)
  h2 := (1,3,4,1,2)
  D := [[1, 3, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_120_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨120, by decide⟩
  m := 1
  T1 := T147_120
  T2 := Q2.T147_120_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_120_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨120, by decide⟩
  m := 1
  T1 := T147_120
  T2 := Q2.T147_120_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_120_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨120, by decide⟩
  m := 1
  T1 := T147_120
  T2 := Q2.T147_120_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_120_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨120, by decide⟩
  m := 1
  T1 := T147_120
  T2 := Q2.T147_120_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_120_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨120, by decide⟩
  m := 1
  T1 := T147_120
  T2 := Q2.T147_120_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_120_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨120, by decide⟩
  m := 1
  T1 := T147_120
  T2 := Q2.T147_120_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_120_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨120, by decide⟩
  m := 1
  T1 := T147_120
  T2 := Q2.T147_120_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 0, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_120_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨120, by decide⟩
  m := 1
  T1 := T147_120
  T2 := Q2.T147_120_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 0, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
