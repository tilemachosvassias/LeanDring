/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C029

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 43: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_120_76_9 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (0,0,1,4,4)
  h2 := (0,0,1,4,4)
  D := [[0, 1, 4, 0], [0, 1, 4, 1], [0, 1, 4, 2], [0, 1, 4, 3], [0, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_76_10 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 2, 3, 2], [0, 2, 3, 4], [0, 2, 3, 1], [0, 2, 3, 3], [0, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_76_11 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (0,0,2,3,1)
  h2 := (0,0,2,3,1)
  D := [[0, 2, 3, 3], [0, 2, 3, 0], [0, 2, 3, 2], [0, 2, 3, 4], [0, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_76_12 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (0,0,2,3,2)
  h2 := (0,0,2,3,2)
  D := [[0, 2, 3, 4], [0, 2, 3, 1], [0, 2, 3, 3], [0, 2, 3, 0], [0, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_76_13 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (0,0,2,3,3)
  h2 := (0,0,2,3,3)
  D := [[0, 2, 3, 0], [0, 2, 3, 2], [0, 2, 3, 4], [0, 2, 3, 1], [0, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_76_14 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (0,0,2,3,4)
  h2 := (0,0,2,3,4)
  D := [[0, 2, 3, 1], [0, 2, 3, 3], [0, 2, 3, 0], [0, 2, 3, 2], [0, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_76_15 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 3, 2, 3], [0, 3, 2, 1], [0, 3, 2, 4], [0, 3, 2, 2], [0, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_76_16 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (0,0,3,2,1)
  h2 := (0,0,3,2,1)
  D := [[0, 3, 2, 4], [0, 3, 2, 2], [0, 3, 2, 0], [0, 3, 2, 3], [0, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_76_17 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (0,0,3,2,2)
  h2 := (0,0,3,2,2)
  D := [[0, 3, 2, 0], [0, 3, 2, 3], [0, 3, 2, 1], [0, 3, 2, 4], [0, 3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_76_18 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (0,0,3,2,3)
  h2 := (0,0,3,2,3)
  D := [[0, 3, 2, 1], [0, 3, 2, 4], [0, 3, 2, 2], [0, 3, 2, 0], [0, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_76_19 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (0,0,3,2,4)
  h2 := (0,0,3,2,4)
  D := [[0, 3, 2, 2], [0, 3, 2, 0], [0, 3, 2, 3], [0, 3, 2, 1], [0, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_76_20 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 4, 1, 4], [0, 4, 1, 3], [0, 4, 1, 2], [0, 4, 1, 1], [0, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_76_21 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (0,0,4,1,1)
  h2 := (0,0,4,1,1)
  D := [[0, 4, 1, 0], [0, 4, 1, 4], [0, 4, 1, 3], [0, 4, 1, 2], [0, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_76_22 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (0,0,4,1,2)
  h2 := (0,0,4,1,2)
  D := [[0, 4, 1, 1], [0, 4, 1, 0], [0, 4, 1, 4], [0, 4, 1, 3], [0, 4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_76_23 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (0,0,4,1,3)
  h2 := (0,0,4,1,3)
  D := [[0, 4, 1, 2], [0, 4, 1, 1], [0, 4, 1, 0], [0, 4, 1, 4], [0, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_76_24 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (0,0,4,1,4)
  h2 := (0,0,4,1,4)
  D := [[0, 4, 1, 3], [0, 4, 1, 2], [0, 4, 1, 1], [0, 4, 1, 0], [0, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_77_0 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨77, by decide⟩
  m := 5
  T1 := T120_77
  T2 := Q2.T120_77_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_77_1 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨77, by decide⟩
  m := 5
  T1 := T120_77
  T2 := Q2.T120_77_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 1, 3, 1], [0, 1, 3, 2], [0, 1, 3, 3], [0, 1, 3, 4], [0, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_77_2 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨77, by decide⟩
  m := 5
  T1 := T120_77
  T2 := Q2.T120_77_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 2, 1, 2], [0, 2, 1, 4], [0, 2, 1, 1], [0, 2, 1, 3], [0, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_77_3 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨77, by decide⟩
  m := 5
  T1 := T120_77
  T2 := Q2.T120_77_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 3, 4, 3], [0, 3, 4, 1], [0, 3, 4, 4], [0, 3, 4, 2], [0, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_77_4 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨77, by decide⟩
  m := 5
  T1 := T120_77
  T2 := Q2.T120_77_2
  h1 := (0,0,4,2,0)
  h2 := (0,0,4,2,0)
  D := [[0, 4, 2, 4], [0, 4, 2, 3], [0, 4, 2, 2], [0, 4, 2, 1], [0, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_78_0 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T120_78
  T2 := Q2.T120_78_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_78_1 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T120_78
  T2 := Q2.T120_78_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 1, 2, 1], [0, 1, 2, 2], [0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_78_2 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T120_78
  T2 := Q2.T120_78_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 2, 4, 2], [0, 2, 4, 4], [0, 2, 4, 1], [0, 2, 4, 3], [0, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_78_3 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T120_78
  T2 := Q2.T120_78_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 3, 1, 3], [0, 3, 1, 1], [0, 3, 1, 4], [0, 3, 1, 2], [0, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_78_4 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T120_78
  T2 := Q2.T120_78_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 4, 3, 4], [0, 4, 3, 3], [0, 4, 3, 2], [0, 4, 3, 1], [0, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_79_0 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T120_79
  T2 := Q2.T120_79_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_79_1 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T120_79
  T2 := Q2.T120_79_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 1, 1, 1], [0, 1, 1, 2], [0, 1, 1, 3], [0, 1, 1, 4], [0, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_79_2 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T120_79
  T2 := Q2.T120_79_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 2, 2, 2], [0, 2, 2, 4], [0, 2, 2, 1], [0, 2, 2, 3], [0, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_79_3 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T120_79
  T2 := Q2.T120_79_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 3, 3, 3], [0, 3, 3, 1], [0, 3, 3, 4], [0, 3, 3, 2], [0, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_79_4 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T120_79
  T2 := Q2.T120_79_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 4, 4, 4], [0, 4, 4, 3], [0, 4, 4, 2], [0, 4, 4, 1], [0, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_79_5 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T120_79
  T2 := Q2.T120_79_2
  h1 := (1,1,0,4,0)
  h2 := (1,1,0,4,0)
  D := [[1, 0, 3, 2], [1, 0, 2, 3], [1, 0, 1, 4], [1, 0, 0, 0], [1, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_79_6 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T120_79
  T2 := Q2.T120_79_2
  h1 := (1,1,1,0,0)
  h2 := (1,1,1,0,0)
  D := [[1, 1, 4, 1], [1, 1, 3, 3], [1, 1, 2, 0], [1, 1, 1, 2], [1, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_79_7 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T120_79
  T2 := Q2.T120_79_2
  h1 := (1,1,2,1,0)
  h2 := (1,1,2,1,0)
  D := [[1, 2, 0, 0], [1, 2, 4, 3], [1, 2, 3, 1], [1, 2, 2, 4], [1, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_79_8 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T120_79
  T2 := Q2.T120_79_2
  h1 := (1,1,3,2,0)
  h2 := (1,1,3,2,0)
  D := [[1, 3, 1, 4], [1, 3, 0, 3], [1, 3, 4, 2], [1, 3, 3, 1], [1, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_79_9 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T120_79
  T2 := Q2.T120_79_2
  h1 := (1,1,4,3,0)
  h2 := (1,1,4,3,0)
  D := [[1, 4, 2, 3], [1, 4, 1, 3], [1, 4, 0, 3], [1, 4, 4, 3], [1, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_79_10 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T120_79
  T2 := Q2.T120_79_2
  h1 := (2,2,0,4,4)
  h2 := (2,2,0,4,4)
  D := [[2, 0, 1, 1], [2, 0, 4, 4], [2, 0, 2, 2], [2, 0, 0, 0], [2, 0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_79_11 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T120_79
  T2 := Q2.T120_79_2
  h1 := (2,2,1,0,4)
  h2 := (2,2,1,0,4)
  D := [[2, 1, 2, 3], [2, 1, 0, 2], [2, 1, 3, 1], [2, 1, 1, 0], [2, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_79_12 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T120_79
  T2 := Q2.T120_79_2
  h1 := (2,2,2,1,4)
  h2 := (2,2,2,1,4)
  D := [[2, 2, 3, 0], [2, 2, 1, 0], [2, 2, 4, 0], [2, 2, 2, 0], [2, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_79_13 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T120_79
  T2 := Q2.T120_79_2
  h1 := (2,2,3,2,4)
  h2 := (2,2,3,2,4)
  D := [[2, 3, 4, 2], [2, 3, 2, 3], [2, 3, 0, 4], [2, 3, 3, 0], [2, 3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_79_14 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T120_79
  T2 := Q2.T120_79_2
  h1 := (2,2,4,3,4)
  h2 := (2,2,4,3,4)
  D := [[2, 4, 0, 4], [2, 4, 3, 1], [2, 4, 1, 3], [2, 4, 4, 0], [2, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_79_15 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T120_79
  T2 := Q2.T120_79_2
  h1 := (3,3,0,0,3)
  h2 := (3,3,0,0,3)
  D := [[3, 0, 4, 2], [3, 0, 1, 3], [3, 0, 3, 4], [3, 0, 0, 0], [3, 0, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_79_16 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T120_79
  T2 := Q2.T120_79_2
  h1 := (3,3,1,1,3)
  h2 := (3,3,1,1,3)
  D := [[3, 1, 0, 2], [3, 1, 2, 4], [3, 1, 4, 1], [3, 1, 1, 3], [3, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_79_17 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T120_79
  T2 := Q2.T120_79_2
  h1 := (3,3,2,2,3)
  h2 := (3,3,2,2,3)
  D := [[3, 2, 1, 2], [3, 2, 3, 0], [3, 2, 0, 3], [3, 2, 2, 1], [3, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_79_18 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T120_79
  T2 := Q2.T120_79_2
  h1 := (3,3,3,3,3)
  h2 := (3,3,3,3,3)
  D := [[3, 3, 2, 2], [3, 3, 4, 1], [3, 3, 1, 0], [3, 3, 3, 4], [3, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_79_19 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T120_79
  T2 := Q2.T120_79_2
  h1 := (3,3,4,4,3)
  h2 := (3,3,4,4,3)
  D := [[3, 4, 3, 2], [3, 4, 0, 2], [3, 4, 2, 2], [3, 4, 4, 2], [3, 4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_79_20 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T120_79
  T2 := Q2.T120_79_2
  h1 := (4,4,0,2,3)
  h2 := (4,4,0,2,3)
  D := [[4, 0, 2, 0], [4, 0, 3, 0], [4, 0, 4, 0], [4, 0, 0, 0], [4, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_79_21 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T120_79
  T2 := Q2.T120_79_2
  h1 := (4,4,1,3,3)
  h2 := (4,4,1,3,3)
  D := [[4, 1, 3, 3], [4, 1, 4, 4], [4, 1, 0, 0], [4, 1, 1, 1], [4, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_79_22 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T120_79
  T2 := Q2.T120_79_2
  h1 := (4,4,2,4,3)
  h2 := (4,4,2,4,3)
  D := [[4, 2, 4, 1], [4, 2, 0, 3], [4, 2, 1, 0], [4, 2, 2, 2], [4, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_79_23 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T120_79
  T2 := Q2.T120_79_2
  h1 := (4,4,3,0,3)
  h2 := (4,4,3,0,3)
  D := [[4, 3, 0, 4], [4, 3, 1, 2], [4, 3, 2, 0], [4, 3, 3, 3], [4, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_79_24 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T120_79
  T2 := Q2.T120_79_2
  h1 := (4,4,4,1,3)
  h2 := (4,4,4,1,3)
  D := [[4, 4, 1, 2], [4, 4, 2, 1], [4, 4, 3, 0], [4, 4, 4, 4], [4, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_80_0 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_80_1 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_80_2 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_80_3 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_80_4 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_80_5 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_80_10 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_80_15 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_80_20 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
