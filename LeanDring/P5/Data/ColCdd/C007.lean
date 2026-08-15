/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C029

/-!
# Species-table cell data, stage 2 — column-data-divergent columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
cdd tier, chunk 6: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_120_76_25 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (1,1,0,4,1)
  h2 := (1,1,0,4,4)
  D1 := [[1, 0, 3, 3], [1, 0, 2, 4], [1, 0, 1, 0], [1, 0, 0, 1], [1, 0, 4, 2]]
  D2 := [[1, 0, 3, 1], [1, 0, 2, 2], [1, 0, 1, 3], [1, 0, 0, 4], [1, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_76_30 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (1,1,1,3,1)
  h2 := (1,1,1,3,4)
  D1 := [[1, 1, 2, 4], [1, 1, 1, 1], [1, 1, 0, 3], [1, 1, 4, 0], [1, 1, 3, 2]]
  D2 := [[1, 1, 2, 2], [1, 1, 1, 4], [1, 1, 0, 1], [1, 1, 4, 3], [1, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_76_35 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (1,1,2,2,1)
  h2 := (1,1,2,2,4)
  D1 := [[1, 2, 1, 0], [1, 2, 0, 3], [1, 2, 4, 1], [1, 2, 3, 4], [1, 2, 2, 2]]
  D2 := [[1, 2, 1, 3], [1, 2, 0, 1], [1, 2, 4, 4], [1, 2, 3, 2], [1, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_76_40 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (1,1,3,1,1)
  h2 := (1,1,3,1,4)
  D1 := [[1, 3, 0, 1], [1, 3, 4, 0], [1, 3, 3, 4], [1, 3, 2, 3], [1, 3, 1, 2]]
  D2 := [[1, 3, 0, 4], [1, 3, 4, 3], [1, 3, 3, 2], [1, 3, 2, 1], [1, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_76_45 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (1,1,4,0,1)
  h2 := (1,1,4,0,4)
  D1 := [[1, 4, 4, 2], [1, 4, 3, 2], [1, 4, 2, 2], [1, 4, 1, 2], [1, 4, 0, 2]]
  D2 := [[1, 4, 4, 0], [1, 4, 3, 0], [1, 4, 2, 0], [1, 4, 1, 0], [1, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_76_50 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (2,2,0,4,1)
  h2 := (2,2,0,4,2)
  D1 := [[2, 0, 1, 3], [2, 0, 4, 1], [2, 0, 2, 4], [2, 0, 0, 2], [2, 0, 3, 0]]
  D2 := [[2, 0, 1, 4], [2, 0, 4, 2], [2, 0, 2, 0], [2, 0, 0, 3], [2, 0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_76_55 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (2,2,1,3,1)
  h2 := (2,2,1,3,2)
  D1 := [[2, 1, 0, 4], [2, 1, 3, 3], [2, 1, 1, 2], [2, 1, 4, 1], [2, 1, 2, 0]]
  D2 := [[2, 1, 0, 0], [2, 1, 3, 4], [2, 1, 1, 3], [2, 1, 4, 2], [2, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_76_60 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (2,2,2,2,1)
  h2 := (2,2,2,2,2)
  D1 := [[2, 2, 4, 0], [2, 2, 2, 0], [2, 2, 0, 0], [2, 2, 3, 0], [2, 2, 1, 0]]
  D2 := [[2, 2, 4, 1], [2, 2, 2, 1], [2, 2, 0, 1], [2, 2, 3, 1], [2, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_76_65 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (2,2,3,1,1)
  h2 := (2,2,3,1,2)
  D1 := [[2, 3, 3, 1], [2, 3, 1, 2], [2, 3, 4, 3], [2, 3, 2, 4], [2, 3, 0, 0]]
  D2 := [[2, 3, 3, 2], [2, 3, 1, 3], [2, 3, 4, 4], [2, 3, 2, 0], [2, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_76_70 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (2,2,4,0,1)
  h2 := (2,2,4,0,2)
  D1 := [[2, 4, 2, 2], [2, 4, 0, 4], [2, 4, 3, 1], [2, 4, 1, 3], [2, 4, 4, 0]]
  D2 := [[2, 4, 2, 3], [2, 4, 0, 0], [2, 4, 3, 2], [2, 4, 1, 4], [2, 4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_76_75 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (3,3,0,0,1)
  h2 := (3,3,0,0,0)
  D1 := [[3, 0, 4, 0], [3, 0, 1, 1], [3, 0, 3, 2], [3, 0, 0, 3], [3, 0, 2, 4]]
  D2 := [[3, 0, 4, 4], [3, 0, 1, 0], [3, 0, 3, 1], [3, 0, 0, 2], [3, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_76_80 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (3,3,1,4,1)
  h2 := (3,3,1,4,0)
  D1 := [[3, 1, 3, 1], [3, 1, 0, 3], [3, 1, 2, 0], [3, 1, 4, 2], [3, 1, 1, 4]]
  D2 := [[3, 1, 3, 0], [3, 1, 0, 2], [3, 1, 2, 4], [3, 1, 4, 1], [3, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_76_85 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (3,3,2,3,1)
  h2 := (3,3,2,3,0)
  D1 := [[3, 2, 2, 2], [3, 2, 4, 0], [3, 2, 1, 3], [3, 2, 3, 1], [3, 2, 0, 4]]
  D2 := [[3, 2, 2, 1], [3, 2, 4, 4], [3, 2, 1, 2], [3, 2, 3, 0], [3, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_76_90 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (3,3,3,2,1)
  h2 := (3,3,3,2,0)
  D1 := [[3, 3, 1, 3], [3, 3, 3, 2], [3, 3, 0, 1], [3, 3, 2, 0], [3, 3, 4, 4]]
  D2 := [[3, 3, 1, 2], [3, 3, 3, 1], [3, 3, 0, 0], [3, 3, 2, 4], [3, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_76_95 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (3,3,4,1,1)
  h2 := (3,3,4,1,0)
  D1 := [[3, 4, 0, 4], [3, 4, 2, 4], [3, 4, 4, 4], [3, 4, 1, 4], [3, 4, 3, 4]]
  D2 := [[3, 4, 0, 3], [3, 4, 2, 3], [3, 4, 4, 3], [3, 4, 1, 3], [3, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_76_100 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (4,4,0,2,2)
  h2 := (4,4,0,2,4)
  D1 := [[4, 0, 2, 4], [4, 0, 3, 4], [4, 0, 4, 4], [4, 0, 0, 4], [4, 0, 1, 4]]
  D2 := [[4, 0, 2, 1], [4, 0, 3, 1], [4, 0, 4, 1], [4, 0, 0, 1], [4, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_76_105 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (4,4,1,1,2)
  h2 := (4,4,1,1,4)
  D1 := [[4, 1, 1, 0], [4, 1, 2, 1], [4, 1, 3, 2], [4, 1, 4, 3], [4, 1, 0, 4]]
  D2 := [[4, 1, 1, 2], [4, 1, 2, 3], [4, 1, 3, 4], [4, 1, 4, 0], [4, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_76_110 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (4,4,2,0,2)
  h2 := (4,4,2,0,4)
  D1 := [[4, 2, 0, 1], [4, 2, 1, 3], [4, 2, 2, 0], [4, 2, 3, 2], [4, 2, 4, 4]]
  D2 := [[4, 2, 0, 3], [4, 2, 1, 0], [4, 2, 2, 2], [4, 2, 3, 4], [4, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_76_115 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (4,4,3,4,2)
  h2 := (4,4,3,4,4)
  D1 := [[4, 3, 4, 2], [4, 3, 0, 0], [4, 3, 1, 3], [4, 3, 2, 1], [4, 3, 3, 4]]
  D2 := [[4, 3, 4, 4], [4, 3, 0, 2], [4, 3, 1, 0], [4, 3, 2, 3], [4, 3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_76_120 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (4,4,4,3,2)
  h2 := (4,4,4,3,4)
  D1 := [[4, 4, 3, 3], [4, 4, 4, 2], [4, 4, 0, 1], [4, 4, 1, 0], [4, 4, 2, 4]]
  D2 := [[4, 4, 3, 0], [4, 4, 4, 4], [4, 4, 0, 3], [4, 4, 1, 2], [4, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_77_5 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨77, by decide⟩
  m := 5
  T1 := T120_77
  T2 := Q2.T120_77_2
  h1 := (1,1,0,4,2)
  h2 := (1,1,0,4,3)
  D1 := [[1, 0, 3, 4], [1, 0, 2, 0], [1, 0, 1, 1], [1, 0, 0, 2], [1, 0, 4, 3]]
  D2 := [[1, 0, 3, 0], [1, 0, 2, 1], [1, 0, 1, 2], [1, 0, 0, 3], [1, 0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_77_6 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨77, by decide⟩
  m := 5
  T1 := T120_77
  T2 := Q2.T120_77_2
  h1 := (1,1,1,2,2)
  h2 := (1,1,1,2,3)
  D1 := [[1, 1, 1, 1], [1, 1, 0, 3], [1, 1, 4, 0], [1, 1, 3, 2], [1, 1, 2, 4]]
  D2 := [[1, 1, 1, 2], [1, 1, 0, 4], [1, 1, 4, 1], [1, 1, 3, 3], [1, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_77_7 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨77, by decide⟩
  m := 5
  T1 := T120_77
  T2 := Q2.T120_77_2
  h1 := (1,1,2,0,2)
  h2 := (1,1,2,0,3)
  D1 := [[1, 2, 4, 3], [1, 2, 3, 1], [1, 2, 2, 4], [1, 2, 1, 2], [1, 2, 0, 0]]
  D2 := [[1, 2, 4, 4], [1, 2, 3, 2], [1, 2, 2, 0], [1, 2, 1, 3], [1, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_77_8 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨77, by decide⟩
  m := 5
  T1 := T120_77
  T2 := Q2.T120_77_2
  h1 := (1,1,3,3,2)
  h2 := (1,1,3,3,3)
  D1 := [[1, 3, 2, 0], [1, 3, 1, 4], [1, 3, 0, 3], [1, 3, 4, 2], [1, 3, 3, 1]]
  D2 := [[1, 3, 2, 1], [1, 3, 1, 0], [1, 3, 0, 4], [1, 3, 4, 3], [1, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_77_9 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨77, by decide⟩
  m := 5
  T1 := T120_77
  T2 := Q2.T120_77_2
  h1 := (1,1,4,1,2)
  h2 := (1,1,4,1,3)
  D1 := [[1, 4, 0, 2], [1, 4, 4, 2], [1, 4, 3, 2], [1, 4, 2, 2], [1, 4, 1, 2]]
  D2 := [[1, 4, 0, 3], [1, 4, 4, 3], [1, 4, 3, 3], [1, 4, 2, 3], [1, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_77_10 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨77, by decide⟩
  m := 5
  T1 := T120_77
  T2 := Q2.T120_77_2
  h1 := (2,2,0,4,3)
  h2 := (2,2,0,4,0)
  D1 := [[2, 0, 1, 0], [2, 0, 4, 3], [2, 0, 2, 1], [2, 0, 0, 4], [2, 0, 3, 2]]
  D2 := [[2, 0, 1, 2], [2, 0, 4, 0], [2, 0, 2, 3], [2, 0, 0, 1], [2, 0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_77_11 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨77, by decide⟩
  m := 5
  T1 := T120_77
  T2 := Q2.T120_77_2
  h1 := (2,2,1,2,3)
  h2 := (2,2,1,2,0)
  D1 := [[2, 1, 4, 3], [2, 1, 2, 2], [2, 1, 0, 1], [2, 1, 3, 0], [2, 1, 1, 4]]
  D2 := [[2, 1, 4, 0], [2, 1, 2, 4], [2, 1, 0, 3], [2, 1, 3, 2], [2, 1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_77_12 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨77, by decide⟩
  m := 5
  T1 := T120_77
  T2 := Q2.T120_77_2
  h1 := (2,2,2,0,3)
  h2 := (2,2,2,0,0)
  D1 := [[2, 2, 2, 1], [2, 2, 0, 1], [2, 2, 3, 1], [2, 2, 1, 1], [2, 2, 4, 1]]
  D2 := [[2, 2, 2, 3], [2, 2, 0, 3], [2, 2, 3, 3], [2, 2, 1, 3], [2, 2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_77_13 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨77, by decide⟩
  m := 5
  T1 := T120_77
  T2 := Q2.T120_77_2
  h1 := (2,2,3,3,3)
  h2 := (2,2,3,3,0)
  D1 := [[2, 3, 0, 4], [2, 3, 3, 0], [2, 3, 1, 1], [2, 3, 4, 2], [2, 3, 2, 3]]
  D2 := [[2, 3, 0, 1], [2, 3, 3, 2], [2, 3, 1, 3], [2, 3, 4, 4], [2, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_77_14 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨77, by decide⟩
  m := 5
  T1 := T120_77
  T2 := Q2.T120_77_2
  h1 := (2,2,4,1,3)
  h2 := (2,2,4,1,0)
  D1 := [[2, 4, 3, 2], [2, 4, 1, 4], [2, 4, 4, 1], [2, 4, 2, 3], [2, 4, 0, 0]]
  D2 := [[2, 4, 3, 4], [2, 4, 1, 1], [2, 4, 4, 3], [2, 4, 2, 0], [2, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_77_15 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨77, by decide⟩
  m := 5
  T1 := T120_77
  T2 := Q2.T120_77_2
  h1 := (3,3,0,0,4)
  h2 := (3,3,0,0,2)
  D1 := [[3, 0, 4, 3], [3, 0, 1, 4], [3, 0, 3, 0], [3, 0, 0, 1], [3, 0, 2, 2]]
  D2 := [[3, 0, 4, 1], [3, 0, 1, 2], [3, 0, 3, 3], [3, 0, 0, 4], [3, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_77_16 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨77, by decide⟩
  m := 5
  T1 := T120_77
  T2 := Q2.T120_77_2
  h1 := (3,3,1,3,4)
  h2 := (3,3,1,3,2)
  D1 := [[3, 1, 2, 2], [3, 1, 4, 4], [3, 1, 1, 1], [3, 1, 3, 3], [3, 1, 0, 0]]
  D2 := [[3, 1, 2, 0], [3, 1, 4, 2], [3, 1, 1, 4], [3, 1, 3, 1], [3, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_77_17 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨77, by decide⟩
  m := 5
  T1 := T120_77
  T2 := Q2.T120_77_2
  h1 := (3,3,2,1,4)
  h2 := (3,3,2,1,2)
  D1 := [[3, 2, 0, 1], [3, 2, 2, 4], [3, 2, 4, 2], [3, 2, 1, 0], [3, 2, 3, 3]]
  D2 := [[3, 2, 0, 4], [3, 2, 2, 2], [3, 2, 4, 0], [3, 2, 1, 3], [3, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_77_18 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨77, by decide⟩
  m := 5
  T1 := T120_77
  T2 := Q2.T120_77_2
  h1 := (3,3,3,4,4)
  h2 := (3,3,3,4,2)
  D1 := [[3, 3, 3, 0], [3, 3, 0, 4], [3, 3, 2, 3], [3, 3, 4, 2], [3, 3, 1, 1]]
  D2 := [[3, 3, 3, 3], [3, 3, 0, 2], [3, 3, 2, 1], [3, 3, 4, 0], [3, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_77_19 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨77, by decide⟩
  m := 5
  T1 := T120_77
  T2 := Q2.T120_77_2
  h1 := (3,3,4,2,4)
  h2 := (3,3,4,2,2)
  D1 := [[3, 4, 1, 4], [3, 4, 3, 4], [3, 4, 0, 4], [3, 4, 2, 4], [3, 4, 4, 4]]
  D2 := [[3, 4, 1, 2], [3, 4, 3, 2], [3, 4, 0, 2], [3, 4, 2, 2], [3, 4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_77_20 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨77, by decide⟩
  m := 5
  T1 := T120_77
  T2 := Q2.T120_77_2
  h1 := (4,4,0,2,1)
  h2 := (4,4,0,2,0)
  D1 := [[4, 0, 2, 3], [4, 0, 3, 3], [4, 0, 4, 3], [4, 0, 0, 3], [4, 0, 1, 3]]
  D2 := [[4, 0, 2, 2], [4, 0, 3, 2], [4, 0, 4, 2], [4, 0, 0, 2], [4, 0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_77_21 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨77, by decide⟩
  m := 5
  T1 := T120_77
  T2 := Q2.T120_77_2
  h1 := (4,4,1,0,1)
  h2 := (4,4,1,0,0)
  D1 := [[4, 1, 0, 3], [4, 1, 1, 4], [4, 1, 2, 0], [4, 1, 3, 1], [4, 1, 4, 2]]
  D2 := [[4, 1, 0, 2], [4, 1, 1, 3], [4, 1, 2, 4], [4, 1, 3, 0], [4, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_77_22 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨77, by decide⟩
  m := 5
  T1 := T120_77
  T2 := Q2.T120_77_2
  h1 := (4,4,2,3,1)
  h2 := (4,4,2,3,0)
  D1 := [[4, 2, 3, 3], [4, 2, 4, 0], [4, 2, 0, 2], [4, 2, 1, 4], [4, 2, 2, 1]]
  D2 := [[4, 2, 3, 2], [4, 2, 4, 4], [4, 2, 0, 1], [4, 2, 1, 3], [4, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_77_23 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨77, by decide⟩
  m := 5
  T1 := T120_77
  T2 := Q2.T120_77_2
  h1 := (4,4,3,1,1)
  h2 := (4,4,3,1,0)
  D1 := [[4, 3, 1, 3], [4, 3, 2, 1], [4, 3, 3, 4], [4, 3, 4, 2], [4, 3, 0, 0]]
  D2 := [[4, 3, 1, 2], [4, 3, 2, 0], [4, 3, 3, 3], [4, 3, 4, 1], [4, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_77_24 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨77, by decide⟩
  m := 5
  T1 := T120_77
  T2 := Q2.T120_77_2
  h1 := (4,4,4,4,1)
  h2 := (4,4,4,4,0)
  D1 := [[4, 4, 4, 3], [4, 4, 0, 2], [4, 4, 1, 1], [4, 4, 2, 0], [4, 4, 3, 4]]
  D2 := [[4, 4, 4, 2], [4, 4, 0, 1], [4, 4, 1, 0], [4, 4, 2, 4], [4, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_78_5 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T120_78
  T2 := Q2.T120_78_2
  h1 := (1,1,0,4,2)
  h2 := (1,1,0,4,3)
  D1 := [[1, 0, 3, 4], [1, 0, 2, 0], [1, 0, 1, 1], [1, 0, 0, 2], [1, 0, 4, 3]]
  D2 := [[1, 0, 3, 0], [1, 0, 2, 1], [1, 0, 1, 2], [1, 0, 0, 3], [1, 0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_78_6 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T120_78
  T2 := Q2.T120_78_2
  h1 := (1,1,1,1,2)
  h2 := (1,1,1,1,3)
  D1 := [[1, 1, 0, 2], [1, 1, 4, 4], [1, 1, 3, 1], [1, 1, 2, 3], [1, 1, 1, 0]]
  D2 := [[1, 1, 0, 3], [1, 1, 4, 0], [1, 1, 3, 2], [1, 1, 2, 4], [1, 1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_78_7 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T120_78
  T2 := Q2.T120_78_2
  h1 := (1,1,2,3,2)
  h2 := (1,1,2,3,3)
  D1 := [[1, 2, 2, 0], [1, 2, 1, 3], [1, 2, 0, 1], [1, 2, 4, 4], [1, 2, 3, 2]]
  D2 := [[1, 2, 2, 1], [1, 2, 1, 4], [1, 2, 0, 2], [1, 2, 4, 0], [1, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_78_8 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T120_78
  T2 := Q2.T120_78_2
  h1 := (1,1,3,0,2)
  h2 := (1,1,3,0,3)
  D1 := [[1, 3, 4, 3], [1, 3, 3, 2], [1, 3, 2, 1], [1, 3, 1, 0], [1, 3, 0, 4]]
  D2 := [[1, 3, 4, 4], [1, 3, 3, 3], [1, 3, 2, 2], [1, 3, 1, 1], [1, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_78_9 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T120_78
  T2 := Q2.T120_78_2
  h1 := (1,1,4,2,2)
  h2 := (1,1,4,2,3)
  D1 := [[1, 4, 1, 1], [1, 4, 0, 1], [1, 4, 4, 1], [1, 4, 3, 1], [1, 4, 2, 1]]
  D2 := [[1, 4, 1, 2], [1, 4, 0, 2], [1, 4, 4, 2], [1, 4, 3, 2], [1, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_78_10 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T120_78
  T2 := Q2.T120_78_2
  h1 := (2,2,0,4,3)
  h2 := (2,2,0,4,0)
  D1 := [[2, 0, 1, 0], [2, 0, 4, 3], [2, 0, 2, 1], [2, 0, 0, 4], [2, 0, 3, 2]]
  D2 := [[2, 0, 1, 2], [2, 0, 4, 0], [2, 0, 2, 3], [2, 0, 0, 1], [2, 0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_78_11 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T120_78
  T2 := Q2.T120_78_2
  h1 := (2,2,1,1,3)
  h2 := (2,2,1,1,0)
  D1 := [[2, 1, 3, 0], [2, 1, 1, 4], [2, 1, 4, 3], [2, 1, 2, 2], [2, 1, 0, 1]]
  D2 := [[2, 1, 3, 2], [2, 1, 1, 1], [2, 1, 4, 0], [2, 1, 2, 4], [2, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_78_12 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T120_78
  T2 := Q2.T120_78_2
  h1 := (2,2,2,3,3)
  h2 := (2,2,2,3,0)
  D1 := [[2, 2, 0, 0], [2, 2, 3, 0], [2, 2, 1, 0], [2, 2, 4, 0], [2, 2, 2, 0]]
  D2 := [[2, 2, 0, 2], [2, 2, 3, 2], [2, 2, 1, 2], [2, 2, 4, 2], [2, 2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_78_13 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T120_78
  T2 := Q2.T120_78_2
  h1 := (2,2,3,0,3)
  h2 := (2,2,3,0,0)
  D1 := [[2, 3, 2, 0], [2, 3, 0, 1], [2, 3, 3, 2], [2, 3, 1, 3], [2, 3, 4, 4]]
  D2 := [[2, 3, 2, 2], [2, 3, 0, 3], [2, 3, 3, 4], [2, 3, 1, 0], [2, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_78_14 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T120_78
  T2 := Q2.T120_78_2
  h1 := (2,2,4,2,3)
  h2 := (2,2,4,2,0)
  D1 := [[2, 4, 4, 0], [2, 4, 2, 2], [2, 4, 0, 4], [2, 4, 3, 1], [2, 4, 1, 3]]
  D2 := [[2, 4, 4, 2], [2, 4, 2, 4], [2, 4, 0, 1], [2, 4, 3, 3], [2, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_78_15 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T120_78
  T2 := Q2.T120_78_2
  h1 := (3,3,0,0,4)
  h2 := (3,3,0,0,2)
  D1 := [[3, 0, 4, 3], [3, 0, 1, 4], [3, 0, 3, 0], [3, 0, 0, 1], [3, 0, 2, 2]]
  D2 := [[3, 0, 4, 1], [3, 0, 1, 2], [3, 0, 3, 3], [3, 0, 0, 4], [3, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_78_16 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T120_78
  T2 := Q2.T120_78_2
  h1 := (3,3,1,2,4)
  h2 := (3,3,1,2,2)
  D1 := [[3, 1, 1, 0], [3, 1, 3, 2], [3, 1, 0, 4], [3, 1, 2, 1], [3, 1, 4, 3]]
  D2 := [[3, 1, 1, 3], [3, 1, 3, 0], [3, 1, 0, 2], [3, 1, 2, 4], [3, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_78_17 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T120_78
  T2 := Q2.T120_78_2
  h1 := (3,3,2,4,4)
  h2 := (3,3,2,4,2)
  D1 := [[3, 2, 3, 2], [3, 2, 0, 0], [3, 2, 2, 3], [3, 2, 4, 1], [3, 2, 1, 4]]
  D2 := [[3, 2, 3, 0], [3, 2, 0, 3], [3, 2, 2, 1], [3, 2, 4, 4], [3, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_78_18 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T120_78
  T2 := Q2.T120_78_2
  h1 := (3,3,3,1,4)
  h2 := (3,3,3,1,2)
  D1 := [[3, 3, 0, 4], [3, 3, 2, 3], [3, 3, 4, 2], [3, 3, 1, 1], [3, 3, 3, 0]]
  D2 := [[3, 3, 0, 2], [3, 3, 2, 1], [3, 3, 4, 0], [3, 3, 1, 4], [3, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_78_19 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T120_78
  T2 := Q2.T120_78_2
  h1 := (3,3,4,3,4)
  h2 := (3,3,4,3,2)
  D1 := [[3, 4, 2, 1], [3, 4, 4, 1], [3, 4, 1, 1], [3, 4, 3, 1], [3, 4, 0, 1]]
  D2 := [[3, 4, 2, 4], [3, 4, 4, 4], [3, 4, 1, 4], [3, 4, 3, 4], [3, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_78_20 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T120_78
  T2 := Q2.T120_78_2
  h1 := (4,4,0,2,1)
  h2 := (4,4,0,2,0)
  D1 := [[4, 0, 2, 3], [4, 0, 3, 3], [4, 0, 4, 3], [4, 0, 0, 3], [4, 0, 1, 3]]
  D2 := [[4, 0, 2, 2], [4, 0, 3, 2], [4, 0, 4, 2], [4, 0, 0, 2], [4, 0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_78_21 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T120_78
  T2 := Q2.T120_78_2
  h1 := (4,4,1,4,1)
  h2 := (4,4,1,4,0)
  D1 := [[4, 1, 4, 2], [4, 1, 0, 3], [4, 1, 1, 4], [4, 1, 2, 0], [4, 1, 3, 1]]
  D2 := [[4, 1, 4, 1], [4, 1, 0, 2], [4, 1, 1, 3], [4, 1, 2, 4], [4, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_78_22 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T120_78
  T2 := Q2.T120_78_2
  h1 := (4,4,2,1,1)
  h2 := (4,4,2,1,0)
  D1 := [[4, 2, 1, 1], [4, 2, 2, 3], [4, 2, 3, 0], [4, 2, 4, 2], [4, 2, 0, 4]]
  D2 := [[4, 2, 1, 0], [4, 2, 2, 2], [4, 2, 3, 4], [4, 2, 4, 1], [4, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_78_23 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T120_78
  T2 := Q2.T120_78_2
  h1 := (4,4,3,3,1)
  h2 := (4,4,3,3,0)
  D1 := [[4, 3, 3, 0], [4, 3, 4, 3], [4, 3, 0, 1], [4, 3, 1, 4], [4, 3, 2, 2]]
  D2 := [[4, 3, 3, 4], [4, 3, 4, 2], [4, 3, 0, 0], [4, 3, 1, 3], [4, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_78_24 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T120_78
  T2 := Q2.T120_78_2
  h1 := (4,4,4,0,1)
  h2 := (4,4,4,0,0)
  D1 := [[4, 4, 0, 4], [4, 4, 1, 3], [4, 4, 2, 2], [4, 4, 3, 1], [4, 4, 4, 0]]
  D2 := [[4, 4, 0, 3], [4, 4, 1, 2], [4, 4, 2, 1], [4, 4, 3, 0], [4, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
