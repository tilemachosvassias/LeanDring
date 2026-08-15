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
rest tier, chunk 45: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_120_114_4 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T120_114
  T2 := Q2.T120_114_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_114_5 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T120_114
  T2 := Q2.T120_114_2
  h1 := (1,1,0,0,0)
  h2 := (1,1,0,0,0)
  D := [[1, 0, 4, 1], [1, 0, 3, 2], [1, 0, 2, 3], [1, 0, 1, 4], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_114_10 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T120_114
  T2 := Q2.T120_114_2
  h1 := (2,2,0,1,0)
  h2 := (2,2,0,1,0)
  D := [[2, 0, 3, 3], [2, 0, 1, 1], [2, 0, 4, 4], [2, 0, 2, 2], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_114_15 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T120_114
  T2 := Q2.T120_114_2
  h1 := (3,3,0,3,1)
  h2 := (3,3,0,3,1)
  D := [[3, 0, 2, 1], [3, 0, 4, 2], [3, 0, 1, 3], [3, 0, 3, 4], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_114_20 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T120_114
  T2 := Q2.T120_114_2
  h1 := (4,4,0,1,4)
  h2 := (4,4,0,1,4)
  D := [[4, 0, 1, 0], [4, 0, 2, 0], [4, 0, 3, 0], [4, 0, 4, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_0 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_1 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_2 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_3 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_4 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_5 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 1, 0, 1], [0, 1, 0, 2], [0, 1, 0, 3], [0, 1, 0, 4], [0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_6 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 1, 1, 1], [0, 1, 1, 2], [0, 1, 1, 3], [0, 1, 1, 4], [0, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_7 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 1, 2, 1], [0, 1, 2, 2], [0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_8 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 1, 3, 1], [0, 1, 3, 2], [0, 1, 3, 3], [0, 1, 3, 4], [0, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_9 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 1, 4, 1], [0, 1, 4, 2], [0, 1, 4, 3], [0, 1, 4, 4], [0, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_10 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 2, 0, 2], [0, 2, 0, 4], [0, 2, 0, 1], [0, 2, 0, 3], [0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_11 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 2, 1, 2], [0, 2, 1, 4], [0, 2, 1, 1], [0, 2, 1, 3], [0, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_12 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 2, 2, 2], [0, 2, 2, 4], [0, 2, 2, 1], [0, 2, 2, 3], [0, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_13 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 2, 3, 2], [0, 2, 3, 4], [0, 2, 3, 1], [0, 2, 3, 3], [0, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_14 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 2, 4, 2], [0, 2, 4, 4], [0, 2, 4, 1], [0, 2, 4, 3], [0, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_15 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 3, 0, 3], [0, 3, 0, 1], [0, 3, 0, 4], [0, 3, 0, 2], [0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_16 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 3, 1, 3], [0, 3, 1, 1], [0, 3, 1, 4], [0, 3, 1, 2], [0, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_17 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 3, 2, 3], [0, 3, 2, 1], [0, 3, 2, 4], [0, 3, 2, 2], [0, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_18 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 3, 3, 3], [0, 3, 3, 1], [0, 3, 3, 4], [0, 3, 3, 2], [0, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_19 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 3, 4, 3], [0, 3, 4, 1], [0, 3, 4, 4], [0, 3, 4, 2], [0, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_20 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 4, 0, 4], [0, 4, 0, 3], [0, 4, 0, 2], [0, 4, 0, 1], [0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_21 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 4, 1, 4], [0, 4, 1, 3], [0, 4, 1, 2], [0, 4, 1, 1], [0, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_22 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (0,0,4,2,0)
  h2 := (0,0,4,2,0)
  D := [[0, 4, 2, 4], [0, 4, 2, 3], [0, 4, 2, 2], [0, 4, 2, 1], [0, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_23 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 4, 3, 4], [0, 4, 3, 3], [0, 4, 3, 2], [0, 4, 3, 1], [0, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_24 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 4, 4, 4], [0, 4, 4, 3], [0, 4, 4, 2], [0, 4, 4, 1], [0, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_25 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (1,1,0,0,0)
  h2 := (1,1,0,0,0)
  D := [[1, 0, 4, 1], [1, 0, 3, 2], [1, 0, 2, 3], [1, 0, 1, 4], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_30 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (1,1,1,0,0)
  h2 := (1,1,1,0,0)
  D := [[1, 1, 4, 1], [1, 1, 3, 3], [1, 1, 2, 0], [1, 1, 1, 2], [1, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_35 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (1,1,2,0,0)
  h2 := (1,1,2,0,0)
  D := [[1, 2, 4, 1], [1, 2, 3, 4], [1, 2, 2, 2], [1, 2, 1, 0], [1, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_40 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (1,1,3,0,0)
  h2 := (1,1,3,0,0)
  D := [[1, 3, 4, 1], [1, 3, 3, 0], [1, 3, 2, 4], [1, 3, 1, 3], [1, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_45 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (1,1,4,0,0)
  h2 := (1,1,4,0,0)
  D := [[1, 4, 4, 1], [1, 4, 3, 1], [1, 4, 2, 1], [1, 4, 1, 1], [1, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_50 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (2,2,0,1,0)
  h2 := (2,2,0,1,0)
  D := [[2, 0, 3, 3], [2, 0, 1, 1], [2, 0, 4, 4], [2, 0, 2, 2], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_55 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (2,2,1,1,0)
  h2 := (2,2,1,1,0)
  D := [[2, 1, 3, 2], [2, 1, 1, 1], [2, 1, 4, 0], [2, 1, 2, 4], [2, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_60 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (2,2,2,1,0)
  h2 := (2,2,2,1,0)
  D := [[2, 2, 3, 1], [2, 2, 1, 1], [2, 2, 4, 1], [2, 2, 2, 1], [2, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_65 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (2,2,3,1,0)
  h2 := (2,2,3,1,0)
  D := [[2, 3, 3, 0], [2, 3, 1, 1], [2, 3, 4, 2], [2, 3, 2, 3], [2, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_70 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (2,2,4,1,0)
  h2 := (2,2,4,1,0)
  D := [[2, 4, 3, 4], [2, 4, 1, 1], [2, 4, 4, 3], [2, 4, 2, 0], [2, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_75 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (3,3,0,3,1)
  h2 := (3,3,0,3,1)
  D := [[3, 0, 2, 1], [3, 0, 4, 2], [3, 0, 1, 3], [3, 0, 3, 4], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_80 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (3,3,1,3,1)
  h2 := (3,3,1,3,1)
  D := [[3, 1, 2, 4], [3, 1, 4, 1], [3, 1, 1, 3], [3, 1, 3, 0], [3, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_85 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (3,3,2,3,1)
  h2 := (3,3,2,3,1)
  D := [[3, 2, 2, 2], [3, 2, 4, 0], [3, 2, 1, 3], [3, 2, 3, 1], [3, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_90 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (3,3,3,3,1)
  h2 := (3,3,3,3,1)
  D := [[3, 3, 2, 0], [3, 3, 4, 4], [3, 3, 1, 3], [3, 3, 3, 2], [3, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_95 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (3,3,4,3,1)
  h2 := (3,3,4,3,1)
  D := [[3, 4, 2, 3], [3, 4, 4, 3], [3, 4, 1, 3], [3, 4, 3, 3], [3, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_100 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (4,4,0,1,4)
  h2 := (4,4,0,1,4)
  D := [[4, 0, 1, 0], [4, 0, 2, 0], [4, 0, 3, 0], [4, 0, 4, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_105 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (4,4,1,1,4)
  h2 := (4,4,1,1,4)
  D := [[4, 1, 1, 2], [4, 1, 2, 3], [4, 1, 3, 4], [4, 1, 4, 0], [4, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_110 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (4,4,2,1,4)
  h2 := (4,4,2,1,4)
  D := [[4, 2, 1, 4], [4, 2, 2, 1], [4, 2, 3, 3], [4, 2, 4, 0], [4, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_115 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (4,4,3,1,4)
  h2 := (4,4,3,1,4)
  D := [[4, 3, 1, 1], [4, 3, 2, 4], [4, 3, 3, 2], [4, 3, 4, 0], [4, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_120_120 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨120, by decide⟩
  m := 5
  T1 := T120_120
  T2 := Q2.T120_120_2
  h1 := (4,4,4,1,4)
  h2 := (4,4,4,1,4)
  D := [[4, 4, 1, 3], [4, 4, 2, 2], [4, 4, 3, 1], [4, 4, 4, 0], [4, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_0_0 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨0, by decide⟩
  m := 5
  T1 := T121_0
  T2 := Q2.T121_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_2_0 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T121_2
  T2 := Q2.T121_2_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_2_1 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T121_2
  T2 := Q2.T121_2_2
  h1 := (1,0,4,1,0)
  h2 := (1,0,4,1,0)
  D := [[1, 0, 1, 4], [1, 0, 1, 4], [1, 0, 1, 4], [1, 0, 1, 4], [1, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_2_2 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T121_2
  T2 := Q2.T121_2_2
  h1 := (2,0,3,2,1)
  h2 := (2,0,3,2,1)
  D := [[2, 0, 2, 2], [2, 0, 2, 2], [2, 0, 2, 2], [2, 0, 2, 2], [2, 0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_2_3 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T121_2
  T2 := Q2.T121_2_2
  h1 := (3,0,2,3,3)
  h2 := (3,0,2,3,3)
  D := [[3, 0, 3, 4], [3, 0, 3, 4], [3, 0, 3, 4], [3, 0, 3, 4], [3, 0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_2_4 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T121_2
  T2 := Q2.T121_2_2
  h1 := (4,0,1,4,1)
  h2 := (4,0,1,4,1)
  D := [[4, 0, 4, 0], [4, 0, 4, 0], [4, 0, 4, 0], [4, 0, 4, 0], [4, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_10_0 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T121_10
  T2 := Q2.T121_10_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_10_1 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T121_10
  T2 := Q2.T121_10_2
  h1 := (0,0,0,1,4)
  h2 := (0,0,0,1,4)
  D := [[0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_10_2 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T121_10
  T2 := Q2.T121_10_2
  h1 := (0,0,0,2,3)
  h2 := (0,0,0,2,3)
  D := [[0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_10_3 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T121_10
  T2 := Q2.T121_10_2
  h1 := (0,0,0,3,2)
  h2 := (0,0,0,3,2)
  D := [[0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
