/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C018

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 169: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_76_52_10 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T76_52
  T2 := Q2.T76_52_2
  h1 := (2,2,0,4,1)
  h2 := (2,2,0,4,2)
  D := [[2, 0, 1], [2, 0, 4], [2, 0, 2], [2, 0, 0], [2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_52_15 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T76_52
  T2 := Q2.T76_52_2
  h1 := (3,3,0,0,1)
  h2 := (3,3,0,0,0)
  D := [[3, 0, 4], [3, 0, 1], [3, 0, 3], [3, 0, 0], [3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_52_20 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T76_52
  T2 := Q2.T76_52_2
  h1 := (4,4,0,2,2)
  h2 := (4,4,0,2,4)
  D := [[4, 0, 2], [4, 0, 3], [4, 0, 4], [4, 0, 0], [4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_0 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_1 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_2 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_3 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_4 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_5 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_6 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (0,0,1,4,1)
  h2 := (0,0,1,4,1)
  D := [[0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_7 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (0,0,1,4,2)
  h2 := (0,0,1,4,2)
  D := [[0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_8 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (0,0,1,4,3)
  h2 := (0,0,1,4,3)
  D := [[0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_9 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (0,0,1,4,4)
  h2 := (0,0,1,4,4)
  D := [[0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_10 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_11 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (0,0,2,3,1)
  h2 := (0,0,2,3,1)
  D := [[0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_12 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (0,0,2,3,2)
  h2 := (0,0,2,3,2)
  D := [[0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_13 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (0,0,2,3,3)
  h2 := (0,0,2,3,3)
  D := [[0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_14 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (0,0,2,3,4)
  h2 := (0,0,2,3,4)
  D := [[0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_15 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_16 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (0,0,3,2,1)
  h2 := (0,0,3,2,1)
  D := [[0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_17 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (0,0,3,2,2)
  h2 := (0,0,3,2,2)
  D := [[0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_18 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (0,0,3,2,3)
  h2 := (0,0,3,2,3)
  D := [[0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_19 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (0,0,3,2,4)
  h2 := (0,0,3,2,4)
  D := [[0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_20 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_21 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (0,0,4,1,1)
  h2 := (0,0,4,1,1)
  D := [[0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_22 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (0,0,4,1,2)
  h2 := (0,0,4,1,2)
  D := [[0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_23 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (0,0,4,1,3)
  h2 := (0,0,4,1,3)
  D := [[0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_24 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (0,0,4,1,4)
  h2 := (0,0,4,1,4)
  D := [[0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_25 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (1,1,0,4,1)
  h2 := (1,1,0,4,4)
  D := [[1, 0, 3], [1, 0, 2], [1, 0, 1], [1, 0, 0], [1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_30 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (1,1,1,3,1)
  h2 := (1,1,1,3,4)
  D := [[1, 1, 3], [1, 1, 2], [1, 1, 1], [1, 1, 0], [1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_35 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (1,1,2,2,1)
  h2 := (1,1,2,2,4)
  D := [[1, 2, 3], [1, 2, 2], [1, 2, 1], [1, 2, 0], [1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_40 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (1,1,3,1,1)
  h2 := (1,1,3,1,4)
  D := [[1, 3, 3], [1, 3, 2], [1, 3, 1], [1, 3, 0], [1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_45 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (1,1,4,0,1)
  h2 := (1,1,4,0,4)
  D := [[1, 4, 3], [1, 4, 2], [1, 4, 1], [1, 4, 0], [1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_50 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (2,2,0,4,1)
  h2 := (2,2,0,4,2)
  D := [[2, 0, 1], [2, 0, 4], [2, 0, 2], [2, 0, 0], [2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_55 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (2,2,1,3,1)
  h2 := (2,2,1,3,2)
  D := [[2, 1, 1], [2, 1, 4], [2, 1, 2], [2, 1, 0], [2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_60 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (2,2,2,2,1)
  h2 := (2,2,2,2,2)
  D := [[2, 2, 1], [2, 2, 4], [2, 2, 2], [2, 2, 0], [2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_65 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (2,2,3,1,1)
  h2 := (2,2,3,1,2)
  D := [[2, 3, 1], [2, 3, 4], [2, 3, 2], [2, 3, 0], [2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_70 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (2,2,4,0,1)
  h2 := (2,2,4,0,2)
  D := [[2, 4, 1], [2, 4, 4], [2, 4, 2], [2, 4, 0], [2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_75 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (3,3,0,0,1)
  h2 := (3,3,0,0,0)
  D := [[3, 0, 4], [3, 0, 1], [3, 0, 3], [3, 0, 0], [3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_80 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (3,3,1,4,1)
  h2 := (3,3,1,4,0)
  D := [[3, 1, 4], [3, 1, 1], [3, 1, 3], [3, 1, 0], [3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_85 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (3,3,2,3,1)
  h2 := (3,3,2,3,0)
  D := [[3, 2, 4], [3, 2, 1], [3, 2, 3], [3, 2, 0], [3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_90 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (3,3,3,2,1)
  h2 := (3,3,3,2,0)
  D := [[3, 3, 4], [3, 3, 1], [3, 3, 3], [3, 3, 0], [3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_95 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (3,3,4,1,1)
  h2 := (3,3,4,1,0)
  D := [[3, 4, 4], [3, 4, 1], [3, 4, 3], [3, 4, 0], [3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_100 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (4,4,0,2,2)
  h2 := (4,4,0,2,4)
  D := [[4, 0, 2], [4, 0, 3], [4, 0, 4], [4, 0, 0], [4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_105 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (4,4,1,1,2)
  h2 := (4,4,1,1,4)
  D := [[4, 1, 2], [4, 1, 3], [4, 1, 4], [4, 1, 0], [4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_110 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (4,4,2,0,2)
  h2 := (4,4,2,0,4)
  D := [[4, 2, 2], [4, 2, 3], [4, 2, 4], [4, 2, 0], [4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_115 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (4,4,3,4,2)
  h2 := (4,4,3,4,4)
  D := [[4, 3, 2], [4, 3, 3], [4, 3, 4], [4, 3, 0], [4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_76_120 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T76_76
  T2 := Q2.T76_76_2
  h1 := (4,4,4,3,2)
  h2 := (4,4,4,3,4)
  D := [[4, 4, 2], [4, 4, 3], [4, 4, 4], [4, 4, 0], [4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_77_0_0 : ColCert where
  rK := ⟨77, by decide⟩
  rH := ⟨0, by decide⟩
  m := 25
  T1 := T77_0
  T2 := Q2.T77_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_77_7_0 : ColCert where
  rK := ⟨77, by decide⟩
  rH := ⟨7, by decide⟩
  m := 25
  T1 := T77_7
  T2 := Q2.T77_7_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_77_7_1 : ColCert where
  rK := ⟨77, by decide⟩
  rH := ⟨7, by decide⟩
  m := 25
  T1 := T77_7
  T2 := Q2.T77_7_2
  h1 := (0,0,1,3,4)
  h2 := (0,0,1,3,4)
  D := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_77_7_2 : ColCert where
  rK := ⟨77, by decide⟩
  rH := ⟨7, by decide⟩
  m := 25
  T1 := T77_7
  T2 := Q2.T77_7_2
  h1 := (0,0,2,1,3)
  h2 := (0,0,2,1,3)
  D := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_77_7_3 : ColCert where
  rK := ⟨77, by decide⟩
  rH := ⟨7, by decide⟩
  m := 25
  T1 := T77_7
  T2 := Q2.T77_7_2
  h1 := (0,0,3,4,2)
  h2 := (0,0,3,4,2)
  D := [[0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_77_7_4 : ColCert where
  rK := ⟨77, by decide⟩
  rH := ⟨7, by decide⟩
  m := 25
  T1 := T77_7
  T2 := Q2.T77_7_2
  h1 := (0,0,4,2,1)
  h2 := (0,0,4,2,1)
  D := [[0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_77_12_0 : ColCert where
  rK := ⟨77, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T77_12
  T2 := Q2.T77_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_77_12_1 : ColCert where
  rK := ⟨77, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T77_12
  T2 := Q2.T77_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_77_12_2 : ColCert where
  rK := ⟨77, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T77_12
  T2 := Q2.T77_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_77_12_3 : ColCert where
  rK := ⟨77, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T77_12
  T2 := Q2.T77_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_77_12_4 : ColCert where
  rK := ⟨77, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T77_12
  T2 := Q2.T77_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_77_25_0 : ColCert where
  rK := ⟨77, by decide⟩
  rH := ⟨25, by decide⟩
  m := 25
  T1 := T77_25
  T2 := Q2.T77_25_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
