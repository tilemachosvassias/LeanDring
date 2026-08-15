/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C037

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 79: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_136_136_16 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨136, by decide⟩
  m := 5
  T1 := T136_136
  T2 := Q2.T136_136_2
  h1 := (3,1,3,0,3)
  h2 := (3,1,3,0,3)
  D := [[3, 1, 2, 3], [3, 1, 2, 2], [3, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_136_17 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨136, by decide⟩
  m := 5
  T1 := T136_136
  T2 := Q2.T136_136_2
  h1 := (3,2,3,0,1)
  h2 := (3,2,3,0,1)
  D := [[3, 2, 4, 1], [3, 2, 4, 4], [3, 2, 4, 2], [3, 2, 4, 0], [3, 2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_136_18 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨136, by decide⟩
  m := 5
  T1 := T136_136
  T2 := Q2.T136_136_2
  h1 := (3,3,3,0,4)
  h2 := (3,3,3,0,4)
  D := [[3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_136_19 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨136, by decide⟩
  m := 5
  T1 := T136_136
  T2 := Q2.T136_136_2
  h1 := (3,4,3,0,2)
  h2 := (3,4,3,0,2)
  D := [[3, 4, 3, 2], [3, 4, 3, 3], [3, 4, 3, 4], [3, 4, 3, 0], [3, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_136_20 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨136, by decide⟩
  m := 5
  T1 := T136_136
  T2 := Q2.T136_136_2
  h1 := (4,0,4,0,0)
  h2 := (4,0,4,0,0)
  D := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_136_21 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨136, by decide⟩
  m := 5
  T1 := T136_136
  T2 := Q2.T136_136_2
  h1 := (4,1,4,0,4)
  h2 := (4,1,4,0,4)
  D := [[4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_136_22 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨136, by decide⟩
  m := 5
  T1 := T136_136
  T2 := Q2.T136_136_2
  h1 := (4,2,4,0,3)
  h2 := (4,2,4,0,3)
  D := [[4, 2, 2, 1], [4, 2, 2, 4], [4, 2, 2, 2], [4, 2, 2, 0], [4, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_136_23 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨136, by decide⟩
  m := 5
  T1 := T136_136
  T2 := Q2.T136_136_2
  h1 := (4,3,4,0,2)
  h2 := (4,3,4,0,2)
  D := [[4, 3, 3, 4], [4, 3, 3, 1], [4, 3, 3, 3], [4, 3, 3, 0], [4, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_136_24 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨136, by decide⟩
  m := 5
  T1 := T136_136
  T2 := Q2.T136_136_2
  h1 := (4,4,4,0,1)
  h2 := (4,4,4,0,1)
  D := [[4, 4, 4, 2], [4, 4, 4, 3], [4, 4, 4, 4], [4, 4, 4, 0], [4, 4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_0_0 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨0, by decide⟩
  m := 5
  T1 := T137_0
  T2 := Q2.T137_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_5_0 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T137_5
  T2 := Q2.T137_5_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_5_1 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T137_5
  T2 := Q2.T137_5_2
  h1 := (1,0,1,4,4)
  h2 := (1,0,1,4,4)
  D := [[1, 0, 0, 4], [1, 0, 0, 4], [1, 0, 0, 4], [1, 0, 0, 4], [1, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_5_2 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T137_5
  T2 := Q2.T137_5_2
  h1 := (2,0,2,3,2)
  h2 := (2,0,2,3,2)
  D := [[2, 0, 0, 3], [2, 0, 0, 3], [2, 0, 0, 3], [2, 0, 0, 3], [2, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_5_3 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T137_5
  T2 := Q2.T137_5_2
  h1 := (3,0,3,2,4)
  h2 := (3,0,3,2,4)
  D := [[3, 0, 0, 2], [3, 0, 0, 2], [3, 0, 0, 2], [3, 0, 0, 2], [3, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_5_4 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T137_5
  T2 := Q2.T137_5_2
  h1 := (4,0,4,1,0)
  h2 := (4,0,4,1,0)
  D := [[4, 0, 0, 1], [4, 0, 0, 1], [4, 0, 0, 1], [4, 0, 0, 1], [4, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_10_0 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T137_10
  T2 := Q2.T137_10_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_10_1 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T137_10
  T2 := Q2.T137_10_2
  h1 := (0,0,0,1,4)
  h2 := (0,0,0,1,4)
  D := [[0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_10_2 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T137_10
  T2 := Q2.T137_10_2
  h1 := (0,0,0,2,3)
  h2 := (0,0,0,2,3)
  D := [[0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_10_3 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T137_10
  T2 := Q2.T137_10_2
  h1 := (0,0,0,3,2)
  h2 := (0,0,0,3,2)
  D := [[0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_10_4 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T137_10
  T2 := Q2.T137_10_2
  h1 := (0,0,0,4,1)
  h2 := (0,0,0,4,1)
  D := [[0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_12_0 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T137_12
  T2 := Q2.T137_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_12_1 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T137_12
  T2 := Q2.T137_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_12_2 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T137_12
  T2 := Q2.T137_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_12_3 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T137_12
  T2 := Q2.T137_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_12_4 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T137_12
  T2 := Q2.T137_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_23_0 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T137_23
  T2 := Q2.T137_23_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_23_1 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T137_23
  T2 := Q2.T137_23_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_23_2 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T137_23
  T2 := Q2.T137_23_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_23_3 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T137_23
  T2 := Q2.T137_23_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_23_4 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T137_23
  T2 := Q2.T137_23_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_23_5 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T137_23
  T2 := Q2.T137_23_2
  h1 := (1,0,1,4,0)
  h2 := (1,0,1,4,0)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_23_10 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T137_23
  T2 := Q2.T137_23_2
  h1 := (2,0,2,3,4)
  h2 := (2,0,2,3,4)
  D := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_23_15 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T137_23
  T2 := Q2.T137_23_2
  h1 := (3,0,3,2,2)
  h2 := (3,0,3,2,2)
  D := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_23_20 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T137_23
  T2 := Q2.T137_23_2
  h1 := (4,0,4,1,4)
  h2 := (4,0,4,1,4)
  D := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_30_0 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T137_30
  T2 := Q2.T137_30_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_30_1 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T137_30
  T2 := Q2.T137_30_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_30_2 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T137_30
  T2 := Q2.T137_30_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_30_3 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T137_30
  T2 := Q2.T137_30_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_30_4 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T137_30
  T2 := Q2.T137_30_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_37_0 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T137_37
  T2 := Q2.T137_37_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_37_1 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T137_37
  T2 := Q2.T137_37_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_37_2 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T137_37
  T2 := Q2.T137_37_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_37_3 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T137_37
  T2 := Q2.T137_37_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_37_4 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T137_37
  T2 := Q2.T137_37_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_41_0 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T137_41
  T2 := Q2.T137_41_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_41_1 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T137_41
  T2 := Q2.T137_41_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_41_2 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T137_41
  T2 := Q2.T137_41_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_41_3 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T137_41
  T2 := Q2.T137_41_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_41_4 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T137_41
  T2 := Q2.T137_41_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_43_0 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T137_43
  T2 := Q2.T137_43_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_43_1 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T137_43
  T2 := Q2.T137_43_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_43_2 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T137_43
  T2 := Q2.T137_43_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_43_3 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T137_43
  T2 := Q2.T137_43_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_43_4 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T137_43
  T2 := Q2.T137_43_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_49_0 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T137_49
  T2 := Q2.T137_49_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_49_1 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T137_49
  T2 := Q2.T137_49_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_49_2 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T137_49
  T2 := Q2.T137_49_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_49_3 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T137_49
  T2 := Q2.T137_49_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_49_4 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T137_49
  T2 := Q2.T137_49_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_49_5 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T137_49
  T2 := Q2.T137_49_2
  h1 := (1,4,0,3,4)
  h2 := (1,4,0,3,4)
  D := [[1, 4, 0, 0], [1, 4, 0, 1], [1, 4, 0, 2], [1, 4, 0, 3], [1, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
