/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C037
import LeanDring.P5.Data.EntryK.C038

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 81: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_137_137_1 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨137, by decide⟩
  m := 5
  T1 := T137_137
  T2 := Q2.T137_137_2
  h1 := (0,1,1,0,0)
  h2 := (0,1,1,0,0)
  D := [[0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_137_2 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨137, by decide⟩
  m := 5
  T1 := T137_137
  T2 := Q2.T137_137_2
  h1 := (0,2,2,0,1)
  h2 := (0,2,2,0,1)
  D := [[0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_137_3 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨137, by decide⟩
  m := 5
  T1 := T137_137
  T2 := Q2.T137_137_2
  h1 := (0,3,3,0,3)
  h2 := (0,3,3,0,3)
  D := [[0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_137_4 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨137, by decide⟩
  m := 5
  T1 := T137_137
  T2 := Q2.T137_137_2
  h1 := (0,4,4,0,1)
  h2 := (0,4,4,0,1)
  D := [[0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_137_5 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨137, by decide⟩
  m := 5
  T1 := T137_137
  T2 := Q2.T137_137_2
  h1 := (1,0,1,4,0)
  h2 := (1,0,1,4,0)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_137_6 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨137, by decide⟩
  m := 5
  T1 := T137_137
  T2 := Q2.T137_137_2
  h1 := (1,1,2,4,1)
  h2 := (1,1,2,4,1)
  D := [[1, 1, 4, 0], [1, 1, 4, 4], [1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_137_7 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨137, by decide⟩
  m := 5
  T1 := T137_137
  T2 := Q2.T137_137_2
  h1 := (1,2,3,4,3)
  h2 := (1,2,3,4,3)
  D := [[1, 2, 3, 0], [1, 2, 3, 3], [1, 2, 3, 1], [1, 2, 3, 4], [1, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_137_8 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨137, by decide⟩
  m := 5
  T1 := T137_137
  T2 := Q2.T137_137_2
  h1 := (1,3,4,4,1)
  h2 := (1,3,4,4,1)
  D := [[1, 3, 2, 0], [1, 3, 2, 2], [1, 3, 2, 4], [1, 3, 2, 1], [1, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_137_9 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨137, by decide⟩
  m := 5
  T1 := T137_137
  T2 := Q2.T137_137_2
  h1 := (1,4,0,4,0)
  h2 := (1,4,0,4,0)
  D := [[1, 4, 1, 0], [1, 4, 1, 1], [1, 4, 1, 2], [1, 4, 1, 3], [1, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_137_10 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨137, by decide⟩
  m := 5
  T1 := T137_137
  T2 := Q2.T137_137_2
  h1 := (2,0,2,3,4)
  h2 := (2,0,2,3,4)
  D := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_137_11 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨137, by decide⟩
  m := 5
  T1 := T137_137
  T2 := Q2.T137_137_2
  h1 := (2,1,3,3,1)
  h2 := (2,1,3,3,1)
  D := [[2, 1, 3, 3], [2, 1, 3, 2], [2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_137_12 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨137, by decide⟩
  m := 5
  T1 := T137_137
  T2 := Q2.T137_137_2
  h1 := (2,2,4,3,4)
  h2 := (2,2,4,3,4)
  D := [[2, 2, 1, 1], [2, 2, 1, 4], [2, 2, 1, 2], [2, 2, 1, 0], [2, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_137_13 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨137, by decide⟩
  m := 5
  T1 := T137_137
  T2 := Q2.T137_137_2
  h1 := (2,3,0,3,3)
  h2 := (2,3,0,3,3)
  D := [[2, 3, 4, 4], [2, 3, 4, 1], [2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_137_14 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨137, by decide⟩
  m := 5
  T1 := T137_137
  T2 := Q2.T137_137_2
  h1 := (2,4,1,3,3)
  h2 := (2,4,1,3,3)
  D := [[2, 4, 2, 2], [2, 4, 2, 3], [2, 4, 2, 4], [2, 4, 2, 0], [2, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_137_15 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨137, by decide⟩
  m := 5
  T1 := T137_137
  T2 := Q2.T137_137_2
  h1 := (3,0,3,2,2)
  h2 := (3,0,3,2,2)
  D := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_137_16 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨137, by decide⟩
  m := 5
  T1 := T137_137
  T2 := Q2.T137_137_2
  h1 := (3,1,4,2,0)
  h2 := (3,1,4,2,0)
  D := [[3, 1, 2, 2], [3, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 4], [3, 1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_137_17 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨137, by decide⟩
  m := 5
  T1 := T137_137
  T2 := Q2.T137_137_2
  h1 := (3,2,0,2,4)
  h2 := (3,2,0,2,4)
  D := [[3, 2, 4, 4], [3, 2, 4, 2], [3, 2, 4, 0], [3, 2, 4, 3], [3, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_137_18 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨137, by decide⟩
  m := 5
  T1 := T137_137
  T2 := Q2.T137_137_2
  h1 := (3,3,1,2,4)
  h2 := (3,3,1,2,4)
  D := [[3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2], [3, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_137_19 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨137, by decide⟩
  m := 5
  T1 := T137_137
  T2 := Q2.T137_137_2
  h1 := (3,4,2,2,0)
  h2 := (3,4,2,2,0)
  D := [[3, 4, 3, 3], [3, 4, 3, 4], [3, 4, 3, 0], [3, 4, 3, 1], [3, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_137_20 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨137, by decide⟩
  m := 5
  T1 := T137_137
  T2 := Q2.T137_137_2
  h1 := (4,0,4,1,4)
  h2 := (4,0,4,1,4)
  D := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_137_21 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨137, by decide⟩
  m := 5
  T1 := T137_137
  T2 := Q2.T137_137_2
  h1 := (4,1,0,1,3)
  h2 := (4,1,0,1,3)
  D := [[4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4], [4, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_137_22 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨137, by decide⟩
  m := 5
  T1 := T137_137
  T2 := Q2.T137_137_2
  h1 := (4,2,1,1,3)
  h2 := (4,2,1,1,3)
  D := [[4, 2, 2, 4], [4, 2, 2, 2], [4, 2, 2, 0], [4, 2, 2, 3], [4, 2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_137_23 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨137, by decide⟩
  m := 5
  T1 := T137_137
  T2 := Q2.T137_137_2
  h1 := (4,3,2,1,4)
  h2 := (4,3,2,1,4)
  D := [[4, 3, 3, 1], [4, 3, 3, 3], [4, 3, 3, 0], [4, 3, 3, 2], [4, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_137_24 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨137, by decide⟩
  m := 5
  T1 := T137_137
  T2 := Q2.T137_137_2
  h1 := (4,4,3,1,1)
  h2 := (4,4,3,1,1)
  D := [[4, 4, 4, 3], [4, 4, 4, 4], [4, 4, 4, 0], [4, 4, 4, 1], [4, 4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_0_0 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨0, by decide⟩
  m := 5
  T1 := T138_0
  T2 := Q2.T138_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_5_0 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T138_5
  T2 := Q2.T138_5_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_10_0 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T138_10
  T2 := Q2.T138_10_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_10_1 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T138_10
  T2 := Q2.T138_10_2
  h1 := (0,0,0,1,4)
  h2 := (0,0,0,1,4)
  D := [[0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_10_2 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T138_10
  T2 := Q2.T138_10_2
  h1 := (0,0,0,2,3)
  h2 := (0,0,0,2,3)
  D := [[0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_10_3 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T138_10
  T2 := Q2.T138_10_2
  h1 := (0,0,0,3,2)
  h2 := (0,0,0,3,2)
  D := [[0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_10_4 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T138_10
  T2 := Q2.T138_10_2
  h1 := (0,0,0,4,1)
  h2 := (0,0,0,4,1)
  D := [[0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_12_0 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T138_12
  T2 := Q2.T138_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_12_1 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T138_12
  T2 := Q2.T138_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_12_2 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T138_12
  T2 := Q2.T138_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_12_3 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T138_12
  T2 := Q2.T138_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_12_4 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T138_12
  T2 := Q2.T138_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_23_0 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T138_23
  T2 := Q2.T138_23_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_23_1 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T138_23
  T2 := Q2.T138_23_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_23_2 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T138_23
  T2 := Q2.T138_23_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_23_3 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T138_23
  T2 := Q2.T138_23_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_23_4 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T138_23
  T2 := Q2.T138_23_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_31_0 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T138_31
  T2 := Q2.T138_31_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_31_1 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T138_31
  T2 := Q2.T138_31_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_31_2 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T138_31
  T2 := Q2.T138_31_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_31_3 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T138_31
  T2 := Q2.T138_31_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_31_4 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T138_31
  T2 := Q2.T138_31_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_31_5 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T138_31
  T2 := Q2.T138_31_2
  h1 := (1,3,2,0,4)
  h2 := (1,3,2,0,0)
  D := [[1, 3, 4, 2], [1, 3, 4, 4], [1, 3, 4, 1], [1, 3, 4, 3], [1, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_33_0 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T138_33
  T2 := Q2.T138_33_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_33_1 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T138_33
  T2 := Q2.T138_33_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_33_2 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T138_33
  T2 := Q2.T138_33_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_33_3 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T138_33
  T2 := Q2.T138_33_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_33_4 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T138_33
  T2 := Q2.T138_33_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_42_0 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T138_42
  T2 := Q2.T138_42_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_42_1 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T138_42
  T2 := Q2.T138_42_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_42_2 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T138_42
  T2 := Q2.T138_42_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_42_3 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T138_42
  T2 := Q2.T138_42_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_42_4 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T138_42
  T2 := Q2.T138_42_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_44_0 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T138_44
  T2 := Q2.T138_44_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_44_1 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T138_44
  T2 := Q2.T138_44_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_44_2 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T138_44
  T2 := Q2.T138_44_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
