/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C038

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 83: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_138_138_6 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨138, by decide⟩
  m := 5
  T1 := T138_138
  T2 := Q2.T138_138_2
  h1 := (1,1,3,3,1)
  h2 := (1,1,3,3,0)
  D := [[1, 1, 4, 4], [1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1], [1, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_138_7 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨138, by decide⟩
  m := 5
  T1 := T138_138
  T2 := Q2.T138_138_2
  h1 := (1,2,0,3,3)
  h2 := (1,2,0,3,3)
  D := [[1, 2, 3, 3], [1, 2, 3, 1], [1, 2, 3, 4], [1, 2, 3, 2], [1, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_138_8 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨138, by decide⟩
  m := 5
  T1 := T138_138
  T2 := Q2.T138_138_2
  h1 := (1,3,2,3,2)
  h2 := (1,3,2,3,3)
  D := [[1, 3, 2, 2], [1, 3, 2, 4], [1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_138_9 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨138, by decide⟩
  m := 5
  T1 := T138_138
  T2 := Q2.T138_138_2
  h1 := (1,4,4,3,3)
  h2 := (1,4,4,3,0)
  D := [[1, 4, 1, 1], [1, 4, 1, 2], [1, 4, 1, 3], [1, 4, 1, 4], [1, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_138_10 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨138, by decide⟩
  m := 5
  T1 := T138_138
  T2 := Q2.T138_138_2
  h1 := (2,0,2,1,0)
  h2 := (2,0,2,1,1)
  D := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_138_11 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨138, by decide⟩
  m := 5
  T1 := T138_138
  T2 := Q2.T138_138_2
  h1 := (2,1,4,1,1)
  h2 := (2,1,4,1,3)
  D := [[2, 1, 3, 2], [2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_138_12 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨138, by decide⟩
  m := 5
  T1 := T138_138
  T2 := Q2.T138_138_2
  h1 := (2,2,1,1,4)
  h2 := (2,2,1,1,2)
  D := [[2, 2, 1, 4], [2, 2, 1, 2], [2, 2, 1, 0], [2, 2, 1, 3], [2, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_138_13 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨138, by decide⟩
  m := 5
  T1 := T138_138
  T2 := Q2.T138_138_2
  h1 := (2,3,3,1,4)
  h2 := (2,3,3,1,3)
  D := [[2, 3, 4, 1], [2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_138_14 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨138, by decide⟩
  m := 5
  T1 := T138_138
  T2 := Q2.T138_138_2
  h1 := (2,4,0,1,1)
  h2 := (2,4,0,1,1)
  D := [[2, 4, 2, 3], [2, 4, 2, 4], [2, 4, 2, 0], [2, 4, 2, 1], [2, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_138_15 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨138, by decide⟩
  m := 5
  T1 := T138_138
  T2 := Q2.T138_138_2
  h1 := (3,0,3,4,2)
  h2 := (3,0,3,4,1)
  D := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_138_16 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨138, by decide⟩
  m := 5
  T1 := T138_138
  T2 := Q2.T138_138_2
  h1 := (3,1,0,4,4)
  h2 := (3,1,0,4,4)
  D := [[3, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_138_17 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨138, by decide⟩
  m := 5
  T1 := T138_138
  T2 := Q2.T138_138_2
  h1 := (3,2,2,4,3)
  h2 := (3,2,2,4,4)
  D := [[3, 2, 4, 2], [3, 2, 4, 0], [3, 2, 4, 3], [3, 2, 4, 1], [3, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_138_18 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨138, by decide⟩
  m := 5
  T1 := T138_138
  T2 := Q2.T138_138_2
  h1 := (3,3,4,4,4)
  h2 := (3,3,4,4,1)
  D := [[3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_138_19 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨138, by decide⟩
  m := 5
  T1 := T138_138
  T2 := Q2.T138_138_2
  h1 := (3,4,1,4,2)
  h2 := (3,4,1,4,0)
  D := [[3, 4, 3, 4], [3, 4, 3, 0], [3, 4, 3, 1], [3, 4, 3, 2], [3, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_138_20 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨138, by decide⟩
  m := 5
  T1 := T138_138
  T2 := Q2.T138_138_2
  h1 := (4,0,4,2,2)
  h2 := (4,0,4,2,4)
  D := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_138_21 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨138, by decide⟩
  m := 5
  T1 := T138_138
  T2 := Q2.T138_138_2
  h1 := (4,1,1,2,0)
  h2 := (4,1,1,2,3)
  D := [[4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4], [4, 1, 1, 3], [4, 1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_138_22 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨138, by decide⟩
  m := 5
  T1 := T138_138
  T2 := Q2.T138_138_2
  h1 := (4,2,3,2,0)
  h2 := (4,2,3,2,4)
  D := [[4, 2, 2, 2], [4, 2, 2, 0], [4, 2, 2, 3], [4, 2, 2, 1], [4, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_138_23 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨138, by decide⟩
  m := 5
  T1 := T138_138
  T2 := Q2.T138_138_2
  h1 := (4,3,0,2,2)
  h2 := (4,3,0,2,2)
  D := [[4, 3, 3, 3], [4, 3, 3, 0], [4, 3, 3, 2], [4, 3, 3, 4], [4, 3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_138_24 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨138, by decide⟩
  m := 5
  T1 := T138_138
  T2 := Q2.T138_138_2
  h1 := (4,4,2,2,1)
  h2 := (4,4,2,2,2)
  D := [[4, 4, 4, 4], [4, 4, 4, 0], [4, 4, 4, 1], [4, 4, 4, 2], [4, 4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_0_0 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨0, by decide⟩
  m := 5
  T1 := T139_0
  T2 := Q2.T139_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_5_0 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T139_5
  T2 := Q2.T139_5_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_10_0 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T139_10
  T2 := Q2.T139_10_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_10_1 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T139_10
  T2 := Q2.T139_10_2
  h1 := (0,0,0,1,4)
  h2 := (0,0,0,1,4)
  D := [[0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_10_2 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T139_10
  T2 := Q2.T139_10_2
  h1 := (0,0,0,2,3)
  h2 := (0,0,0,2,3)
  D := [[0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_10_3 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T139_10
  T2 := Q2.T139_10_2
  h1 := (0,0,0,3,2)
  h2 := (0,0,0,3,2)
  D := [[0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_10_4 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T139_10
  T2 := Q2.T139_10_2
  h1 := (0,0,0,4,1)
  h2 := (0,0,0,4,1)
  D := [[0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_12_0 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T139_12
  T2 := Q2.T139_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_12_1 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T139_12
  T2 := Q2.T139_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_12_2 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T139_12
  T2 := Q2.T139_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_12_3 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T139_12
  T2 := Q2.T139_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_12_4 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T139_12
  T2 := Q2.T139_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_23_0 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T139_23
  T2 := Q2.T139_23_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_23_1 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T139_23
  T2 := Q2.T139_23_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_23_2 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T139_23
  T2 := Q2.T139_23_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_23_3 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T139_23
  T2 := Q2.T139_23_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_23_4 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T139_23
  T2 := Q2.T139_23_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_32_0 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T139_32
  T2 := Q2.T139_32_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_32_1 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T139_32
  T2 := Q2.T139_32_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_32_2 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T139_32
  T2 := Q2.T139_32_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_32_3 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T139_32
  T2 := Q2.T139_32_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_32_4 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T139_32
  T2 := Q2.T139_32_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_32_5 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T139_32
  T2 := Q2.T139_32_2
  h1 := (1,1,4,4,0)
  h2 := (1,1,4,4,3)
  D := [[1, 1, 2, 3], [1, 1, 2, 2], [1, 1, 2, 1], [1, 1, 2, 0], [1, 1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_32_10 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T139_32
  T2 := Q2.T139_32_2
  h1 := (2,2,3,4,3)
  h2 := (2,2,3,4,4)
  D := [[2, 2, 3, 1], [2, 2, 3, 4], [2, 2, 3, 2], [2, 2, 3, 0], [2, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_32_15 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T139_32
  T2 := Q2.T139_32_2
  h1 := (3,3,2,0,0)
  h2 := (3,3,2,0,4)
  D := [[3, 3, 3, 0], [3, 3, 3, 2], [3, 3, 3, 4], [3, 3, 3, 1], [3, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_32_20 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T139_32
  T2 := Q2.T139_32_2
  h1 := (4,4,1,2,2)
  h2 := (4,4,1,2,4)
  D := [[4, 4, 2, 1], [4, 4, 2, 2], [4, 4, 2, 3], [4, 4, 2, 4], [4, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_34_0 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T139_34
  T2 := Q2.T139_34_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_34_1 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T139_34
  T2 := Q2.T139_34_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_34_2 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T139_34
  T2 := Q2.T139_34_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_34_3 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T139_34
  T2 := Q2.T139_34_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_34_4 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T139_34
  T2 := Q2.T139_34_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_38_0 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T139_38
  T2 := Q2.T139_38_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_38_1 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T139_38
  T2 := Q2.T139_38_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_38_2 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T139_38
  T2 := Q2.T139_38_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_38_3 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T139_38
  T2 := Q2.T139_38_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_38_4 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T139_38
  T2 := Q2.T139_38_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_45_0 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T139_45
  T2 := Q2.T139_45_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_45_1 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T139_45
  T2 := Q2.T139_45_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_45_2 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T139_45
  T2 := Q2.T139_45_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_45_3 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T139_45
  T2 := Q2.T139_45_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_45_4 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T139_45
  T2 := Q2.T139_45_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
