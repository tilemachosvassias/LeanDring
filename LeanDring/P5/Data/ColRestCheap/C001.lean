/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryA.C001
import LeanDring.P5.Data.EntryA.C004

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 0: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_13_1_0 : ColCert where
  rK := ⟨13, by decide⟩
  rH := ⟨1, by decide⟩
  m := 25
  T1 := T13_1
  T2 := Q2.T13_1_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_13_1_1 : ColCert where
  rK := ⟨13, by decide⟩
  rH := ⟨1, by decide⟩
  m := 25
  T1 := T13_1
  T2 := Q2.T13_1_2
  h1 := (0,0,1,4,4)
  h2 := (0,0,1,4,4)
  D := [[1, 4], [1, 4], [1, 4], [1, 4], [1, 4], [1, 4], [1, 4], [1, 4], [1, 4], [1, 4], [1, 4], [1, 4], [1, 4], [1, 4], [1, 4], [1, 4], [1, 4], [1, 4], [1, 4], [1, 4], [1, 4], [1, 4], [1, 4], [1, 4], [1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_13_1_2 : ColCert where
  rK := ⟨13, by decide⟩
  rH := ⟨1, by decide⟩
  m := 25
  T1 := T13_1
  T2 := Q2.T13_1_2
  h1 := (0,0,2,3,3)
  h2 := (0,0,2,3,3)
  D := [[2, 3], [2, 3], [2, 3], [2, 3], [2, 3], [2, 3], [2, 3], [2, 3], [2, 3], [2, 3], [2, 3], [2, 3], [2, 3], [2, 3], [2, 3], [2, 3], [2, 3], [2, 3], [2, 3], [2, 3], [2, 3], [2, 3], [2, 3], [2, 3], [2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_13_1_3 : ColCert where
  rK := ⟨13, by decide⟩
  rH := ⟨1, by decide⟩
  m := 25
  T1 := T13_1
  T2 := Q2.T13_1_2
  h1 := (0,0,3,2,2)
  h2 := (0,0,3,2,2)
  D := [[3, 2], [3, 2], [3, 2], [3, 2], [3, 2], [3, 2], [3, 2], [3, 2], [3, 2], [3, 2], [3, 2], [3, 2], [3, 2], [3, 2], [3, 2], [3, 2], [3, 2], [3, 2], [3, 2], [3, 2], [3, 2], [3, 2], [3, 2], [3, 2], [3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_13_1_4 : ColCert where
  rK := ⟨13, by decide⟩
  rH := ⟨1, by decide⟩
  m := 25
  T1 := T13_1
  T2 := Q2.T13_1_2
  h1 := (0,0,4,1,1)
  h2 := (0,0,4,1,1)
  D := [[4, 1], [4, 1], [4, 1], [4, 1], [4, 1], [4, 1], [4, 1], [4, 1], [4, 1], [4, 1], [4, 1], [4, 1], [4, 1], [4, 1], [4, 1], [4, 1], [4, 1], [4, 1], [4, 1], [4, 1], [4, 1], [4, 1], [4, 1], [4, 1], [4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_13_13_0 : ColCert where
  rK := ⟨13, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T13_13
  T2 := Q2.T13_13_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_13_13_1 : ColCert where
  rK := ⟨13, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T13_13
  T2 := Q2.T13_13_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 1], [0, 1], [0, 1], [0, 1], [0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_13_13_2 : ColCert where
  rK := ⟨13, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T13_13
  T2 := Q2.T13_13_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 2], [0, 2], [0, 2], [0, 2], [0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_13_13_3 : ColCert where
  rK := ⟨13, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T13_13
  T2 := Q2.T13_13_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 3], [0, 3], [0, 3], [0, 3], [0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_13_13_4 : ColCert where
  rK := ⟨13, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T13_13
  T2 := Q2.T13_13_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_13_13_9 : ColCert where
  rK := ⟨13, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T13_13
  T2 := Q2.T13_13_2
  h1 := (0,0,1,4,4)
  h2 := (0,0,1,4,4)
  D := [[1, 4], [1, 4], [1, 4], [1, 4], [1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_13_13_10 : ColCert where
  rK := ⟨13, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T13_13
  T2 := Q2.T13_13_2
  h1 := (0,0,2,0,3)
  h2 := (0,0,2,0,3)
  D := [[2, 0], [2, 0], [2, 0], [2, 0], [2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_13_13_11 : ColCert where
  rK := ⟨13, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T13_13
  T2 := Q2.T13_13_2
  h1 := (0,0,2,1,3)
  h2 := (0,0,2,1,3)
  D := [[2, 1], [2, 1], [2, 1], [2, 1], [2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_13_13_12 : ColCert where
  rK := ⟨13, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T13_13
  T2 := Q2.T13_13_2
  h1 := (0,0,2,2,3)
  h2 := (0,0,2,2,3)
  D := [[2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_13_13_13 : ColCert where
  rK := ⟨13, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T13_13
  T2 := Q2.T13_13_2
  h1 := (0,0,2,3,3)
  h2 := (0,0,2,3,3)
  D := [[2, 3], [2, 3], [2, 3], [2, 3], [2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_13_13_14 : ColCert where
  rK := ⟨13, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T13_13
  T2 := Q2.T13_13_2
  h1 := (0,0,2,4,3)
  h2 := (0,0,2,4,3)
  D := [[2, 4], [2, 4], [2, 4], [2, 4], [2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_13_13_15 : ColCert where
  rK := ⟨13, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T13_13
  T2 := Q2.T13_13_2
  h1 := (0,0,3,0,2)
  h2 := (0,0,3,0,2)
  D := [[3, 0], [3, 0], [3, 0], [3, 0], [3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_13_13_16 : ColCert where
  rK := ⟨13, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T13_13
  T2 := Q2.T13_13_2
  h1 := (0,0,3,1,2)
  h2 := (0,0,3,1,2)
  D := [[3, 1], [3, 1], [3, 1], [3, 1], [3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_13_13_17 : ColCert where
  rK := ⟨13, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T13_13
  T2 := Q2.T13_13_2
  h1 := (0,0,3,2,2)
  h2 := (0,0,3,2,2)
  D := [[3, 2], [3, 2], [3, 2], [3, 2], [3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_13_13_18 : ColCert where
  rK := ⟨13, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T13_13
  T2 := Q2.T13_13_2
  h1 := (0,0,3,3,2)
  h2 := (0,0,3,3,2)
  D := [[3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_13_13_19 : ColCert where
  rK := ⟨13, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T13_13
  T2 := Q2.T13_13_2
  h1 := (0,0,3,4,2)
  h2 := (0,0,3,4,2)
  D := [[3, 4], [3, 4], [3, 4], [3, 4], [3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_13_13_20 : ColCert where
  rK := ⟨13, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T13_13
  T2 := Q2.T13_13_2
  h1 := (0,0,4,0,1)
  h2 := (0,0,4,0,1)
  D := [[4, 0], [4, 0], [4, 0], [4, 0], [4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_13_13_21 : ColCert where
  rK := ⟨13, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T13_13
  T2 := Q2.T13_13_2
  h1 := (0,0,4,1,1)
  h2 := (0,0,4,1,1)
  D := [[4, 1], [4, 1], [4, 1], [4, 1], [4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_13_13_22 : ColCert where
  rK := ⟨13, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T13_13
  T2 := Q2.T13_13_2
  h1 := (0,0,4,2,1)
  h2 := (0,0,4,2,1)
  D := [[4, 2], [4, 2], [4, 2], [4, 2], [4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_13_13_23 : ColCert where
  rK := ⟨13, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T13_13
  T2 := Q2.T13_13_2
  h1 := (0,0,4,3,1)
  h2 := (0,0,4,3,1)
  D := [[4, 3], [4, 3], [4, 3], [4, 3], [4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_13_13_24 : ColCert where
  rK := ⟨13, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T13_13
  T2 := Q2.T13_13_2
  h1 := (0,0,4,4,1)
  h2 := (0,0,4,4,1)
  D := [[4, 4], [4, 4], [4, 4], [4, 4], [4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_2_0 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T16_2
  T2 := Q2.T16_2_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_2_1 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T16_2
  T2 := Q2.T16_2_2
  h1 := (1,0,4,1,0)
  h2 := (1,0,4,1,0)
  D := [[1, 4], [1, 4], [1, 4], [1, 4], [1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_2_2 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T16_2
  T2 := Q2.T16_2_2
  h1 := (2,0,3,2,1)
  h2 := (2,0,3,2,1)
  D := [[2, 3], [2, 3], [2, 3], [2, 3], [2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_2_3 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T16_2
  T2 := Q2.T16_2_2
  h1 := (3,0,2,3,3)
  h2 := (3,0,2,3,3)
  D := [[3, 2], [3, 2], [3, 2], [3, 2], [3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_2_4 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T16_2
  T2 := Q2.T16_2_2
  h1 := (4,0,1,4,1)
  h2 := (4,0,1,4,1)
  D := [[4, 1], [4, 1], [4, 1], [4, 1], [4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_3_0 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T16_3
  T2 := Q2.T16_3_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_3_1 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T16_3
  T2 := Q2.T16_3_2
  h1 := (1,0,2,3,1)
  h2 := (1,0,2,3,1)
  D := [[1, 2], [1, 2], [1, 2], [1, 2], [1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_3_2 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T16_3
  T2 := Q2.T16_3_2
  h1 := (2,0,4,1,0)
  h2 := (2,0,4,1,0)
  D := [[2, 4], [2, 4], [2, 4], [2, 4], [2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_3_3 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T16_3
  T2 := Q2.T16_3_2
  h1 := (3,0,1,4,2)
  h2 := (3,0,1,4,2)
  D := [[3, 1], [3, 1], [3, 1], [3, 1], [3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_3_4 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T16_3
  T2 := Q2.T16_3_2
  h1 := (4,0,3,2,2)
  h2 := (4,0,3,2,2)
  D := [[4, 3], [4, 3], [4, 3], [4, 3], [4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_4_0 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T16_4
  T2 := Q2.T16_4_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_4_1 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T16_4
  T2 := Q2.T16_4_2
  h1 := (1,0,3,2,3)
  h2 := (1,0,3,2,3)
  D := [[1, 3], [1, 3], [1, 3], [1, 3], [1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_4_2 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T16_4
  T2 := Q2.T16_4_2
  h1 := (2,0,1,4,3)
  h2 := (2,0,1,4,3)
  D := [[2, 1], [2, 1], [2, 1], [2, 1], [2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_4_3 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T16_4
  T2 := Q2.T16_4_2
  h1 := (3,0,4,1,0)
  h2 := (3,0,4,1,0)
  D := [[3, 4], [3, 4], [3, 4], [3, 4], [3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_4_4 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T16_4
  T2 := Q2.T16_4_2
  h1 := (4,0,2,3,4)
  h2 := (4,0,2,3,4)
  D := [[4, 2], [4, 2], [4, 2], [4, 2], [4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_5_0 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T16_5
  T2 := Q2.T16_5_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_5_1 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T16_5
  T2 := Q2.T16_5_2
  h1 := (1,0,1,4,4)
  h2 := (1,0,1,4,4)
  D := [[1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_5_2 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T16_5
  T2 := Q2.T16_5_2
  h1 := (2,0,2,3,2)
  h2 := (2,0,2,3,2)
  D := [[2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_5_3 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T16_5
  T2 := Q2.T16_5_2
  h1 := (3,0,3,2,4)
  h2 := (3,0,3,2,4)
  D := [[3, 3], [3, 3], [3, 3], [3, 3], [3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_5_4 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T16_5
  T2 := Q2.T16_5_2
  h1 := (4,0,4,1,0)
  h2 := (4,0,4,1,0)
  D := [[4, 4], [4, 4], [4, 4], [4, 4], [4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_9_0 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨9, by decide⟩
  m := 25
  T1 := T16_9
  T2 := Q2.T16_9_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_9_1 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨9, by decide⟩
  m := 25
  T1 := T16_9
  T2 := Q2.T16_9_2
  h1 := (0,0,1,0,4)
  h2 := (0,0,1,0,4)
  D := [[0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_9_2 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨9, by decide⟩
  m := 25
  T1 := T16_9
  T2 := Q2.T16_9_2
  h1 := (0,0,2,0,3)
  h2 := (0,0,2,0,3)
  D := [[0, 2], [0, 2], [0, 2], [0, 2], [0, 2], [0, 2], [0, 2], [0, 2], [0, 2], [0, 2], [0, 2], [0, 2], [0, 2], [0, 2], [0, 2], [0, 2], [0, 2], [0, 2], [0, 2], [0, 2], [0, 2], [0, 2], [0, 2], [0, 2], [0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_9_3 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨9, by decide⟩
  m := 25
  T1 := T16_9
  T2 := Q2.T16_9_2
  h1 := (0,0,3,0,2)
  h2 := (0,0,3,0,2)
  D := [[0, 3], [0, 3], [0, 3], [0, 3], [0, 3], [0, 3], [0, 3], [0, 3], [0, 3], [0, 3], [0, 3], [0, 3], [0, 3], [0, 3], [0, 3], [0, 3], [0, 3], [0, 3], [0, 3], [0, 3], [0, 3], [0, 3], [0, 3], [0, 3], [0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_9_4 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨9, by decide⟩
  m := 25
  T1 := T16_9
  T2 := Q2.T16_9_2
  h1 := (0,0,4,0,1)
  h2 := (0,0,4,0,1)
  D := [[0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4], [0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_11_0 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨11, by decide⟩
  m := 5
  T1 := T16_11
  T2 := Q2.T16_11_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_11_1 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨11, by decide⟩
  m := 5
  T1 := T16_11
  T2 := Q2.T16_11_2
  h1 := (1,0,0,4,3)
  h2 := (1,0,0,4,3)
  D := [[1, 0], [1, 0], [1, 0], [1, 0], [1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_11_2 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨11, by decide⟩
  m := 5
  T1 := T16_11
  T2 := Q2.T16_11_2
  h1 := (2,0,0,3,0)
  h2 := (2,0,0,3,0)
  D := [[2, 0], [2, 0], [2, 0], [2, 0], [2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_11_3 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨11, by decide⟩
  m := 5
  T1 := T16_11
  T2 := Q2.T16_11_2
  h1 := (3,0,0,2,1)
  h2 := (3,0,0,2,1)
  D := [[3, 0], [3, 0], [3, 0], [3, 0], [3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_11_4 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨11, by decide⟩
  m := 5
  T1 := T16_11
  T2 := Q2.T16_11_2
  h1 := (4,0,0,1,1)
  h2 := (4,0,0,1,1)
  D := [[4, 0], [4, 0], [4, 0], [4, 0], [4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_16_0 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨16, by decide⟩
  m := 5
  T1 := T16_16
  T2 := Q2.T16_16_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_16_1 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨16, by decide⟩
  m := 5
  T1 := T16_16
  T2 := Q2.T16_16_2
  h1 := (0,0,1,0,3)
  h2 := (0,0,1,0,3)
  D := [[0, 1], [0, 1], [0, 1], [0, 1], [0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_16_2 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨16, by decide⟩
  m := 5
  T1 := T16_16
  T2 := Q2.T16_16_2
  h1 := (0,0,2,0,1)
  h2 := (0,0,2,0,1)
  D := [[0, 2], [0, 2], [0, 2], [0, 2], [0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_16_16_3 : ColCert where
  rK := ⟨16, by decide⟩
  rH := ⟨16, by decide⟩
  m := 5
  T1 := T16_16
  T2 := Q2.T16_16_2
  h1 := (0,0,3,0,4)
  h2 := (0,0,3,0,4)
  D := [[0, 3], [0, 3], [0, 3], [0, 3], [0, 3]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
