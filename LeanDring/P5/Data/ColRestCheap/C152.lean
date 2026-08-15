/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C015

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 151: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_64_39_0 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T64_39
  T2 := Q2.T64_39_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_39_1 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T64_39
  T2 := Q2.T64_39_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_39_2 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T64_39
  T2 := Q2.T64_39_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_39_3 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T64_39
  T2 := Q2.T64_39_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_39_4 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T64_39
  T2 := Q2.T64_39_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_39_5 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T64_39
  T2 := Q2.T64_39_2
  h1 := (1,4,2,3,2)
  h2 := (1,4,2,3,2)
  D := [[1, 2, 0], [1, 2, 4], [1, 2, 3], [1, 2, 2], [1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_39_10 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T64_39
  T2 := Q2.T64_39_2
  h1 := (2,3,4,0,1)
  h2 := (2,3,4,0,2)
  D := [[2, 4, 0], [2, 4, 3], [2, 4, 1], [2, 4, 4], [2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_39_15 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T64_39
  T2 := Q2.T64_39_2
  h1 := (3,2,1,1,0)
  h2 := (3,2,1,1,2)
  D := [[3, 1, 0], [3, 1, 2], [3, 1, 4], [3, 1, 1], [3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_39_20 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T64_39
  T2 := Q2.T64_39_2
  h1 := (4,1,3,1,3)
  h2 := (4,1,3,1,1)
  D := [[4, 3, 0], [4, 3, 1], [4, 3, 2], [4, 3, 3], [4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_44_0 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T64_44
  T2 := Q2.T64_44_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_44_1 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T64_44
  T2 := Q2.T64_44_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_44_2 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T64_44
  T2 := Q2.T64_44_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_44_3 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T64_44
  T2 := Q2.T64_44_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_44_4 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T64_44
  T2 := Q2.T64_44_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_44_5 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T64_44
  T2 := Q2.T64_44_2
  h1 := (1,4,4,3,0)
  h2 := (1,4,4,3,0)
  D := [[1, 4, 3], [1, 4, 2], [1, 4, 1], [1, 4, 0], [1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_44_10 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T64_44
  T2 := Q2.T64_44_2
  h1 := (2,3,3,0,0)
  h2 := (2,3,3,0,1)
  D := [[2, 3, 1], [2, 3, 4], [2, 3, 2], [2, 3, 0], [2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_44_15 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T64_44
  T2 := Q2.T64_44_2
  h1 := (3,2,2,1,3)
  h2 := (3,2,2,1,0)
  D := [[3, 2, 4], [3, 2, 1], [3, 2, 3], [3, 2, 0], [3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_44_20 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T64_44
  T2 := Q2.T64_44_2
  h1 := (4,1,1,1,3)
  h2 := (4,1,1,1,1)
  D := [[4, 1, 2], [4, 1, 3], [4, 1, 4], [4, 1, 0], [4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_49_0 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T64_49
  T2 := Q2.T64_49_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_49_1 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T64_49
  T2 := Q2.T64_49_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_49_2 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T64_49
  T2 := Q2.T64_49_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_49_3 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T64_49
  T2 := Q2.T64_49_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_49_4 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T64_49
  T2 := Q2.T64_49_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_49_5 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T64_49
  T2 := Q2.T64_49_2
  h1 := (1,4,0,3,4)
  h2 := (1,4,0,3,4)
  D := [[1, 0, 4], [1, 0, 3], [1, 0, 2], [1, 0, 1], [1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_49_10 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T64_49
  T2 := Q2.T64_49_2
  h1 := (2,3,0,0,2)
  h2 := (2,3,0,0,3)
  D := [[2, 0, 3], [2, 0, 1], [2, 0, 4], [2, 0, 2], [2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_49_15 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T64_49
  T2 := Q2.T64_49_2
  h1 := (3,2,0,1,2)
  h2 := (3,2,0,1,4)
  D := [[3, 0, 2], [3, 0, 4], [3, 0, 1], [3, 0, 3], [3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_49_20 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T64_49
  T2 := Q2.T64_49_2
  h1 := (4,1,0,1,3)
  h2 := (4,1,0,1,1)
  D := [[4, 0, 1], [4, 0, 2], [4, 0, 3], [4, 0, 4], [4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_0 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_1 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_2 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_3 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_4 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_5 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_6 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (0,0,1,1,1)
  h2 := (0,0,1,1,1)
  D := [[0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_7 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (0,0,1,1,2)
  h2 := (0,0,1,1,2)
  D := [[0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_8 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (0,0,1,1,3)
  h2 := (0,0,1,1,3)
  D := [[0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_9 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (0,0,1,1,4)
  h2 := (0,0,1,1,4)
  D := [[0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_10 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_11 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (0,0,2,2,1)
  h2 := (0,0,2,2,1)
  D := [[0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_12 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (0,0,2,2,2)
  h2 := (0,0,2,2,2)
  D := [[0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_13 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (0,0,2,2,3)
  h2 := (0,0,2,2,3)
  D := [[0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_14 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (0,0,2,2,4)
  h2 := (0,0,2,2,4)
  D := [[0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_15 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_16 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (0,0,3,3,1)
  h2 := (0,0,3,3,1)
  D := [[0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_17 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (0,0,3,3,2)
  h2 := (0,0,3,3,2)
  D := [[0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_18 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (0,0,3,3,3)
  h2 := (0,0,3,3,3)
  D := [[0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_19 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (0,0,3,3,4)
  h2 := (0,0,3,3,4)
  D := [[0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_20 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_21 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (0,0,4,4,1)
  h2 := (0,0,4,4,1)
  D := [[0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_22 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (0,0,4,4,2)
  h2 := (0,0,4,4,2)
  D := [[0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_23 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (0,0,4,4,3)
  h2 := (0,0,4,4,3)
  D := [[0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_24 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (0,0,4,4,4)
  h2 := (0,0,4,4,4)
  D := [[0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_25 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (1,4,0,3,0)
  h2 := (1,4,0,3,0)
  D := [[1, 0, 0], [1, 0, 4], [1, 0, 3], [1, 0, 2], [1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_30 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (1,4,1,4,0)
  h2 := (1,4,1,4,0)
  D := [[1, 1, 0], [1, 1, 4], [1, 1, 3], [1, 1, 2], [1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_35 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (1,4,2,0,0)
  h2 := (1,4,2,0,0)
  D := [[1, 2, 0], [1, 2, 4], [1, 2, 3], [1, 2, 2], [1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_40 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (1,4,3,1,0)
  h2 := (1,4,3,1,0)
  D := [[1, 3, 0], [1, 3, 4], [1, 3, 3], [1, 3, 2], [1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_45 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (1,4,4,2,0)
  h2 := (1,4,4,2,0)
  D := [[1, 4, 0], [1, 4, 4], [1, 4, 3], [1, 4, 2], [1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_50 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (2,3,0,0,4)
  h2 := (2,3,0,0,0)
  D := [[2, 0, 0], [2, 0, 3], [2, 0, 1], [2, 0, 4], [2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_55 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (2,3,1,1,4)
  h2 := (2,3,1,1,0)
  D := [[2, 1, 0], [2, 1, 3], [2, 1, 1], [2, 1, 4], [2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_60 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (2,3,2,2,4)
  h2 := (2,3,2,2,0)
  D := [[2, 2, 0], [2, 2, 3], [2, 2, 1], [2, 2, 4], [2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
