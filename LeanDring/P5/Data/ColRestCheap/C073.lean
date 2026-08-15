/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C035
import LeanDring.P5.Data.EntryK.C036

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 72: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_133_98_1 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T133_98
  T2 := Q2.T133_98_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_98_2 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T133_98
  T2 := Q2.T133_98_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_98_3 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T133_98
  T2 := Q2.T133_98_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_98_4 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T133_98
  T2 := Q2.T133_98_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_98_5 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T133_98
  T2 := Q2.T133_98_2
  h1 := (1,3,1,1,3)
  h2 := (1,3,1,1,3)
  D := [[1, 3, 0, 2], [1, 3, 0, 4], [1, 3, 0, 1], [1, 3, 0, 3], [1, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_101_0 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T133_101
  T2 := Q2.T133_101_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_101_1 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T133_101
  T2 := Q2.T133_101_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_101_2 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T133_101
  T2 := Q2.T133_101_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_101_3 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T133_101
  T2 := Q2.T133_101_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_101_4 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T133_101
  T2 := Q2.T133_101_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_101_5 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T133_101
  T2 := Q2.T133_101_2
  h1 := (1,4,2,4,3)
  h2 := (1,4,2,4,3)
  D := [[1, 4, 2, 3], [1, 4, 2, 4], [1, 4, 2, 0], [1, 4, 2, 1], [1, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_105_0 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T133_105
  T2 := Q2.T133_105_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_105_1 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T133_105
  T2 := Q2.T133_105_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_105_2 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T133_105
  T2 := Q2.T133_105_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_105_3 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T133_105
  T2 := Q2.T133_105_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_105_4 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T133_105
  T2 := Q2.T133_105_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_105_5 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T133_105
  T2 := Q2.T133_105_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_105_10 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T133_105
  T2 := Q2.T133_105_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_105_15 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T133_105
  T2 := Q2.T133_105_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_105_20 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T133_105
  T2 := Q2.T133_105_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_105_25 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T133_105
  T2 := Q2.T133_105_2
  h1 := (0,1,1,0,0)
  h2 := (0,1,1,0,0)
  D := [[0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_105_50 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T133_105
  T2 := Q2.T133_105_2
  h1 := (0,2,2,0,1)
  h2 := (0,2,2,0,1)
  D := [[0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_105_75 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T133_105
  T2 := Q2.T133_105_2
  h1 := (0,3,3,0,3)
  h2 := (0,3,3,0,3)
  D := [[0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_105_100 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T133_105
  T2 := Q2.T133_105_2
  h1 := (0,4,4,0,1)
  h2 := (0,4,4,0,1)
  D := [[0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_112_0 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T133_112
  T2 := Q2.T133_112_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_112_1 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T133_112
  T2 := Q2.T133_112_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_112_2 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T133_112
  T2 := Q2.T133_112_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_112_3 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T133_112
  T2 := Q2.T133_112_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_112_4 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T133_112
  T2 := Q2.T133_112_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_112_5 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T133_112
  T2 := Q2.T133_112_2
  h1 := (1,2,0,3,3)
  h2 := (1,2,0,3,3)
  D := [[1, 2, 3, 0], [1, 2, 3, 3], [1, 2, 3, 1], [1, 2, 3, 4], [1, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_112_10 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T133_112
  T2 := Q2.T133_112_2
  h1 := (2,4,0,3,4)
  h2 := (2,4,0,3,4)
  D := [[2, 4, 4, 0], [2, 4, 4, 1], [2, 4, 4, 2], [2, 4, 4, 3], [2, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_133_0 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨133, by decide⟩
  m := 5
  T1 := T133_133
  T2 := Q2.T133_133_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_133_1 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨133, by decide⟩
  m := 5
  T1 := T133_133
  T2 := Q2.T133_133_2
  h1 := (0,1,1,0,0)
  h2 := (0,1,1,0,0)
  D := [[0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_133_2 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨133, by decide⟩
  m := 5
  T1 := T133_133
  T2 := Q2.T133_133_2
  h1 := (0,2,2,0,1)
  h2 := (0,2,2,0,1)
  D := [[0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_133_3 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨133, by decide⟩
  m := 5
  T1 := T133_133
  T2 := Q2.T133_133_2
  h1 := (0,3,3,0,3)
  h2 := (0,3,3,0,3)
  D := [[0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_133_4 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨133, by decide⟩
  m := 5
  T1 := T133_133
  T2 := Q2.T133_133_2
  h1 := (0,4,4,0,1)
  h2 := (0,4,4,0,1)
  D := [[0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_133_5 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨133, by decide⟩
  m := 5
  T1 := T133_133
  T2 := Q2.T133_133_2
  h1 := (1,0,3,3,1)
  h2 := (1,0,3,3,1)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_133_6 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨133, by decide⟩
  m := 5
  T1 := T133_133
  T2 := Q2.T133_133_2
  h1 := (1,1,4,3,4)
  h2 := (1,1,4,3,4)
  D := [[1, 1, 4, 0], [1, 1, 4, 4], [1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_133_7 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨133, by decide⟩
  m := 5
  T1 := T133_133
  T2 := Q2.T133_133_2
  h1 := (1,2,0,3,3)
  h2 := (1,2,0,3,3)
  D := [[1, 2, 3, 0], [1, 2, 3, 3], [1, 2, 3, 1], [1, 2, 3, 4], [1, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_133_8 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨133, by decide⟩
  m := 5
  T1 := T133_133
  T2 := Q2.T133_133_2
  h1 := (1,3,1,3,3)
  h2 := (1,3,1,3,3)
  D := [[1, 3, 2, 0], [1, 3, 2, 2], [1, 3, 2, 4], [1, 3, 2, 1], [1, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_133_9 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨133, by decide⟩
  m := 5
  T1 := T133_133
  T2 := Q2.T133_133_2
  h1 := (1,4,2,3,4)
  h2 := (1,4,2,3,4)
  D := [[1, 4, 1, 0], [1, 4, 1, 1], [1, 4, 1, 2], [1, 4, 1, 3], [1, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_133_10 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨133, by decide⟩
  m := 5
  T1 := T133_133
  T2 := Q2.T133_133_2
  h1 := (2,0,1,1,0)
  h2 := (2,0,1,1,0)
  D := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_133_11 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨133, by decide⟩
  m := 5
  T1 := T133_133
  T2 := Q2.T133_133_2
  h1 := (2,1,2,1,1)
  h2 := (2,1,2,1,1)
  D := [[2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3], [2, 1, 3, 2], [2, 1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_133_12 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨133, by decide⟩
  m := 5
  T1 := T133_133
  T2 := Q2.T133_133_2
  h1 := (2,2,3,1,3)
  h2 := (2,2,3,1,3)
  D := [[2, 2, 1, 0], [2, 2, 1, 3], [2, 2, 1, 1], [2, 2, 1, 4], [2, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_133_13 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨133, by decide⟩
  m := 5
  T1 := T133_133
  T2 := Q2.T133_133_2
  h1 := (2,3,4,1,1)
  h2 := (2,3,4,1,1)
  D := [[2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1], [2, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_133_14 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨133, by decide⟩
  m := 5
  T1 := T133_133
  T2 := Q2.T133_133_2
  h1 := (2,4,0,1,0)
  h2 := (2,4,0,1,0)
  D := [[2, 4, 2, 0], [2, 4, 2, 1], [2, 4, 2, 2], [2, 4, 2, 3], [2, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_133_15 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨133, by decide⟩
  m := 5
  T1 := T133_133
  T2 := Q2.T133_133_2
  h1 := (3,0,4,4,2)
  h2 := (3,0,4,4,2)
  D := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_133_16 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨133, by decide⟩
  m := 5
  T1 := T133_133
  T2 := Q2.T133_133_2
  h1 := (3,1,0,4,1)
  h2 := (3,1,0,4,1)
  D := [[3, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_133_17 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨133, by decide⟩
  m := 5
  T1 := T133_133
  T2 := Q2.T133_133_2
  h1 := (3,2,1,4,1)
  h2 := (3,2,1,4,1)
  D := [[3, 2, 4, 2], [3, 2, 4, 0], [3, 2, 4, 3], [3, 2, 4, 1], [3, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_133_18 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨133, by decide⟩
  m := 5
  T1 := T133_133
  T2 := Q2.T133_133_2
  h1 := (3,3,2,4,2)
  h2 := (3,3,2,4,2)
  D := [[3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_133_19 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨133, by decide⟩
  m := 5
  T1 := T133_133
  T2 := Q2.T133_133_2
  h1 := (3,4,3,4,4)
  h2 := (3,4,3,4,4)
  D := [[3, 4, 3, 4], [3, 4, 3, 0], [3, 4, 3, 1], [3, 4, 3, 2], [3, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_133_20 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨133, by decide⟩
  m := 5
  T1 := T133_133
  T2 := Q2.T133_133_2
  h1 := (4,0,2,2,2)
  h2 := (4,0,2,2,2)
  D := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_133_21 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨133, by decide⟩
  m := 5
  T1 := T133_133
  T2 := Q2.T133_133_2
  h1 := (4,1,3,2,4)
  h2 := (4,1,3,2,4)
  D := [[4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_133_22 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨133, by decide⟩
  m := 5
  T1 := T133_133
  T2 := Q2.T133_133_2
  h1 := (4,2,4,2,2)
  h2 := (4,2,4,2,2)
  D := [[4, 2, 2, 1], [4, 2, 2, 4], [4, 2, 2, 2], [4, 2, 2, 0], [4, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_133_23 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨133, by decide⟩
  m := 5
  T1 := T133_133
  T2 := Q2.T133_133_2
  h1 := (4,3,0,2,1)
  h2 := (4,3,0,2,1)
  D := [[4, 3, 3, 4], [4, 3, 3, 1], [4, 3, 3, 3], [4, 3, 3, 0], [4, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_133_24 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨133, by decide⟩
  m := 5
  T1 := T133_133
  T2 := Q2.T133_133_2
  h1 := (4,4,1,2,1)
  h2 := (4,4,1,2,1)
  D := [[4, 4, 4, 2], [4, 4, 4, 3], [4, 4, 4, 4], [4, 4, 4, 0], [4, 4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_0_0 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨0, by decide⟩
  m := 5
  T1 := T134_0
  T2 := Q2.T134_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_4_0 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T134_4
  T2 := Q2.T134_4_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_10_0 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T134_10
  T2 := Q2.T134_10_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_10_1 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T134_10
  T2 := Q2.T134_10_2
  h1 := (0,0,0,1,4)
  h2 := (0,0,0,1,4)
  D := [[0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
