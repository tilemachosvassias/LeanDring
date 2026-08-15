/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C030
import LeanDring.P5.Data.EntryK.C031

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 51: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_123_81_3 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T123_81
  T2 := Q2.T123_81_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_81_4 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T123_81
  T2 := Q2.T123_81_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_91_0 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T123_91
  T2 := Q2.T123_91_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_91_1 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T123_91
  T2 := Q2.T123_91_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_91_2 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T123_91
  T2 := Q2.T123_91_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_91_3 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T123_91
  T2 := Q2.T123_91_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_91_4 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T123_91
  T2 := Q2.T123_91_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_91_20 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T123_91
  T2 := Q2.T123_91_2
  h1 := (4,1,4,0,3)
  h2 := (4,1,4,0,1)
  D := [[4, 1, 4, 2], [4, 1, 4, 1], [4, 1, 4, 0], [4, 1, 4, 4], [4, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_99_0 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T123_99
  T2 := Q2.T123_99_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_99_1 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T123_99
  T2 := Q2.T123_99_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_99_2 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T123_99
  T2 := Q2.T123_99_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_99_3 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T123_99
  T2 := Q2.T123_99_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_99_4 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T123_99
  T2 := Q2.T123_99_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_100_0 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T123_100
  T2 := Q2.T123_100_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_100_1 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T123_100
  T2 := Q2.T123_100_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_100_2 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T123_100
  T2 := Q2.T123_100_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_100_3 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T123_100
  T2 := Q2.T123_100_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_100_4 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T123_100
  T2 := Q2.T123_100_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_100_5 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T123_100
  T2 := Q2.T123_100_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_100_10 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T123_100
  T2 := Q2.T123_100_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_100_15 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T123_100
  T2 := Q2.T123_100_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_100_20 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T123_100
  T2 := Q2.T123_100_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_108_0 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T123_108
  T2 := Q2.T123_108_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_108_1 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T123_108
  T2 := Q2.T123_108_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_108_2 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T123_108
  T2 := Q2.T123_108_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_108_3 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T123_108
  T2 := Q2.T123_108_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_108_4 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T123_108
  T2 := Q2.T123_108_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_112_0 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T123_112
  T2 := Q2.T123_112_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_112_1 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T123_112
  T2 := Q2.T123_112_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_112_2 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T123_112
  T2 := Q2.T123_112_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_112_3 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T123_112
  T2 := Q2.T123_112_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_112_4 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T123_112
  T2 := Q2.T123_112_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_112_5 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T123_112
  T2 := Q2.T123_112_2
  h1 := (1,2,0,3,3)
  h2 := (1,2,0,3,3)
  D := [[1, 2, 3, 1], [1, 2, 3, 4], [1, 2, 3, 2], [1, 2, 3, 0], [1, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_112_10 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T123_112
  T2 := Q2.T123_112_2
  h1 := (2,4,0,3,4)
  h2 := (2,4,0,3,4)
  D := [[2, 4, 4, 4], [2, 4, 4, 0], [2, 4, 4, 1], [2, 4, 4, 2], [2, 4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_123_0 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨123, by decide⟩
  m := 5
  T1 := T123_123
  T2 := Q2.T123_123_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_123_1 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨123, by decide⟩
  m := 5
  T1 := T123_123
  T2 := Q2.T123_123_2
  h1 := (0,1,3,0,2)
  h2 := (0,1,3,0,3)
  D := [[0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_123_2 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨123, by decide⟩
  m := 5
  T1 := T123_123
  T2 := Q2.T123_123_2
  h1 := (0,2,1,0,2)
  h2 := (0,2,1,0,4)
  D := [[0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_123_3 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨123, by decide⟩
  m := 5
  T1 := T123_123
  T2 := Q2.T123_123_2
  h1 := (0,3,4,0,0)
  h2 := (0,3,4,0,3)
  D := [[0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_123_4 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨123, by decide⟩
  m := 5
  T1 := T123_123
  T2 := Q2.T123_123_2
  h1 := (0,4,2,0,1)
  h2 := (0,4,2,0,0)
  D := [[0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_123_5 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨123, by decide⟩
  m := 5
  T1 := T123_123
  T2 := Q2.T123_123_2
  h1 := (1,0,4,3,3)
  h2 := (1,0,4,3,1)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_123_6 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨123, by decide⟩
  m := 5
  T1 := T123_123
  T2 := Q2.T123_123_2
  h1 := (1,1,2,3,4)
  h2 := (1,1,2,3,3)
  D := [[1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1], [1, 1, 4, 0], [1, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_123_7 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨123, by decide⟩
  m := 5
  T1 := T123_123
  T2 := Q2.T123_123_2
  h1 := (1,2,0,3,3)
  h2 := (1,2,0,3,3)
  D := [[1, 2, 3, 1], [1, 2, 3, 4], [1, 2, 3, 2], [1, 2, 3, 0], [1, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_123_8 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨123, by decide⟩
  m := 5
  T1 := T123_123
  T2 := Q2.T123_123_2
  h1 := (1,3,3,3,0)
  h2 := (1,3,3,3,1)
  D := [[1, 3, 2, 4], [1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0], [1, 3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_123_9 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨123, by decide⟩
  m := 5
  T1 := T123_123
  T2 := Q2.T123_123_2
  h1 := (1,4,1,3,0)
  h2 := (1,4,1,3,2)
  D := [[1, 4, 1, 2], [1, 4, 1, 3], [1, 4, 1, 4], [1, 4, 1, 0], [1, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_123_10 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨123, by decide⟩
  m := 5
  T1 := T123_123
  T2 := Q2.T123_123_2
  h1 := (2,0,3,1,4)
  h2 := (2,0,3,1,0)
  D := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_123_11 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨123, by decide⟩
  m := 5
  T1 := T123_123
  T2 := Q2.T123_123_2
  h1 := (2,1,1,1,4)
  h2 := (2,1,1,1,1)
  D := [[2, 1, 3, 4], [2, 1, 3, 3], [2, 1, 3, 2], [2, 1, 3, 1], [2, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_123_12 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨123, by decide⟩
  m := 5
  T1 := T123_123
  T2 := Q2.T123_123_2
  h1 := (2,2,4,1,2)
  h2 := (2,2,4,1,0)
  D := [[2, 2, 1, 3], [2, 2, 1, 1], [2, 2, 1, 4], [2, 2, 1, 2], [2, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_123_13 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨123, by decide⟩
  m := 5
  T1 := T123_123
  T2 := Q2.T123_123_2
  h1 := (2,3,2,1,3)
  h2 := (2,3,2,1,2)
  D := [[2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1], [2, 3, 4, 3], [2, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_123_14 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨123, by decide⟩
  m := 5
  T1 := T123_123
  T2 := Q2.T123_123_2
  h1 := (2,4,0,1,2)
  h2 := (2,4,0,1,2)
  D := [[2, 4, 2, 1], [2, 4, 2, 2], [2, 4, 2, 3], [2, 4, 2, 4], [2, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_123_15 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨123, by decide⟩
  m := 5
  T1 := T123_123
  T2 := Q2.T123_123_2
  h1 := (3,0,2,4,3)
  h2 := (3,0,2,4,2)
  D := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_123_16 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨123, by decide⟩
  m := 5
  T1 := T123_123
  T2 := Q2.T123_123_2
  h1 := (3,1,0,4,2)
  h2 := (3,1,0,4,2)
  D := [[3, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_123_17 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨123, by decide⟩
  m := 5
  T1 := T123_123
  T2 := Q2.T123_123_2
  h1 := (3,2,3,4,4)
  h2 := (3,2,3,4,0)
  D := [[3, 2, 4, 2], [3, 2, 4, 0], [3, 2, 4, 3], [3, 2, 4, 1], [3, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_123_18 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨123, by decide⟩
  m := 5
  T1 := T123_123
  T2 := Q2.T123_123_2
  h1 := (3,3,1,4,4)
  h2 := (3,3,1,4,1)
  D := [[3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_123_19 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨123, by decide⟩
  m := 5
  T1 := T123_123
  T2 := Q2.T123_123_2
  h1 := (3,4,4,4,2)
  h2 := (3,4,4,4,0)
  D := [[3, 4, 3, 4], [3, 4, 3, 0], [3, 4, 3, 1], [3, 4, 3, 2], [3, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_123_20 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨123, by decide⟩
  m := 5
  T1 := T123_123
  T2 := Q2.T123_123_2
  h1 := (4,0,1,2,0)
  h2 := (4,0,1,2,2)
  D := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_123_21 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨123, by decide⟩
  m := 5
  T1 := T123_123
  T2 := Q2.T123_123_2
  h1 := (4,1,4,2,3)
  h2 := (4,1,4,2,1)
  D := [[4, 1, 1, 4], [4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_123_22 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨123, by decide⟩
  m := 5
  T1 := T123_123
  T2 := Q2.T123_123_2
  h1 := (4,2,2,2,4)
  h2 := (4,2,2,2,3)
  D := [[4, 2, 2, 3], [4, 2, 2, 1], [4, 2, 2, 4], [4, 2, 2, 2], [4, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_123_23 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨123, by decide⟩
  m := 5
  T1 := T123_123
  T2 := Q2.T123_123_2
  h1 := (4,3,0,2,3)
  h2 := (4,3,0,2,3)
  D := [[4, 3, 3, 2], [4, 3, 3, 4], [4, 3, 3, 1], [4, 3, 3, 3], [4, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_123_24 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨123, by decide⟩
  m := 5
  T1 := T123_123
  T2 := Q2.T123_123_2
  h1 := (4,4,3,2,0)
  h2 := (4,4,3,2,1)
  D := [[4, 4, 4, 1], [4, 4, 4, 2], [4, 4, 4, 3], [4, 4, 4, 4], [4, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_0_0 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨0, by decide⟩
  m := 5
  T1 := T124_0
  T2 := Q2.T124_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
