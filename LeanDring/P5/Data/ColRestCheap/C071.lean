/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C035

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 70: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_132_100_4 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T132_100
  T2 := Q2.T132_100_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_100_5 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T132_100
  T2 := Q2.T132_100_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_100_10 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T132_100
  T2 := Q2.T132_100_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_100_15 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T132_100
  T2 := Q2.T132_100_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_100_20 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T132_100
  T2 := Q2.T132_100_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_109_0 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T132_109
  T2 := Q2.T132_109_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_109_1 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T132_109
  T2 := Q2.T132_109_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_109_2 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T132_109
  T2 := Q2.T132_109_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_109_3 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T132_109
  T2 := Q2.T132_109_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_109_4 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T132_109
  T2 := Q2.T132_109_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_111_0 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T132_111
  T2 := Q2.T132_111_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_111_1 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T132_111
  T2 := Q2.T132_111_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_111_2 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T132_111
  T2 := Q2.T132_111_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_111_3 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T132_111
  T2 := Q2.T132_111_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_111_4 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T132_111
  T2 := Q2.T132_111_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_111_5 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T132_111
  T2 := Q2.T132_111_2
  h1 := (1,4,0,4,0)
  h2 := (1,4,0,4,0)
  D := [[1, 4, 1, 2], [1, 4, 1, 3], [1, 4, 1, 4], [1, 4, 1, 0], [1, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_132_0 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨132, by decide⟩
  m := 5
  T1 := T132_132
  T2 := Q2.T132_132_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_132_1 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨132, by decide⟩
  m := 5
  T1 := T132_132
  T2 := Q2.T132_132_2
  h1 := (0,1,3,0,2)
  h2 := (0,1,3,0,3)
  D := [[0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_132_2 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨132, by decide⟩
  m := 5
  T1 := T132_132
  T2 := Q2.T132_132_2
  h1 := (0,2,1,0,2)
  h2 := (0,2,1,0,4)
  D := [[0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_132_3 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨132, by decide⟩
  m := 5
  T1 := T132_132
  T2 := Q2.T132_132_2
  h1 := (0,3,4,0,0)
  h2 := (0,3,4,0,3)
  D := [[0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_132_4 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨132, by decide⟩
  m := 5
  T1 := T132_132
  T2 := Q2.T132_132_2
  h1 := (0,4,2,0,1)
  h2 := (0,4,2,0,0)
  D := [[0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_132_5 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨132, by decide⟩
  m := 5
  T1 := T132_132
  T2 := Q2.T132_132_2
  h1 := (1,0,3,4,2)
  h2 := (1,0,3,4,3)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_132_6 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨132, by decide⟩
  m := 5
  T1 := T132_132
  T2 := Q2.T132_132_2
  h1 := (1,1,1,4,2)
  h2 := (1,1,1,4,4)
  D := [[1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1], [1, 1, 4, 0], [1, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_132_7 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨132, by decide⟩
  m := 5
  T1 := T132_132
  T2 := Q2.T132_132_2
  h1 := (1,2,4,4,0)
  h2 := (1,2,4,4,3)
  D := [[1, 2, 3, 1], [1, 2, 3, 4], [1, 2, 3, 2], [1, 2, 3, 0], [1, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_132_8 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨132, by decide⟩
  m := 5
  T1 := T132_132
  T2 := Q2.T132_132_2
  h1 := (1,3,2,4,1)
  h2 := (1,3,2,4,0)
  D := [[1, 3, 2, 4], [1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0], [1, 3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_132_9 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨132, by decide⟩
  m := 5
  T1 := T132_132
  T2 := Q2.T132_132_2
  h1 := (1,4,0,4,0)
  h2 := (1,4,0,4,0)
  D := [[1, 4, 1, 2], [1, 4, 1, 3], [1, 4, 1, 4], [1, 4, 1, 0], [1, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_132_10 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨132, by decide⟩
  m := 5
  T1 := T132_132
  T2 := Q2.T132_132_2
  h1 := (2,0,1,3,3)
  h2 := (2,0,1,3,0)
  D := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_132_11 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨132, by decide⟩
  m := 5
  T1 := T132_132
  T2 := Q2.T132_132_2
  h1 := (2,1,4,3,1)
  h2 := (2,1,4,3,4)
  D := [[2, 1, 3, 3], [2, 1, 3, 2], [2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_132_12 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨132, by decide⟩
  m := 5
  T1 := T132_132
  T2 := Q2.T132_132_2
  h1 := (2,2,2,3,2)
  h2 := (2,2,2,3,1)
  D := [[2, 2, 1, 1], [2, 2, 1, 4], [2, 2, 1, 2], [2, 2, 1, 0], [2, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_132_13 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨132, by decide⟩
  m := 5
  T1 := T132_132
  T2 := Q2.T132_132_2
  h1 := (2,3,0,3,1)
  h2 := (2,3,0,3,1)
  D := [[2, 3, 4, 4], [2, 3, 4, 1], [2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_132_14 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨132, by decide⟩
  m := 5
  T1 := T132_132
  T2 := Q2.T132_132_2
  h1 := (2,4,3,3,3)
  h2 := (2,4,3,3,4)
  D := [[2, 4, 2, 2], [2, 4, 2, 3], [2, 4, 2, 4], [2, 4, 2, 0], [2, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_132_15 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨132, by decide⟩
  m := 5
  T1 := T132_132
  T2 := Q2.T132_132_2
  h1 := (3,0,4,2,3)
  h2 := (3,0,4,2,1)
  D := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_132_16 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨132, by decide⟩
  m := 5
  T1 := T132_132
  T2 := Q2.T132_132_2
  h1 := (3,1,2,2,4)
  h2 := (3,1,2,2,3)
  D := [[3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2], [3, 1, 2, 1], [3, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_132_17 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨132, by decide⟩
  m := 5
  T1 := T132_132
  T2 := Q2.T132_132_2
  h1 := (3,2,0,2,3)
  h2 := (3,2,0,2,3)
  D := [[3, 2, 4, 3], [3, 2, 4, 1], [3, 2, 4, 4], [3, 2, 4, 2], [3, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_132_18 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨132, by decide⟩
  m := 5
  T1 := T132_132
  T2 := Q2.T132_132_2
  h1 := (3,3,3,2,0)
  h2 := (3,3,3,2,1)
  D := [[3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_132_19 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨132, by decide⟩
  m := 5
  T1 := T132_132
  T2 := Q2.T132_132_2
  h1 := (3,4,1,2,0)
  h2 := (3,4,1,2,2)
  D := [[3, 4, 3, 1], [3, 4, 3, 2], [3, 4, 3, 3], [3, 4, 3, 4], [3, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_132_20 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨132, by decide⟩
  m := 5
  T1 := T132_132
  T2 := Q2.T132_132_2
  h1 := (4,0,2,1,2)
  h2 := (4,0,2,1,1)
  D := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_132_21 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨132, by decide⟩
  m := 5
  T1 := T132_132
  T2 := Q2.T132_132_2
  h1 := (4,1,0,1,1)
  h2 := (4,1,0,1,1)
  D := [[4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4], [4, 1, 1, 3], [4, 1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_132_22 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨132, by decide⟩
  m := 5
  T1 := T132_132
  T2 := Q2.T132_132_2
  h1 := (4,2,3,1,3)
  h2 := (4,2,3,1,4)
  D := [[4, 2, 2, 2], [4, 2, 2, 0], [4, 2, 2, 3], [4, 2, 2, 1], [4, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_132_23 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨132, by decide⟩
  m := 5
  T1 := T132_132
  T2 := Q2.T132_132_2
  h1 := (4,3,1,1,3)
  h2 := (4,3,1,1,0)
  D := [[4, 3, 3, 3], [4, 3, 3, 0], [4, 3, 3, 2], [4, 3, 3, 4], [4, 3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_132_24 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨132, by decide⟩
  m := 5
  T1 := T132_132
  T2 := Q2.T132_132_2
  h1 := (4,4,4,1,1)
  h2 := (4,4,4,1,4)
  D := [[4, 4, 4, 4], [4, 4, 4, 0], [4, 4, 4, 1], [4, 4, 4, 2], [4, 4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_0_0 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨0, by decide⟩
  m := 5
  T1 := T133_0
  T2 := Q2.T133_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_4_0 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T133_4
  T2 := Q2.T133_4_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_4_1 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T133_4
  T2 := Q2.T133_4_2
  h1 := (1,0,3,2,3)
  h2 := (1,0,3,2,3)
  D := [[1, 0, 4, 3], [1, 0, 4, 3], [1, 0, 4, 3], [1, 0, 4, 3], [1, 0, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_4_2 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T133_4
  T2 := Q2.T133_4_2
  h1 := (2,0,1,4,3)
  h2 := (2,0,1,4,3)
  D := [[2, 0, 3, 2], [2, 0, 3, 2], [2, 0, 3, 2], [2, 0, 3, 2], [2, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_4_3 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T133_4
  T2 := Q2.T133_4_2
  h1 := (3,0,4,1,0)
  h2 := (3,0,4,1,0)
  D := [[3, 0, 2, 2], [3, 0, 2, 2], [3, 0, 2, 2], [3, 0, 2, 2], [3, 0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_4_4 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T133_4
  T2 := Q2.T133_4_2
  h1 := (4,0,2,3,4)
  h2 := (4,0,2,3,4)
  D := [[4, 0, 1, 3], [4, 0, 1, 3], [4, 0, 1, 3], [4, 0, 1, 3], [4, 0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_10_0 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T133_10
  T2 := Q2.T133_10_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_10_1 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T133_10
  T2 := Q2.T133_10_2
  h1 := (0,0,0,1,4)
  h2 := (0,0,0,1,4)
  D := [[0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_10_2 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T133_10
  T2 := Q2.T133_10_2
  h1 := (0,0,0,2,3)
  h2 := (0,0,0,2,3)
  D := [[0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_10_3 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T133_10
  T2 := Q2.T133_10_2
  h1 := (0,0,0,3,2)
  h2 := (0,0,0,3,2)
  D := [[0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_10_4 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T133_10
  T2 := Q2.T133_10_2
  h1 := (0,0,0,4,1)
  h2 := (0,0,0,4,1)
  D := [[0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_12_0 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T133_12
  T2 := Q2.T133_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_12_1 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T133_12
  T2 := Q2.T133_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_12_2 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T133_12
  T2 := Q2.T133_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_12_3 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T133_12
  T2 := Q2.T133_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_12_4 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T133_12
  T2 := Q2.T133_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_22_0 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T133_22
  T2 := Q2.T133_22_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_22_1 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T133_22
  T2 := Q2.T133_22_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_22_2 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T133_22
  T2 := Q2.T133_22_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
