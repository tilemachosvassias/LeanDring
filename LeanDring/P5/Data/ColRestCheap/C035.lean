/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C027
import LeanDring.P5.Data.EntryK.C028

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 34: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_118_112_4 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T118_112
  T2 := Q2.T118_112_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_112_5 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T118_112
  T2 := Q2.T118_112_2
  h1 := (1,2,0,3,3)
  h2 := (1,2,0,3,3)
  D := [[1, 0, 3, 2], [1, 0, 2, 3], [1, 0, 1, 4], [1, 0, 0, 0], [1, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_112_10 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T118_112
  T2 := Q2.T118_112_2
  h1 := (2,4,0,3,4)
  h2 := (2,4,0,3,4)
  D := [[2, 0, 1, 1], [2, 0, 4, 4], [2, 0, 2, 2], [2, 0, 0, 0], [2, 0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_112_15 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T118_112
  T2 := Q2.T118_112_2
  h1 := (3,1,0,0,1)
  h2 := (3,1,0,0,2)
  D := [[3, 0, 4, 2], [3, 0, 1, 3], [3, 0, 3, 4], [3, 0, 0, 0], [3, 0, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_112_20 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T118_112
  T2 := Q2.T118_112_2
  h1 := (4,3,0,4,4)
  h2 := (4,3,0,4,0)
  D := [[4, 0, 2, 0], [4, 0, 3, 0], [4, 0, 4, 0], [4, 0, 0, 0], [4, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_0 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_1 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_2 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_3 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_4 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_5 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 1, 0, 2], [0, 1, 0, 3], [0, 1, 0, 4], [0, 1, 0, 0], [0, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_6 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 1, 1, 2], [0, 1, 1, 3], [0, 1, 1, 4], [0, 1, 1, 0], [0, 1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_7 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 1, 2, 2], [0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 2, 0], [0, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_8 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 1, 3, 2], [0, 1, 3, 3], [0, 1, 3, 4], [0, 1, 3, 0], [0, 1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_9 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 1, 4, 2], [0, 1, 4, 3], [0, 1, 4, 4], [0, 1, 4, 0], [0, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_10 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 2, 0, 4], [0, 2, 0, 1], [0, 2, 0, 3], [0, 2, 0, 0], [0, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_11 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 2, 1, 4], [0, 2, 1, 1], [0, 2, 1, 3], [0, 2, 1, 0], [0, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_12 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 2, 2, 4], [0, 2, 2, 1], [0, 2, 2, 3], [0, 2, 2, 0], [0, 2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_13 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 2, 3, 4], [0, 2, 3, 1], [0, 2, 3, 3], [0, 2, 3, 0], [0, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_14 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 2, 4, 4], [0, 2, 4, 1], [0, 2, 4, 3], [0, 2, 4, 0], [0, 2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_15 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 3, 0, 1], [0, 3, 0, 4], [0, 3, 0, 2], [0, 3, 0, 0], [0, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_16 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 3, 1, 1], [0, 3, 1, 4], [0, 3, 1, 2], [0, 3, 1, 0], [0, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_17 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 3, 2, 1], [0, 3, 2, 4], [0, 3, 2, 2], [0, 3, 2, 0], [0, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_18 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 3, 3, 1], [0, 3, 3, 4], [0, 3, 3, 2], [0, 3, 3, 0], [0, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_19 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 3, 4, 1], [0, 3, 4, 4], [0, 3, 4, 2], [0, 3, 4, 0], [0, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_20 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 4, 0, 3], [0, 4, 0, 2], [0, 4, 0, 1], [0, 4, 0, 0], [0, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_21 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 4, 1, 3], [0, 4, 1, 2], [0, 4, 1, 1], [0, 4, 1, 0], [0, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_22 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (0,0,4,2,0)
  h2 := (0,0,4,2,0)
  D := [[0, 4, 2, 3], [0, 4, 2, 2], [0, 4, 2, 1], [0, 4, 2, 0], [0, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_23 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 4, 3, 3], [0, 4, 3, 2], [0, 4, 3, 1], [0, 4, 3, 0], [0, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_24 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 4, 4, 3], [0, 4, 4, 2], [0, 4, 4, 1], [0, 4, 4, 0], [0, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_25 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (1,2,0,3,3)
  h2 := (1,2,0,3,3)
  D := [[1, 0, 3, 2], [1, 0, 2, 3], [1, 0, 1, 4], [1, 0, 0, 0], [1, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_30 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (1,2,1,3,3)
  h2 := (1,2,1,3,3)
  D := [[1, 1, 3, 2], [1, 1, 2, 4], [1, 1, 1, 1], [1, 1, 0, 3], [1, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_35 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (1,2,2,3,3)
  h2 := (1,2,2,3,3)
  D := [[1, 2, 3, 2], [1, 2, 2, 0], [1, 2, 1, 3], [1, 2, 0, 1], [1, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_40 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (1,2,3,3,3)
  h2 := (1,2,3,3,3)
  D := [[1, 3, 3, 2], [1, 3, 2, 1], [1, 3, 1, 0], [1, 3, 0, 4], [1, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_45 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (1,2,4,3,3)
  h2 := (1,2,4,3,3)
  D := [[1, 4, 3, 2], [1, 4, 2, 2], [1, 4, 1, 2], [1, 4, 0, 2], [1, 4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_50 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (2,4,0,3,4)
  h2 := (2,4,0,3,4)
  D := [[2, 0, 1, 1], [2, 0, 4, 4], [2, 0, 2, 2], [2, 0, 0, 0], [2, 0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_55 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (2,4,1,3,4)
  h2 := (2,4,1,3,4)
  D := [[2, 1, 1, 4], [2, 1, 4, 3], [2, 1, 2, 2], [2, 1, 0, 1], [2, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_60 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (2,4,2,3,4)
  h2 := (2,4,2,3,4)
  D := [[2, 2, 1, 2], [2, 2, 4, 2], [2, 2, 2, 2], [2, 2, 0, 2], [2, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_65 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (2,4,3,3,4)
  h2 := (2,4,3,3,4)
  D := [[2, 3, 1, 0], [2, 3, 4, 1], [2, 3, 2, 2], [2, 3, 0, 3], [2, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_70 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (2,4,4,3,4)
  h2 := (2,4,4,3,4)
  D := [[2, 4, 1, 3], [2, 4, 4, 0], [2, 4, 2, 2], [2, 4, 0, 4], [2, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_75 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (3,1,0,0,1)
  h2 := (3,1,0,0,2)
  D := [[3, 0, 4, 2], [3, 0, 1, 3], [3, 0, 3, 4], [3, 0, 0, 0], [3, 0, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_80 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (3,1,1,0,1)
  h2 := (3,1,1,0,2)
  D := [[3, 1, 4, 3], [3, 1, 1, 0], [3, 1, 3, 2], [3, 1, 0, 4], [3, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_85 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (3,1,2,0,1)
  h2 := (3,1,2,0,2)
  D := [[3, 2, 4, 4], [3, 2, 1, 2], [3, 2, 3, 0], [3, 2, 0, 3], [3, 2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_90 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (3,1,3,0,1)
  h2 := (3,1,3,0,2)
  D := [[3, 3, 4, 0], [3, 3, 1, 4], [3, 3, 3, 3], [3, 3, 0, 2], [3, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_95 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (3,1,4,0,1)
  h2 := (3,1,4,0,2)
  D := [[3, 4, 4, 1], [3, 4, 1, 1], [3, 4, 3, 1], [3, 4, 0, 1], [3, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_100 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (4,3,0,4,4)
  h2 := (4,3,0,4,0)
  D := [[4, 0, 2, 0], [4, 0, 3, 0], [4, 0, 4, 0], [4, 0, 0, 0], [4, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_105 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (4,3,1,4,4)
  h2 := (4,3,1,4,0)
  D := [[4, 1, 2, 4], [4, 1, 3, 0], [4, 1, 4, 1], [4, 1, 0, 2], [4, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_110 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (4,3,2,4,4)
  h2 := (4,3,2,4,0)
  D := [[4, 2, 2, 3], [4, 2, 3, 0], [4, 2, 4, 2], [4, 2, 0, 4], [4, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_115 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (4,3,3,4,4)
  h2 := (4,3,3,4,0)
  D := [[4, 3, 2, 2], [4, 3, 3, 0], [4, 3, 4, 3], [4, 3, 0, 1], [4, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_118_120 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨118, by decide⟩
  m := 5
  T1 := T118_118
  T2 := Q2.T118_118_2
  h1 := (4,3,4,4,4)
  h2 := (4,3,4,4,0)
  D := [[4, 4, 2, 1], [4, 4, 3, 0], [4, 4, 4, 4], [4, 4, 0, 3], [4, 4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_0_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨0, by decide⟩
  m := 5
  T1 := T119_0
  T2 := Q2.T119_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_1_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨1, by decide⟩
  m := 5
  T1 := T119_1
  T2 := Q2.T119_1_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_1_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨1, by decide⟩
  m := 5
  T1 := T119_1
  T2 := Q2.T119_1_2
  h1 := (0,0,1,4,4)
  h2 := (0,0,1,4,4)
  D := [[0, 1, 4, 2], [0, 1, 4, 3], [0, 1, 4, 4], [0, 1, 4, 0], [0, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_1_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨1, by decide⟩
  m := 5
  T1 := T119_1
  T2 := Q2.T119_1_2
  h1 := (0,0,2,3,3)
  h2 := (0,0,2,3,3)
  D := [[0, 2, 3, 4], [0, 2, 3, 1], [0, 2, 3, 3], [0, 2, 3, 0], [0, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_1_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨1, by decide⟩
  m := 5
  T1 := T119_1
  T2 := Q2.T119_1_2
  h1 := (0,0,3,2,2)
  h2 := (0,0,3,2,2)
  D := [[0, 3, 2, 1], [0, 3, 2, 4], [0, 3, 2, 2], [0, 3, 2, 0], [0, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_1_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨1, by decide⟩
  m := 5
  T1 := T119_1
  T2 := Q2.T119_1_2
  h1 := (0,0,4,1,1)
  h2 := (0,0,4,1,1)
  D := [[0, 4, 1, 3], [0, 4, 1, 2], [0, 4, 1, 1], [0, 4, 1, 0], [0, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_6_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨6, by decide⟩
  m := 5
  T1 := T119_6
  T2 := Q2.T119_6_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_6_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨6, by decide⟩
  m := 5
  T1 := T119_6
  T2 := Q2.T119_6_2
  h1 := (0,0,1,2,4)
  h2 := (0,0,1,2,4)
  D := [[0, 1, 2, 2], [0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 2, 0], [0, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_6_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨6, by decide⟩
  m := 5
  T1 := T119_6
  T2 := Q2.T119_6_2
  h1 := (0,0,2,4,3)
  h2 := (0,0,2,4,3)
  D := [[0, 2, 4, 4], [0, 2, 4, 1], [0, 2, 4, 3], [0, 2, 4, 0], [0, 2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_6_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨6, by decide⟩
  m := 5
  T1 := T119_6
  T2 := Q2.T119_6_2
  h1 := (0,0,3,1,2)
  h2 := (0,0,3,1,2)
  D := [[0, 3, 1, 1], [0, 3, 1, 4], [0, 3, 1, 2], [0, 3, 1, 0], [0, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
