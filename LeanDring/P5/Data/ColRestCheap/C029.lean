/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C026

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 28: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_117_101_2 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T117_101
  T2 := Q2.T117_101_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_101_3 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T117_101
  T2 := Q2.T117_101_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_101_4 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T117_101
  T2 := Q2.T117_101_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_101_5 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T117_101
  T2 := Q2.T117_101_2
  h1 := (1,4,2,4,3)
  h2 := (1,4,2,4,3)
  D := [[1, 2, 1, 2], [1, 2, 0, 0], [1, 2, 4, 3], [1, 2, 3, 1], [1, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_101_10 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T117_101
  T2 := Q2.T117_101_2
  h1 := (2,3,4,2,4)
  h2 := (2,3,4,2,0)
  D := [[2, 4, 2, 0], [2, 4, 0, 2], [2, 4, 3, 4], [2, 4, 1, 1], [2, 4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_101_15 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T117_101
  T2 := Q2.T117_101_2
  h1 := (3,2,1,4,1)
  h2 := (3,2,1,4,3)
  D := [[3, 1, 3, 4], [3, 1, 0, 1], [3, 1, 2, 3], [3, 1, 4, 0], [3, 1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_101_20 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T117_101
  T2 := Q2.T117_101_2
  h1 := (4,1,3,0,3)
  h2 := (4,1,3,0,1)
  D := [[4, 3, 4, 4], [4, 3, 0, 2], [4, 3, 1, 0], [4, 3, 2, 3], [4, 3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_106_0 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T117_106
  T2 := Q2.T117_106_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_106_1 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T117_106
  T2 := Q2.T117_106_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_106_2 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T117_106
  T2 := Q2.T117_106_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_106_3 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T117_106
  T2 := Q2.T117_106_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_106_4 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T117_106
  T2 := Q2.T117_106_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_106_5 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T117_106
  T2 := Q2.T117_106_2
  h1 := (1,4,4,4,1)
  h2 := (1,4,4,4,1)
  D := [[1, 4, 1, 0], [1, 4, 0, 0], [1, 4, 4, 0], [1, 4, 3, 0], [1, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_106_10 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T117_106
  T2 := Q2.T117_106_2
  h1 := (2,3,3,2,3)
  h2 := (2,3,3,2,4)
  D := [[2, 3, 2, 3], [2, 3, 0, 4], [2, 3, 3, 0], [2, 3, 1, 1], [2, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_106_15 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T117_106
  T2 := Q2.T117_106_2
  h1 := (3,2,2,4,4)
  h2 := (3,2,2,4,1)
  D := [[3, 2, 3, 4], [3, 2, 0, 2], [3, 2, 2, 0], [3, 2, 4, 3], [3, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_106_20 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T117_106
  T2 := Q2.T117_106_2
  h1 := (4,1,1,0,3)
  h2 := (4,1,1,0,1)
  D := [[4, 1, 4, 3], [4, 1, 0, 4], [4, 1, 1, 0], [4, 1, 2, 1], [4, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_111_0 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T117_111
  T2 := Q2.T117_111_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_111_1 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T117_111
  T2 := Q2.T117_111_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_111_2 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T117_111
  T2 := Q2.T117_111_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_111_3 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T117_111
  T2 := Q2.T117_111_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_111_4 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T117_111
  T2 := Q2.T117_111_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_111_5 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T117_111
  T2 := Q2.T117_111_2
  h1 := (1,4,0,4,0)
  h2 := (1,4,0,4,0)
  D := [[1, 0, 1, 4], [1, 0, 0, 0], [1, 0, 4, 1], [1, 0, 3, 2], [1, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_111_10 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T117_111
  T2 := Q2.T117_111_2
  h1 := (2,3,0,2,0)
  h2 := (2,3,0,2,1)
  D := [[2, 0, 2, 2], [2, 0, 0, 0], [2, 0, 3, 3], [2, 0, 1, 1], [2, 0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_111_15 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T117_111
  T2 := Q2.T117_111_2
  h1 := (3,2,0,4,3)
  h2 := (3,2,0,4,0)
  D := [[3, 0, 3, 4], [3, 0, 0, 0], [3, 0, 2, 1], [3, 0, 4, 2], [3, 0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_111_20 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T117_111
  T2 := Q2.T117_111_2
  h1 := (4,1,0,0,3)
  h2 := (4,1,0,0,1)
  D := [[4, 0, 4, 0], [4, 0, 0, 0], [4, 0, 1, 0], [4, 0, 2, 0], [4, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_0 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_1 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_2 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_3 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_4 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_5 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 1, 0, 4], [0, 1, 0, 0], [0, 1, 0, 1], [0, 1, 0, 2], [0, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_6 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 1, 1, 4], [0, 1, 1, 0], [0, 1, 1, 1], [0, 1, 1, 2], [0, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_7 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 1, 2, 4], [0, 1, 2, 0], [0, 1, 2, 1], [0, 1, 2, 2], [0, 1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_8 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 1, 3, 4], [0, 1, 3, 0], [0, 1, 3, 1], [0, 1, 3, 2], [0, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_9 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 1, 4, 4], [0, 1, 4, 0], [0, 1, 4, 1], [0, 1, 4, 2], [0, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_10 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 2, 0, 3], [0, 2, 0, 0], [0, 2, 0, 2], [0, 2, 0, 4], [0, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_11 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 2, 1, 3], [0, 2, 1, 0], [0, 2, 1, 2], [0, 2, 1, 4], [0, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_12 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 2, 2, 3], [0, 2, 2, 0], [0, 2, 2, 2], [0, 2, 2, 4], [0, 2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_13 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 2, 3, 3], [0, 2, 3, 0], [0, 2, 3, 2], [0, 2, 3, 4], [0, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_14 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 2, 4, 3], [0, 2, 4, 0], [0, 2, 4, 2], [0, 2, 4, 4], [0, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_15 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 3, 0, 2], [0, 3, 0, 0], [0, 3, 0, 3], [0, 3, 0, 1], [0, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_16 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 3, 1, 2], [0, 3, 1, 0], [0, 3, 1, 3], [0, 3, 1, 1], [0, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_17 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 3, 2, 2], [0, 3, 2, 0], [0, 3, 2, 3], [0, 3, 2, 1], [0, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_18 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 3, 3, 2], [0, 3, 3, 0], [0, 3, 3, 3], [0, 3, 3, 1], [0, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_19 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 3, 4, 2], [0, 3, 4, 0], [0, 3, 4, 3], [0, 3, 4, 1], [0, 3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_20 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 4, 0, 1], [0, 4, 0, 0], [0, 4, 0, 4], [0, 4, 0, 3], [0, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_21 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 4, 1, 1], [0, 4, 1, 0], [0, 4, 1, 4], [0, 4, 1, 3], [0, 4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_22 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (0,0,4,2,0)
  h2 := (0,0,4,2,0)
  D := [[0, 4, 2, 1], [0, 4, 2, 0], [0, 4, 2, 4], [0, 4, 2, 3], [0, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_23 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 4, 3, 1], [0, 4, 3, 0], [0, 4, 3, 4], [0, 4, 3, 3], [0, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_24 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 4, 4, 1], [0, 4, 4, 0], [0, 4, 4, 4], [0, 4, 4, 3], [0, 4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_25 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (1,4,0,4,0)
  h2 := (1,4,0,4,0)
  D := [[1, 0, 1, 4], [1, 0, 0, 0], [1, 0, 4, 1], [1, 0, 3, 2], [1, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_30 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (1,4,1,4,0)
  h2 := (1,4,1,4,0)
  D := [[1, 1, 1, 4], [1, 1, 0, 1], [1, 1, 4, 3], [1, 1, 3, 0], [1, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_35 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (1,4,2,4,0)
  h2 := (1,4,2,4,0)
  D := [[1, 2, 1, 4], [1, 2, 0, 2], [1, 2, 4, 0], [1, 2, 3, 3], [1, 2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_40 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (1,4,3,4,0)
  h2 := (1,4,3,4,0)
  D := [[1, 3, 1, 4], [1, 3, 0, 3], [1, 3, 4, 2], [1, 3, 3, 1], [1, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_45 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (1,4,4,4,0)
  h2 := (1,4,4,4,0)
  D := [[1, 4, 1, 4], [1, 4, 0, 4], [1, 4, 4, 4], [1, 4, 3, 4], [1, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_50 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (2,3,0,2,0)
  h2 := (2,3,0,2,1)
  D := [[2, 0, 2, 2], [2, 0, 0, 0], [2, 0, 3, 3], [2, 0, 1, 1], [2, 0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_55 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (2,3,1,2,0)
  h2 := (2,3,1,2,1)
  D := [[2, 1, 2, 3], [2, 1, 0, 2], [2, 1, 3, 1], [2, 1, 1, 0], [2, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_60 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (2,3,2,2,0)
  h2 := (2,3,2,2,1)
  D := [[2, 2, 2, 4], [2, 2, 0, 4], [2, 2, 3, 4], [2, 2, 1, 4], [2, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_65 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (2,3,3,2,0)
  h2 := (2,3,3,2,1)
  D := [[2, 3, 2, 0], [2, 3, 0, 1], [2, 3, 3, 2], [2, 3, 1, 3], [2, 3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_70 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (2,3,4,2,0)
  h2 := (2,3,4,2,1)
  D := [[2, 4, 2, 1], [2, 4, 0, 3], [2, 4, 3, 0], [2, 4, 1, 2], [2, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
