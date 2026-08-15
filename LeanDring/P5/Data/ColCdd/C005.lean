/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C028

/-!
# Species-table cell data, stage 2 — column-data-divergent columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
cdd tier, chunk 4: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_119_31_5 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T119_31
  T2 := Q2.T119_31_2
  h1 := (1,3,2,0,4)
  h2 := (1,3,2,0,0)
  D1 := [[1, 2, 1, 1], [1, 2, 0, 4], [1, 2, 4, 2], [1, 2, 3, 0], [1, 2, 2, 3]]
  D2 := [[1, 2, 1, 2], [1, 2, 0, 0], [1, 2, 4, 3], [1, 2, 3, 1], [1, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_31_10 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T119_31
  T2 := Q2.T119_31_2
  h1 := (2,1,4,3,0)
  h2 := (2,1,4,3,3)
  D1 := [[2, 4, 2, 0], [2, 4, 0, 2], [2, 4, 3, 4], [2, 4, 1, 1], [2, 4, 4, 3]]
  D2 := [[2, 4, 2, 2], [2, 4, 0, 4], [2, 4, 3, 1], [2, 4, 1, 3], [2, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_31_15 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T119_31
  T2 := Q2.T119_31_2
  h1 := (3,4,1,4,4)
  h2 := (3,4,1,4,3)
  D1 := [[3, 1, 3, 2], [3, 1, 0, 4], [3, 1, 2, 1], [3, 1, 4, 3], [3, 1, 1, 0]]
  D2 := [[3, 1, 3, 0], [3, 1, 0, 2], [3, 1, 2, 4], [3, 1, 4, 1], [3, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_31_20 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T119_31
  T2 := Q2.T119_31_2
  h1 := (4,2,3,3,1)
  h2 := (4,2,3,3,2)
  D1 := [[4, 3, 4, 2], [4, 3, 0, 0], [4, 3, 1, 3], [4, 3, 2, 1], [4, 3, 3, 4]]
  D2 := [[4, 3, 4, 1], [4, 3, 0, 4], [4, 3, 1, 2], [4, 3, 2, 0], [4, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_36_5 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T119_36
  T2 := Q2.T119_36_2
  h1 := (1,3,1,0,1)
  h2 := (1,3,1,0,2)
  D1 := [[1, 1, 1, 3], [1, 1, 0, 0], [1, 1, 4, 2], [1, 1, 3, 4], [1, 1, 2, 1]]
  D2 := [[1, 1, 1, 4], [1, 1, 0, 1], [1, 1, 4, 3], [1, 1, 3, 0], [1, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_36_10 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T119_36
  T2 := Q2.T119_36_2
  h1 := (2,1,2,3,1)
  h2 := (2,1,2,3,4)
  D1 := [[2, 2, 2, 2], [2, 2, 0, 2], [2, 2, 3, 2], [2, 2, 1, 2], [2, 2, 4, 2]]
  D2 := [[2, 2, 2, 4], [2, 2, 0, 4], [2, 2, 3, 4], [2, 2, 1, 4], [2, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_36_15 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T119_36
  T2 := Q2.T119_36_2
  h1 := (3,4,3,4,1)
  h2 := (3,4,3,4,0)
  D1 := [[3, 3, 3, 2], [3, 3, 0, 1], [3, 3, 2, 0], [3, 3, 4, 4], [3, 3, 1, 3]]
  D2 := [[3, 3, 3, 0], [3, 3, 0, 4], [3, 3, 2, 3], [3, 3, 4, 2], [3, 3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_36_20 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T119_36
  T2 := Q2.T119_36_2
  h1 := (4,2,4,3,1)
  h2 := (4,2,4,3,2)
  D1 := [[4, 4, 4, 3], [4, 4, 0, 2], [4, 4, 1, 1], [4, 4, 2, 0], [4, 4, 3, 4]]
  D2 := [[4, 4, 4, 2], [4, 4, 0, 1], [4, 4, 1, 0], [4, 4, 2, 4], [4, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_41_5 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T119_41
  T2 := Q2.T119_41_2
  h1 := (1,3,4,0,0)
  h2 := (1,3,4,0,1)
  D1 := [[1, 4, 1, 2], [1, 4, 0, 2], [1, 4, 4, 2], [1, 4, 3, 2], [1, 4, 2, 2]]
  D2 := [[1, 4, 1, 3], [1, 4, 0, 3], [1, 4, 4, 3], [1, 4, 3, 3], [1, 4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_41_10 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T119_41
  T2 := Q2.T119_41_2
  h1 := (2,1,3,3,3)
  h2 := (2,1,3,3,1)
  D1 := [[2, 3, 2, 1], [2, 3, 0, 2], [2, 3, 3, 3], [2, 3, 1, 4], [2, 3, 4, 0]]
  D2 := [[2, 3, 2, 3], [2, 3, 0, 4], [2, 3, 3, 0], [2, 3, 1, 1], [2, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_41_15 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T119_41
  T2 := Q2.T119_41_2
  h1 := (3,4,2,4,0)
  h2 := (3,4,2,4,4)
  D1 := [[3, 2, 3, 2], [3, 2, 0, 0], [3, 2, 2, 3], [3, 2, 4, 1], [3, 2, 1, 4]]
  D2 := [[3, 2, 3, 0], [3, 2, 0, 3], [3, 2, 2, 1], [3, 2, 4, 4], [3, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_41_20 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T119_41
  T2 := Q2.T119_41_2
  h1 := (4,2,1,3,1)
  h2 := (4,2,1,3,2)
  D1 := [[4, 1, 4, 0], [4, 1, 0, 1], [4, 1, 1, 2], [4, 1, 2, 3], [4, 1, 3, 4]]
  D2 := [[4, 1, 4, 4], [4, 1, 0, 0], [4, 1, 1, 1], [4, 1, 2, 2], [4, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_46_5 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T119_46
  T2 := Q2.T119_46_2
  h1 := (1,3,3,0,2)
  h2 := (1,3,3,0,3)
  D1 := [[1, 3, 1, 4], [1, 3, 0, 3], [1, 3, 4, 2], [1, 3, 3, 1], [1, 3, 2, 0]]
  D2 := [[1, 3, 1, 0], [1, 3, 0, 4], [1, 3, 4, 3], [1, 3, 3, 2], [1, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_46_10 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T119_46
  T2 := Q2.T119_46_2
  h1 := (2,1,1,3,4)
  h2 := (2,1,1,3,2)
  D1 := [[2, 1, 2, 3], [2, 1, 0, 2], [2, 1, 3, 1], [2, 1, 1, 0], [2, 1, 4, 4]]
  D2 := [[2, 1, 2, 0], [2, 1, 0, 4], [2, 1, 3, 3], [2, 1, 1, 2], [2, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_46_15 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T119_46
  T2 := Q2.T119_46_2
  h1 := (3,4,4,4,2)
  h2 := (3,4,4,4,1)
  D1 := [[3, 4, 3, 2], [3, 4, 0, 2], [3, 4, 2, 2], [3, 4, 4, 2], [3, 4, 1, 2]]
  D2 := [[3, 4, 3, 0], [3, 4, 0, 0], [3, 4, 2, 0], [3, 4, 4, 0], [3, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_46_20 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T119_46
  T2 := Q2.T119_46_2
  h1 := (4,2,2,3,1)
  h2 := (4,2,2,3,2)
  D1 := [[4, 2, 4, 1], [4, 2, 0, 3], [4, 2, 1, 0], [4, 2, 2, 2], [4, 2, 3, 4]]
  D2 := [[4, 2, 4, 0], [4, 2, 0, 2], [4, 2, 1, 4], [4, 2, 2, 1], [4, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_51_5 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T119_51
  T2 := Q2.T119_51_2
  h1 := (1,3,0,0,3)
  h2 := (1,3,0,0,4)
  D1 := [[1, 0, 1, 0], [1, 0, 0, 1], [1, 0, 4, 2], [1, 0, 3, 3], [1, 0, 2, 4]]
  D2 := [[1, 0, 1, 1], [1, 0, 0, 2], [1, 0, 4, 3], [1, 0, 3, 4], [1, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_51_10 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T119_51
  T2 := Q2.T119_51_2
  h1 := (2,1,0,3,2)
  h2 := (2,1,0,3,0)
  D1 := [[2, 0, 2, 4], [2, 0, 0, 2], [2, 0, 3, 0], [2, 0, 1, 3], [2, 0, 4, 1]]
  D2 := [[2, 0, 2, 1], [2, 0, 0, 4], [2, 0, 3, 2], [2, 0, 1, 0], [2, 0, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_51_15 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T119_51
  T2 := Q2.T119_51_2
  h1 := (3,4,0,4,3)
  h2 := (3,4,0,4,2)
  D1 := [[3, 0, 3, 2], [3, 0, 0, 3], [3, 0, 2, 4], [3, 0, 4, 0], [3, 0, 1, 1]]
  D2 := [[3, 0, 3, 0], [3, 0, 0, 1], [3, 0, 2, 2], [3, 0, 4, 3], [3, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_51_20 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T119_51
  T2 := Q2.T119_51_2
  h1 := (4,2,0,3,1)
  h2 := (4,2,0,3,2)
  D1 := [[4, 0, 4, 4], [4, 0, 0, 4], [4, 0, 1, 4], [4, 0, 2, 4], [4, 0, 3, 4]]
  D2 := [[4, 0, 4, 3], [4, 0, 0, 3], [4, 0, 1, 3], [4, 0, 2, 3], [4, 0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_70_5 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T119_70
  T2 := Q2.T119_70_2
  h1 := (1,3,0,0,3)
  h2 := (1,3,0,0,4)
  D1 := [[1, 0, 1, 0], [1, 0, 0, 1], [1, 0, 4, 2], [1, 0, 3, 3], [1, 0, 2, 4]]
  D2 := [[1, 0, 1, 1], [1, 0, 0, 2], [1, 0, 4, 3], [1, 0, 3, 4], [1, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_70_6 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T119_70
  T2 := Q2.T119_70_2
  h1 := (1,3,1,0,3)
  h2 := (1,3,1,0,4)
  D1 := [[1, 1, 1, 0], [1, 1, 0, 2], [1, 1, 4, 4], [1, 1, 3, 1], [1, 1, 2, 3]]
  D2 := [[1, 1, 1, 1], [1, 1, 0, 3], [1, 1, 4, 0], [1, 1, 3, 2], [1, 1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_70_7 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T119_70
  T2 := Q2.T119_70_2
  h1 := (1,3,2,0,3)
  h2 := (1,3,2,0,4)
  D1 := [[1, 2, 1, 0], [1, 2, 0, 3], [1, 2, 4, 1], [1, 2, 3, 4], [1, 2, 2, 2]]
  D2 := [[1, 2, 1, 1], [1, 2, 0, 4], [1, 2, 4, 2], [1, 2, 3, 0], [1, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_70_8 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T119_70
  T2 := Q2.T119_70_2
  h1 := (1,3,3,0,3)
  h2 := (1,3,3,0,4)
  D1 := [[1, 3, 1, 0], [1, 3, 0, 4], [1, 3, 4, 3], [1, 3, 3, 2], [1, 3, 2, 1]]
  D2 := [[1, 3, 1, 1], [1, 3, 0, 0], [1, 3, 4, 4], [1, 3, 3, 3], [1, 3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_70_9 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T119_70
  T2 := Q2.T119_70_2
  h1 := (1,3,4,0,3)
  h2 := (1,3,4,0,4)
  D1 := [[1, 4, 1, 0], [1, 4, 0, 0], [1, 4, 4, 0], [1, 4, 3, 0], [1, 4, 2, 0]]
  D2 := [[1, 4, 1, 1], [1, 4, 0, 1], [1, 4, 4, 1], [1, 4, 3, 1], [1, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_70_10 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T119_70
  T2 := Q2.T119_70_2
  h1 := (2,1,0,3,2)
  h2 := (2,1,0,3,0)
  D1 := [[2, 0, 2, 4], [2, 0, 0, 2], [2, 0, 3, 0], [2, 0, 1, 3], [2, 0, 4, 1]]
  D2 := [[2, 0, 2, 1], [2, 0, 0, 4], [2, 0, 3, 2], [2, 0, 1, 0], [2, 0, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_70_11 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T119_70
  T2 := Q2.T119_70_2
  h1 := (2,1,1,3,2)
  h2 := (2,1,1,3,0)
  D1 := [[2, 1, 2, 1], [2, 1, 0, 0], [2, 1, 3, 4], [2, 1, 1, 3], [2, 1, 4, 2]]
  D2 := [[2, 1, 2, 3], [2, 1, 0, 2], [2, 1, 3, 1], [2, 1, 1, 0], [2, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_70_12 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T119_70
  T2 := Q2.T119_70_2
  h1 := (2,1,2,3,2)
  h2 := (2,1,2,3,0)
  D1 := [[2, 2, 2, 3], [2, 2, 0, 3], [2, 2, 3, 3], [2, 2, 1, 3], [2, 2, 4, 3]]
  D2 := [[2, 2, 2, 0], [2, 2, 0, 0], [2, 2, 3, 0], [2, 2, 1, 0], [2, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_70_13 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T119_70
  T2 := Q2.T119_70_2
  h1 := (2,1,3,3,2)
  h2 := (2,1,3,3,0)
  D1 := [[2, 3, 2, 0], [2, 3, 0, 1], [2, 3, 3, 2], [2, 3, 1, 3], [2, 3, 4, 4]]
  D2 := [[2, 3, 2, 2], [2, 3, 0, 3], [2, 3, 3, 4], [2, 3, 1, 0], [2, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_70_14 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T119_70
  T2 := Q2.T119_70_2
  h1 := (2,1,4,3,2)
  h2 := (2,1,4,3,0)
  D1 := [[2, 4, 2, 2], [2, 4, 0, 4], [2, 4, 3, 1], [2, 4, 1, 3], [2, 4, 4, 0]]
  D2 := [[2, 4, 2, 4], [2, 4, 0, 1], [2, 4, 3, 3], [2, 4, 1, 0], [2, 4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_70_15 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T119_70
  T2 := Q2.T119_70_2
  h1 := (3,4,0,4,3)
  h2 := (3,4,0,4,2)
  D1 := [[3, 0, 3, 2], [3, 0, 0, 3], [3, 0, 2, 4], [3, 0, 4, 0], [3, 0, 1, 1]]
  D2 := [[3, 0, 3, 0], [3, 0, 0, 1], [3, 0, 2, 2], [3, 0, 4, 3], [3, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_70_16 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T119_70
  T2 := Q2.T119_70_2
  h1 := (3,4,1,4,3)
  h2 := (3,4,1,4,2)
  D1 := [[3, 1, 3, 1], [3, 1, 0, 3], [3, 1, 2, 0], [3, 1, 4, 2], [3, 1, 1, 4]]
  D2 := [[3, 1, 3, 4], [3, 1, 0, 1], [3, 1, 2, 3], [3, 1, 4, 0], [3, 1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_70_17 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T119_70
  T2 := Q2.T119_70_2
  h1 := (3,4,2,4,3)
  h2 := (3,4,2,4,2)
  D1 := [[3, 2, 3, 0], [3, 2, 0, 3], [3, 2, 2, 1], [3, 2, 4, 4], [3, 2, 1, 2]]
  D2 := [[3, 2, 3, 3], [3, 2, 0, 1], [3, 2, 2, 4], [3, 2, 4, 2], [3, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_70_18 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T119_70
  T2 := Q2.T119_70_2
  h1 := (3,4,3,4,3)
  h2 := (3,4,3,4,2)
  D1 := [[3, 3, 3, 4], [3, 3, 0, 3], [3, 3, 2, 2], [3, 3, 4, 1], [3, 3, 1, 0]]
  D2 := [[3, 3, 3, 2], [3, 3, 0, 1], [3, 3, 2, 0], [3, 3, 4, 4], [3, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_70_19 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T119_70
  T2 := Q2.T119_70_2
  h1 := (3,4,4,4,3)
  h2 := (3,4,4,4,2)
  D1 := [[3, 4, 3, 3], [3, 4, 0, 3], [3, 4, 2, 3], [3, 4, 4, 3], [3, 4, 1, 3]]
  D2 := [[3, 4, 3, 1], [3, 4, 0, 1], [3, 4, 2, 1], [3, 4, 4, 1], [3, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_70_20 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T119_70
  T2 := Q2.T119_70_2
  h1 := (4,2,0,3,1)
  h2 := (4,2,0,3,2)
  D1 := [[4, 0, 4, 4], [4, 0, 0, 4], [4, 0, 1, 4], [4, 0, 2, 4], [4, 0, 3, 4]]
  D2 := [[4, 0, 4, 3], [4, 0, 0, 3], [4, 0, 1, 3], [4, 0, 2, 3], [4, 0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_70_21 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T119_70
  T2 := Q2.T119_70_2
  h1 := (4,2,1,3,1)
  h2 := (4,2,1,3,2)
  D1 := [[4, 1, 4, 0], [4, 1, 0, 1], [4, 1, 1, 2], [4, 1, 2, 3], [4, 1, 3, 4]]
  D2 := [[4, 1, 4, 4], [4, 1, 0, 0], [4, 1, 1, 1], [4, 1, 2, 2], [4, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_70_22 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T119_70
  T2 := Q2.T119_70_2
  h1 := (4,2,2,3,1)
  h2 := (4,2,2,3,2)
  D1 := [[4, 2, 4, 1], [4, 2, 0, 3], [4, 2, 1, 0], [4, 2, 2, 2], [4, 2, 3, 4]]
  D2 := [[4, 2, 4, 0], [4, 2, 0, 2], [4, 2, 1, 4], [4, 2, 2, 1], [4, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_70_23 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T119_70
  T2 := Q2.T119_70_2
  h1 := (4,2,3,3,1)
  h2 := (4,2,3,3,2)
  D1 := [[4, 3, 4, 2], [4, 3, 0, 0], [4, 3, 1, 3], [4, 3, 2, 1], [4, 3, 3, 4]]
  D2 := [[4, 3, 4, 1], [4, 3, 0, 4], [4, 3, 1, 2], [4, 3, 2, 0], [4, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_70_24 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T119_70
  T2 := Q2.T119_70_2
  h1 := (4,2,4,3,1)
  h2 := (4,2,4,3,2)
  D1 := [[4, 4, 4, 3], [4, 4, 0, 2], [4, 4, 1, 1], [4, 4, 2, 0], [4, 4, 3, 4]]
  D2 := [[4, 4, 4, 2], [4, 4, 0, 1], [4, 4, 1, 0], [4, 4, 2, 4], [4, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_71_5 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T119_71
  T2 := Q2.T119_71_2
  h1 := (1,3,0,0,1)
  h2 := (1,3,0,0,2)
  D1 := [[1, 0, 1, 3], [1, 0, 0, 4], [1, 0, 4, 0], [1, 0, 3, 1], [1, 0, 2, 2]]
  D2 := [[1, 0, 1, 4], [1, 0, 0, 0], [1, 0, 4, 1], [1, 0, 3, 2], [1, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_71_6 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T119_71
  T2 := Q2.T119_71_2
  h1 := (1,3,1,4,1)
  h2 := (1,3,1,4,2)
  D1 := [[1, 1, 0, 4], [1, 1, 4, 1], [1, 1, 3, 3], [1, 1, 2, 0], [1, 1, 1, 2]]
  D2 := [[1, 1, 0, 0], [1, 1, 4, 2], [1, 1, 3, 4], [1, 1, 2, 1], [1, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_71_7 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T119_71
  T2 := Q2.T119_71_2
  h1 := (1,3,2,3,1)
  h2 := (1,3,2,3,2)
  D1 := [[1, 2, 4, 0], [1, 2, 3, 3], [1, 2, 2, 1], [1, 2, 1, 4], [1, 2, 0, 2]]
  D2 := [[1, 2, 4, 1], [1, 2, 3, 4], [1, 2, 2, 2], [1, 2, 1, 0], [1, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_71_8 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T119_71
  T2 := Q2.T119_71_2
  h1 := (1,3,3,2,1)
  h2 := (1,3,3,2,2)
  D1 := [[1, 3, 3, 1], [1, 3, 2, 0], [1, 3, 1, 4], [1, 3, 0, 3], [1, 3, 4, 2]]
  D2 := [[1, 3, 3, 2], [1, 3, 2, 1], [1, 3, 1, 0], [1, 3, 0, 4], [1, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_71_9 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T119_71
  T2 := Q2.T119_71_2
  h1 := (1,3,4,1,1)
  h2 := (1,3,4,1,2)
  D1 := [[1, 4, 2, 2], [1, 4, 1, 2], [1, 4, 0, 2], [1, 4, 4, 2], [1, 4, 3, 2]]
  D2 := [[1, 4, 2, 3], [1, 4, 1, 3], [1, 4, 0, 3], [1, 4, 4, 3], [1, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_71_10 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T119_71
  T2 := Q2.T119_71_2
  h1 := (2,1,0,3,3)
  h2 := (2,1,0,3,1)
  D1 := [[2, 0, 2, 0], [2, 0, 0, 3], [2, 0, 3, 1], [2, 0, 1, 4], [2, 0, 4, 2]]
  D2 := [[2, 0, 2, 2], [2, 0, 0, 0], [2, 0, 3, 3], [2, 0, 1, 1], [2, 0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_71_11 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T119_71
  T2 := Q2.T119_71_2
  h1 := (2,1,1,2,3)
  h2 := (2,1,1,2,1)
  D1 := [[2, 1, 1, 4], [2, 1, 4, 3], [2, 1, 2, 2], [2, 1, 0, 1], [2, 1, 3, 0]]
  D2 := [[2, 1, 1, 1], [2, 1, 4, 0], [2, 1, 2, 4], [2, 1, 0, 3], [2, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_71_12 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T119_71
  T2 := Q2.T119_71_2
  h1 := (2,1,2,1,3)
  h2 := (2,1,2,1,1)
  D1 := [[2, 2, 0, 3], [2, 2, 3, 3], [2, 2, 1, 3], [2, 2, 4, 3], [2, 2, 2, 3]]
  D2 := [[2, 2, 0, 0], [2, 2, 3, 0], [2, 2, 1, 0], [2, 2, 4, 0], [2, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_71_13 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T119_71
  T2 := Q2.T119_71_2
  h1 := (2,1,3,0,3)
  h2 := (2,1,3,0,1)
  D1 := [[2, 3, 4, 2], [2, 3, 2, 3], [2, 3, 0, 4], [2, 3, 3, 0], [2, 3, 1, 1]]
  D2 := [[2, 3, 4, 4], [2, 3, 2, 0], [2, 3, 0, 1], [2, 3, 3, 2], [2, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_71_14 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T119_71
  T2 := Q2.T119_71_2
  h1 := (2,1,4,4,3)
  h2 := (2,1,4,4,1)
  D1 := [[2, 4, 3, 1], [2, 4, 1, 3], [2, 4, 4, 0], [2, 4, 2, 2], [2, 4, 0, 4]]
  D2 := [[2, 4, 3, 3], [2, 4, 1, 0], [2, 4, 4, 2], [2, 4, 2, 4], [2, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_71_15 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T119_71
  T2 := Q2.T119_71_2
  h1 := (3,4,0,4,2)
  h2 := (3,4,0,4,1)
  D1 := [[3, 0, 3, 1], [3, 0, 0, 2], [3, 0, 2, 3], [3, 0, 4, 4], [3, 0, 1, 0]]
  D2 := [[3, 0, 3, 4], [3, 0, 0, 0], [3, 0, 2, 1], [3, 0, 4, 2], [3, 0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_71_16 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T119_71
  T2 := Q2.T119_71_2
  h1 := (3,4,1,3,2)
  h2 := (3,4,1,3,1)
  D1 := [[3, 1, 2, 3], [3, 1, 4, 0], [3, 1, 1, 2], [3, 1, 3, 4], [3, 1, 0, 1]]
  D2 := [[3, 1, 2, 1], [3, 1, 4, 3], [3, 1, 1, 0], [3, 1, 3, 2], [3, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_71_17 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T119_71
  T2 := Q2.T119_71_2
  h1 := (3,4,2,2,2)
  h2 := (3,4,2,2,1)
  D1 := [[3, 2, 1, 0], [3, 2, 3, 3], [3, 2, 0, 1], [3, 2, 2, 4], [3, 2, 4, 2]]
  D2 := [[3, 2, 1, 3], [3, 2, 3, 1], [3, 2, 0, 4], [3, 2, 2, 2], [3, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_71_18 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T119_71
  T2 := Q2.T119_71_2
  h1 := (3,4,3,1,2)
  h2 := (3,4,3,1,1)
  D1 := [[3, 3, 0, 2], [3, 3, 2, 1], [3, 3, 4, 0], [3, 3, 1, 4], [3, 3, 3, 3]]
  D2 := [[3, 3, 0, 0], [3, 3, 2, 4], [3, 3, 4, 3], [3, 3, 1, 2], [3, 3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_71_19 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T119_71
  T2 := Q2.T119_71_2
  h1 := (3,4,4,0,2)
  h2 := (3,4,4,0,1)
  D1 := [[3, 4, 4, 4], [3, 4, 1, 4], [3, 4, 3, 4], [3, 4, 0, 4], [3, 4, 2, 4]]
  D2 := [[3, 4, 4, 2], [3, 4, 1, 2], [3, 4, 3, 2], [3, 4, 0, 2], [3, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_71_20 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T119_71
  T2 := Q2.T119_71_2
  h1 := (4,2,0,3,3)
  h2 := (4,2,0,3,4)
  D1 := [[4, 0, 4, 1], [4, 0, 0, 1], [4, 0, 1, 1], [4, 0, 2, 1], [4, 0, 3, 1]]
  D2 := [[4, 0, 4, 0], [4, 0, 0, 0], [4, 0, 1, 0], [4, 0, 2, 0], [4, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_71_21 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T119_71
  T2 := Q2.T119_71_2
  h1 := (4,2,1,2,3)
  h2 := (4,2,1,2,4)
  D1 := [[4, 1, 3, 1], [4, 1, 4, 2], [4, 1, 0, 3], [4, 1, 1, 4], [4, 1, 2, 0]]
  D2 := [[4, 1, 3, 0], [4, 1, 4, 1], [4, 1, 0, 2], [4, 1, 1, 3], [4, 1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_71_22 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T119_71
  T2 := Q2.T119_71_2
  h1 := (4,2,2,1,3)
  h2 := (4,2,2,1,4)
  D1 := [[4, 2, 2, 1], [4, 2, 3, 3], [4, 2, 4, 0], [4, 2, 0, 2], [4, 2, 1, 4]]
  D2 := [[4, 2, 2, 0], [4, 2, 3, 2], [4, 2, 4, 4], [4, 2, 0, 1], [4, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_71_23 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T119_71
  T2 := Q2.T119_71_2
  h1 := (4,2,3,0,3)
  h2 := (4,2,3,0,4)
  D1 := [[4, 3, 1, 1], [4, 3, 2, 4], [4, 3, 3, 2], [4, 3, 4, 0], [4, 3, 0, 3]]
  D2 := [[4, 3, 1, 0], [4, 3, 2, 3], [4, 3, 3, 1], [4, 3, 4, 4], [4, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_71_24 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T119_71
  T2 := Q2.T119_71_2
  h1 := (4,2,4,4,3)
  h2 := (4,2,4,4,4)
  D1 := [[4, 4, 0, 1], [4, 4, 1, 0], [4, 4, 2, 4], [4, 4, 3, 3], [4, 4, 4, 2]]
  D2 := [[4, 4, 0, 0], [4, 4, 1, 4], [4, 4, 2, 3], [4, 4, 3, 2], [4, 4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
