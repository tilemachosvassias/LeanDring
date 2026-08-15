/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C028
import LeanDring.P5.Data.EntryK.C029

/-!
# Species-table cell data, stage 2 — column-data-divergent columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
cdd tier, chunk 5: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_119_72_5 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨72, by decide⟩
  m := 5
  T1 := T119_72
  T2 := Q2.T119_72_2
  h1 := (1,3,0,0,3)
  h2 := (1,3,0,0,4)
  D1 := [[1, 0, 1, 0], [1, 0, 0, 1], [1, 0, 4, 2], [1, 0, 3, 3], [1, 0, 2, 4]]
  D2 := [[1, 0, 1, 1], [1, 0, 0, 2], [1, 0, 4, 3], [1, 0, 3, 4], [1, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_72_6 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨72, by decide⟩
  m := 5
  T1 := T119_72
  T2 := Q2.T119_72_2
  h1 := (1,3,1,3,3)
  h2 := (1,3,1,3,4)
  D1 := [[1, 1, 4, 2], [1, 1, 3, 4], [1, 1, 2, 1], [1, 1, 1, 3], [1, 1, 0, 0]]
  D2 := [[1, 1, 4, 3], [1, 1, 3, 0], [1, 1, 2, 2], [1, 1, 1, 4], [1, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_72_7 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨72, by decide⟩
  m := 5
  T1 := T119_72
  T2 := Q2.T119_72_2
  h1 := (1,3,2,1,3)
  h2 := (1,3,2,1,4)
  D1 := [[1, 2, 2, 4], [1, 2, 1, 2], [1, 2, 0, 0], [1, 2, 4, 3], [1, 2, 3, 1]]
  D2 := [[1, 2, 2, 0], [1, 2, 1, 3], [1, 2, 0, 1], [1, 2, 4, 4], [1, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_72_8 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨72, by decide⟩
  m := 5
  T1 := T119_72
  T2 := Q2.T119_72_2
  h1 := (1,3,3,4,3)
  h2 := (1,3,3,4,4)
  D1 := [[1, 3, 0, 1], [1, 3, 4, 0], [1, 3, 3, 4], [1, 3, 2, 3], [1, 3, 1, 2]]
  D2 := [[1, 3, 0, 2], [1, 3, 4, 1], [1, 3, 3, 0], [1, 3, 2, 4], [1, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_72_9 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨72, by decide⟩
  m := 5
  T1 := T119_72
  T2 := Q2.T119_72_2
  h1 := (1,3,4,2,3)
  h2 := (1,3,4,2,4)
  D1 := [[1, 4, 3, 3], [1, 4, 2, 3], [1, 4, 1, 3], [1, 4, 0, 3], [1, 4, 4, 3]]
  D2 := [[1, 4, 3, 4], [1, 4, 2, 4], [1, 4, 1, 4], [1, 4, 0, 4], [1, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_72_10 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨72, by decide⟩
  m := 5
  T1 := T119_72
  T2 := Q2.T119_72_2
  h1 := (2,1,0,3,2)
  h2 := (2,1,0,3,0)
  D1 := [[2, 0, 2, 4], [2, 0, 0, 2], [2, 0, 3, 0], [2, 0, 1, 3], [2, 0, 4, 1]]
  D2 := [[2, 0, 2, 1], [2, 0, 0, 4], [2, 0, 3, 2], [2, 0, 1, 0], [2, 0, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_72_11 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨72, by decide⟩
  m := 5
  T1 := T119_72
  T2 := Q2.T119_72_2
  h1 := (2,1,1,1,2)
  h2 := (2,1,1,1,0)
  D1 := [[2, 1, 0, 0], [2, 1, 3, 4], [2, 1, 1, 3], [2, 1, 4, 2], [2, 1, 2, 1]]
  D2 := [[2, 1, 0, 2], [2, 1, 3, 1], [2, 1, 1, 0], [2, 1, 4, 4], [2, 1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_72_12 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨72, by decide⟩
  m := 5
  T1 := T119_72
  T2 := Q2.T119_72_2
  h1 := (2,1,2,4,2)
  h2 := (2,1,2,4,0)
  D1 := [[2, 2, 3, 1], [2, 2, 1, 1], [2, 2, 4, 1], [2, 2, 2, 1], [2, 2, 0, 1]]
  D2 := [[2, 2, 3, 3], [2, 2, 1, 3], [2, 2, 4, 3], [2, 2, 2, 3], [2, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_72_13 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨72, by decide⟩
  m := 5
  T1 := T119_72
  T2 := Q2.T119_72_2
  h1 := (2,1,3,2,2)
  h2 := (2,1,3,2,0)
  D1 := [[2, 3, 1, 2], [2, 3, 4, 3], [2, 3, 2, 4], [2, 3, 0, 0], [2, 3, 3, 1]]
  D2 := [[2, 3, 1, 4], [2, 3, 4, 0], [2, 3, 2, 1], [2, 3, 0, 2], [2, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_72_14 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨72, by decide⟩
  m := 5
  T1 := T119_72
  T2 := Q2.T119_72_2
  h1 := (2,1,4,0,2)
  h2 := (2,1,4,0,0)
  D1 := [[2, 4, 4, 3], [2, 4, 2, 0], [2, 4, 0, 2], [2, 4, 3, 4], [2, 4, 1, 1]]
  D2 := [[2, 4, 4, 0], [2, 4, 2, 2], [2, 4, 0, 4], [2, 4, 3, 1], [2, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_72_15 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨72, by decide⟩
  m := 5
  T1 := T119_72
  T2 := Q2.T119_72_2
  h1 := (3,4,0,4,3)
  h2 := (3,4,0,4,2)
  D1 := [[3, 0, 3, 2], [3, 0, 0, 3], [3, 0, 2, 4], [3, 0, 4, 0], [3, 0, 1, 1]]
  D2 := [[3, 0, 3, 0], [3, 0, 0, 1], [3, 0, 2, 2], [3, 0, 4, 3], [3, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_72_16 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨72, by decide⟩
  m := 5
  T1 := T119_72
  T2 := Q2.T119_72_2
  h1 := (3,4,1,2,3)
  h2 := (3,4,1,2,2)
  D1 := [[3, 1, 1, 2], [3, 1, 3, 4], [3, 1, 0, 1], [3, 1, 2, 3], [3, 1, 4, 0]]
  D2 := [[3, 1, 1, 0], [3, 1, 3, 2], [3, 1, 0, 4], [3, 1, 2, 1], [3, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_72_17 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨72, by decide⟩
  m := 5
  T1 := T119_72
  T2 := Q2.T119_72_2
  h1 := (3,4,2,0,3)
  h2 := (3,4,2,0,2)
  D1 := [[3, 2, 4, 2], [3, 2, 1, 0], [3, 2, 3, 3], [3, 2, 0, 1], [3, 2, 2, 4]]
  D2 := [[3, 2, 4, 0], [3, 2, 1, 3], [3, 2, 3, 1], [3, 2, 0, 4], [3, 2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_72_18 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨72, by decide⟩
  m := 5
  T1 := T119_72
  T2 := Q2.T119_72_2
  h1 := (3,4,3,3,3)
  h2 := (3,4,3,3,2)
  D1 := [[3, 3, 2, 2], [3, 3, 4, 1], [3, 3, 1, 0], [3, 3, 3, 4], [3, 3, 0, 3]]
  D2 := [[3, 3, 2, 0], [3, 3, 4, 4], [3, 3, 1, 3], [3, 3, 3, 2], [3, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_72_19 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨72, by decide⟩
  m := 5
  T1 := T119_72
  T2 := Q2.T119_72_2
  h1 := (3,4,4,1,3)
  h2 := (3,4,4,1,2)
  D1 := [[3, 4, 0, 2], [3, 4, 2, 2], [3, 4, 4, 2], [3, 4, 1, 2], [3, 4, 3, 2]]
  D2 := [[3, 4, 0, 0], [3, 4, 2, 0], [3, 4, 4, 0], [3, 4, 1, 0], [3, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_72_20 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨72, by decide⟩
  m := 5
  T1 := T119_72
  T2 := Q2.T119_72_2
  h1 := (4,2,0,3,1)
  h2 := (4,2,0,3,2)
  D1 := [[4, 0, 4, 4], [4, 0, 0, 4], [4, 0, 1, 4], [4, 0, 2, 4], [4, 0, 3, 4]]
  D2 := [[4, 0, 4, 3], [4, 0, 0, 3], [4, 0, 1, 3], [4, 0, 2, 3], [4, 0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_72_21 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨72, by decide⟩
  m := 5
  T1 := T119_72
  T2 := Q2.T119_72_2
  h1 := (4,2,1,1,1)
  h2 := (4,2,1,1,2)
  D1 := [[4, 1, 2, 3], [4, 1, 3, 4], [4, 1, 4, 0], [4, 1, 0, 1], [4, 1, 1, 2]]
  D2 := [[4, 1, 2, 2], [4, 1, 3, 3], [4, 1, 4, 4], [4, 1, 0, 0], [4, 1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_72_22 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨72, by decide⟩
  m := 5
  T1 := T119_72
  T2 := Q2.T119_72_2
  h1 := (4,2,2,4,1)
  h2 := (4,2,2,4,2)
  D1 := [[4, 2, 0, 2], [4, 2, 1, 4], [4, 2, 2, 1], [4, 2, 3, 3], [4, 2, 4, 0]]
  D2 := [[4, 2, 0, 1], [4, 2, 1, 3], [4, 2, 2, 0], [4, 2, 3, 2], [4, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_72_23 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨72, by decide⟩
  m := 5
  T1 := T119_72
  T2 := Q2.T119_72_2
  h1 := (4,2,3,2,1)
  h2 := (4,2,3,2,2)
  D1 := [[4, 3, 3, 1], [4, 3, 4, 4], [4, 3, 0, 2], [4, 3, 1, 0], [4, 3, 2, 3]]
  D2 := [[4, 3, 3, 0], [4, 3, 4, 3], [4, 3, 0, 1], [4, 3, 1, 4], [4, 3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_72_24 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨72, by decide⟩
  m := 5
  T1 := T119_72
  T2 := Q2.T119_72_2
  h1 := (4,2,4,0,1)
  h2 := (4,2,4,0,2)
  D1 := [[4, 4, 1, 0], [4, 4, 2, 4], [4, 4, 3, 3], [4, 4, 4, 2], [4, 4, 0, 1]]
  D2 := [[4, 4, 1, 4], [4, 4, 2, 3], [4, 4, 3, 2], [4, 4, 4, 1], [4, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_32_5 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T120_32
  T2 := Q2.T120_32_2
  h1 := (1,1,4,4,0)
  h2 := (1,1,4,4,3)
  D1 := [[1, 4, 3, 2], [1, 4, 2, 2], [1, 4, 1, 2], [1, 4, 0, 2], [1, 4, 4, 2]]
  D2 := [[1, 4, 3, 0], [1, 4, 2, 0], [1, 4, 1, 0], [1, 4, 0, 0], [1, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_32_10 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T120_32
  T2 := Q2.T120_32_2
  h1 := (2,2,3,4,3)
  h2 := (2,2,3,4,4)
  D1 := [[2, 3, 1, 2], [2, 3, 4, 3], [2, 3, 2, 4], [2, 3, 0, 0], [2, 3, 3, 1]]
  D2 := [[2, 3, 1, 3], [2, 3, 4, 4], [2, 3, 2, 0], [2, 3, 0, 1], [2, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_32_15 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T120_32
  T2 := Q2.T120_32_2
  h1 := (3,3,2,0,0)
  h2 := (3,3,2,0,4)
  D1 := [[3, 2, 4, 0], [3, 2, 1, 3], [3, 2, 3, 1], [3, 2, 0, 4], [3, 2, 2, 2]]
  D2 := [[3, 2, 4, 4], [3, 2, 1, 2], [3, 2, 3, 0], [3, 2, 0, 3], [3, 2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_32_20 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T120_32
  T2 := Q2.T120_32_2
  h1 := (4,4,1,2,2)
  h2 := (4,4,1,2,4)
  D1 := [[4, 1, 2, 1], [4, 1, 3, 2], [4, 1, 4, 3], [4, 1, 0, 4], [4, 1, 1, 0]]
  D2 := [[4, 1, 2, 3], [4, 1, 3, 4], [4, 1, 4, 0], [4, 1, 0, 1], [4, 1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_37_5 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T120_37
  T2 := Q2.T120_37_2
  h1 := (1,1,2,4,3)
  h2 := (1,1,2,4,1)
  D1 := [[1, 2, 3, 0], [1, 2, 2, 3], [1, 2, 1, 1], [1, 2, 0, 4], [1, 2, 4, 2]]
  D2 := [[1, 2, 3, 3], [1, 2, 2, 1], [1, 2, 1, 4], [1, 2, 0, 2], [1, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_37_10 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T120_37
  T2 := Q2.T120_37_2
  h1 := (2,2,4,4,2)
  h2 := (2,2,4,4,3)
  D1 := [[2, 4, 1, 0], [2, 4, 4, 2], [2, 4, 2, 4], [2, 4, 0, 1], [2, 4, 3, 3]]
  D2 := [[2, 4, 1, 1], [2, 4, 4, 3], [2, 4, 2, 0], [2, 4, 0, 2], [2, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_37_15 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T120_37
  T2 := Q2.T120_37_2
  h1 := (3,3,1,0,3)
  h2 := (3,3,1,0,2)
  D1 := [[3, 1, 4, 0], [3, 1, 1, 2], [3, 1, 3, 4], [3, 1, 0, 1], [3, 1, 2, 3]]
  D2 := [[3, 1, 4, 4], [3, 1, 1, 1], [3, 1, 3, 3], [3, 1, 0, 0], [3, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_37_20 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T120_37
  T2 := Q2.T120_37_2
  h1 := (4,4,3,2,2)
  h2 := (4,4,3,2,4)
  D1 := [[4, 3, 2, 0], [4, 3, 3, 3], [4, 3, 4, 1], [4, 3, 0, 4], [4, 3, 1, 2]]
  D2 := [[4, 3, 2, 2], [4, 3, 3, 0], [4, 3, 4, 3], [4, 3, 0, 1], [4, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_42_5 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T120_42
  T2 := Q2.T120_42_2
  h1 := (1,1,3,4,4)
  h2 := (1,1,3,4,2)
  D1 := [[1, 3, 3, 1], [1, 3, 2, 0], [1, 3, 1, 4], [1, 3, 0, 3], [1, 3, 4, 2]]
  D2 := [[1, 3, 3, 4], [1, 3, 2, 3], [1, 3, 1, 2], [1, 3, 0, 1], [1, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_42_10 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T120_42
  T2 := Q2.T120_42_2
  h1 := (2,2,1,4,0)
  h2 := (2,2,1,4,1)
  D1 := [[2, 1, 1, 1], [2, 1, 4, 0], [2, 1, 2, 4], [2, 1, 0, 3], [2, 1, 3, 2]]
  D2 := [[2, 1, 1, 2], [2, 1, 4, 1], [2, 1, 2, 0], [2, 1, 0, 4], [2, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_42_15 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T120_42
  T2 := Q2.T120_42_2
  h1 := (3,3,4,0,4)
  h2 := (3,3,4,0,3)
  D1 := [[3, 4, 4, 0], [3, 4, 1, 0], [3, 4, 3, 0], [3, 4, 0, 0], [3, 4, 2, 0]]
  D2 := [[3, 4, 4, 4], [3, 4, 1, 4], [3, 4, 3, 4], [3, 4, 0, 4], [3, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_42_20 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T120_42
  T2 := Q2.T120_42_2
  h1 := (4,4,2,2,2)
  h2 := (4,4,2,2,4)
  D1 := [[4, 2, 2, 3], [4, 2, 3, 0], [4, 2, 4, 2], [4, 2, 0, 4], [4, 2, 1, 1]]
  D2 := [[4, 2, 2, 0], [4, 2, 3, 2], [4, 2, 4, 4], [4, 2, 0, 1], [4, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_47_5 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T120_47
  T2 := Q2.T120_47_2
  h1 := (1,1,1,4,2)
  h2 := (1,1,1,4,0)
  D1 := [[1, 1, 3, 4], [1, 1, 2, 1], [1, 1, 1, 3], [1, 1, 0, 0], [1, 1, 4, 2]]
  D2 := [[1, 1, 3, 2], [1, 1, 2, 4], [1, 1, 1, 1], [1, 1, 0, 3], [1, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_47_10 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T120_47
  T2 := Q2.T120_47_2
  h1 := (2,2,2,4,4)
  h2 := (2,2,2,4,0)
  D1 := [[2, 2, 1, 4], [2, 2, 4, 4], [2, 2, 2, 4], [2, 2, 0, 4], [2, 2, 3, 4]]
  D2 := [[2, 2, 1, 0], [2, 2, 4, 0], [2, 2, 2, 0], [2, 2, 0, 0], [2, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_47_15 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T120_47
  T2 := Q2.T120_47_2
  h1 := (3,3,3,0,2)
  h2 := (3,3,3,0,1)
  D1 := [[3, 3, 4, 0], [3, 3, 1, 4], [3, 3, 3, 3], [3, 3, 0, 2], [3, 3, 2, 1]]
  D2 := [[3, 3, 4, 4], [3, 3, 1, 3], [3, 3, 3, 2], [3, 3, 0, 1], [3, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_47_20 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T120_47
  T2 := Q2.T120_47_2
  h1 := (4,4,4,2,2)
  h2 := (4,4,4,2,4)
  D1 := [[4, 4, 2, 2], [4, 4, 3, 1], [4, 4, 4, 0], [4, 4, 0, 4], [4, 4, 1, 3]]
  D2 := [[4, 4, 2, 4], [4, 4, 3, 3], [4, 4, 4, 2], [4, 4, 0, 1], [4, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_52_5 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T120_52
  T2 := Q2.T120_52_2
  h1 := (1,1,0,4,1)
  h2 := (1,1,0,4,4)
  D1 := [[1, 0, 3, 3], [1, 0, 2, 4], [1, 0, 1, 0], [1, 0, 0, 1], [1, 0, 4, 2]]
  D2 := [[1, 0, 3, 1], [1, 0, 2, 2], [1, 0, 1, 3], [1, 0, 0, 4], [1, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_52_10 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T120_52
  T2 := Q2.T120_52_2
  h1 := (2,2,0,4,1)
  h2 := (2,2,0,4,2)
  D1 := [[2, 0, 1, 3], [2, 0, 4, 1], [2, 0, 2, 4], [2, 0, 0, 2], [2, 0, 3, 0]]
  D2 := [[2, 0, 1, 4], [2, 0, 4, 2], [2, 0, 2, 0], [2, 0, 0, 3], [2, 0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_52_15 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T120_52
  T2 := Q2.T120_52_2
  h1 := (3,3,0,0,1)
  h2 := (3,3,0,0,0)
  D1 := [[3, 0, 4, 0], [3, 0, 1, 1], [3, 0, 3, 2], [3, 0, 0, 3], [3, 0, 2, 4]]
  D2 := [[3, 0, 4, 4], [3, 0, 1, 0], [3, 0, 3, 1], [3, 0, 0, 2], [3, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_52_20 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T120_52
  T2 := Q2.T120_52_2
  h1 := (4,4,0,2,2)
  h2 := (4,4,0,2,4)
  D1 := [[4, 0, 2, 4], [4, 0, 3, 4], [4, 0, 4, 4], [4, 0, 0, 4], [4, 0, 1, 4]]
  D2 := [[4, 0, 2, 1], [4, 0, 3, 1], [4, 0, 4, 1], [4, 0, 0, 1], [4, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_75_5 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T120_75
  T2 := Q2.T120_75_2
  h1 := (1,1,0,4,1)
  h2 := (1,1,0,4,4)
  D1 := [[1, 0, 3, 3], [1, 0, 2, 4], [1, 0, 1, 0], [1, 0, 0, 1], [1, 0, 4, 2]]
  D2 := [[1, 0, 3, 1], [1, 0, 2, 2], [1, 0, 1, 3], [1, 0, 0, 4], [1, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_75_6 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T120_75
  T2 := Q2.T120_75_2
  h1 := (1,1,1,4,1)
  h2 := (1,1,1,4,4)
  D1 := [[1, 1, 3, 3], [1, 1, 2, 0], [1, 1, 1, 2], [1, 1, 0, 4], [1, 1, 4, 1]]
  D2 := [[1, 1, 3, 1], [1, 1, 2, 3], [1, 1, 1, 0], [1, 1, 0, 2], [1, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_75_7 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T120_75
  T2 := Q2.T120_75_2
  h1 := (1,1,2,4,1)
  h2 := (1,1,2,4,4)
  D1 := [[1, 2, 3, 3], [1, 2, 2, 1], [1, 2, 1, 4], [1, 2, 0, 2], [1, 2, 4, 0]]
  D2 := [[1, 2, 3, 1], [1, 2, 2, 4], [1, 2, 1, 2], [1, 2, 0, 0], [1, 2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_75_8 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T120_75
  T2 := Q2.T120_75_2
  h1 := (1,1,3,4,1)
  h2 := (1,1,3,4,4)
  D1 := [[1, 3, 3, 3], [1, 3, 2, 2], [1, 3, 1, 1], [1, 3, 0, 0], [1, 3, 4, 4]]
  D2 := [[1, 3, 3, 1], [1, 3, 2, 0], [1, 3, 1, 4], [1, 3, 0, 3], [1, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_75_9 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T120_75
  T2 := Q2.T120_75_2
  h1 := (1,1,4,4,1)
  h2 := (1,1,4,4,4)
  D1 := [[1, 4, 3, 3], [1, 4, 2, 3], [1, 4, 1, 3], [1, 4, 0, 3], [1, 4, 4, 3]]
  D2 := [[1, 4, 3, 1], [1, 4, 2, 1], [1, 4, 1, 1], [1, 4, 0, 1], [1, 4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_75_10 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T120_75
  T2 := Q2.T120_75_2
  h1 := (2,2,0,4,1)
  h2 := (2,2,0,4,2)
  D1 := [[2, 0, 1, 3], [2, 0, 4, 1], [2, 0, 2, 4], [2, 0, 0, 2], [2, 0, 3, 0]]
  D2 := [[2, 0, 1, 4], [2, 0, 4, 2], [2, 0, 2, 0], [2, 0, 0, 3], [2, 0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_75_11 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T120_75
  T2 := Q2.T120_75_2
  h1 := (2,2,1,4,1)
  h2 := (2,2,1,4,2)
  D1 := [[2, 1, 1, 2], [2, 1, 4, 1], [2, 1, 2, 0], [2, 1, 0, 4], [2, 1, 3, 3]]
  D2 := [[2, 1, 1, 3], [2, 1, 4, 2], [2, 1, 2, 1], [2, 1, 0, 0], [2, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_75_12 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T120_75
  T2 := Q2.T120_75_2
  h1 := (2,2,2,4,1)
  h2 := (2,2,2,4,2)
  D1 := [[2, 2, 1, 1], [2, 2, 4, 1], [2, 2, 2, 1], [2, 2, 0, 1], [2, 2, 3, 1]]
  D2 := [[2, 2, 1, 2], [2, 2, 4, 2], [2, 2, 2, 2], [2, 2, 0, 2], [2, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_75_13 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T120_75
  T2 := Q2.T120_75_2
  h1 := (2,2,3,4,1)
  h2 := (2,2,3,4,2)
  D1 := [[2, 3, 1, 0], [2, 3, 4, 1], [2, 3, 2, 2], [2, 3, 0, 3], [2, 3, 3, 4]]
  D2 := [[2, 3, 1, 1], [2, 3, 4, 2], [2, 3, 2, 3], [2, 3, 0, 4], [2, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_75_14 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T120_75
  T2 := Q2.T120_75_2
  h1 := (2,2,4,4,1)
  h2 := (2,2,4,4,2)
  D1 := [[2, 4, 1, 4], [2, 4, 4, 1], [2, 4, 2, 3], [2, 4, 0, 0], [2, 4, 3, 2]]
  D2 := [[2, 4, 1, 0], [2, 4, 4, 2], [2, 4, 2, 4], [2, 4, 0, 1], [2, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_75_15 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T120_75
  T2 := Q2.T120_75_2
  h1 := (3,3,0,0,1)
  h2 := (3,3,0,0,0)
  D1 := [[3, 0, 4, 0], [3, 0, 1, 1], [3, 0, 3, 2], [3, 0, 0, 3], [3, 0, 2, 4]]
  D2 := [[3, 0, 4, 4], [3, 0, 1, 0], [3, 0, 3, 1], [3, 0, 0, 2], [3, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_75_16 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T120_75
  T2 := Q2.T120_75_2
  h1 := (3,3,1,0,1)
  h2 := (3,3,1,0,0)
  D1 := [[3, 1, 4, 3], [3, 1, 1, 0], [3, 1, 3, 2], [3, 1, 0, 4], [3, 1, 2, 1]]
  D2 := [[3, 1, 4, 2], [3, 1, 1, 4], [3, 1, 3, 1], [3, 1, 0, 3], [3, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_75_17 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T120_75
  T2 := Q2.T120_75_2
  h1 := (3,3,2,0,1)
  h2 := (3,3,2,0,0)
  D1 := [[3, 2, 4, 1], [3, 2, 1, 4], [3, 2, 3, 2], [3, 2, 0, 0], [3, 2, 2, 3]]
  D2 := [[3, 2, 4, 0], [3, 2, 1, 3], [3, 2, 3, 1], [3, 2, 0, 4], [3, 2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_75_18 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T120_75
  T2 := Q2.T120_75_2
  h1 := (3,3,3,0,1)
  h2 := (3,3,3,0,0)
  D1 := [[3, 3, 4, 4], [3, 3, 1, 3], [3, 3, 3, 2], [3, 3, 0, 1], [3, 3, 2, 0]]
  D2 := [[3, 3, 4, 3], [3, 3, 1, 2], [3, 3, 3, 1], [3, 3, 0, 0], [3, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_75_19 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T120_75
  T2 := Q2.T120_75_2
  h1 := (3,3,4,0,1)
  h2 := (3,3,4,0,0)
  D1 := [[3, 4, 4, 2], [3, 4, 1, 2], [3, 4, 3, 2], [3, 4, 0, 2], [3, 4, 2, 2]]
  D2 := [[3, 4, 4, 1], [3, 4, 1, 1], [3, 4, 3, 1], [3, 4, 0, 1], [3, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_75_20 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T120_75
  T2 := Q2.T120_75_2
  h1 := (4,4,0,2,2)
  h2 := (4,4,0,2,4)
  D1 := [[4, 0, 2, 4], [4, 0, 3, 4], [4, 0, 4, 4], [4, 0, 0, 4], [4, 0, 1, 4]]
  D2 := [[4, 0, 2, 1], [4, 0, 3, 1], [4, 0, 4, 1], [4, 0, 0, 1], [4, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_75_21 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T120_75
  T2 := Q2.T120_75_2
  h1 := (4,4,1,2,2)
  h2 := (4,4,1,2,4)
  D1 := [[4, 1, 2, 1], [4, 1, 3, 2], [4, 1, 4, 3], [4, 1, 0, 4], [4, 1, 1, 0]]
  D2 := [[4, 1, 2, 3], [4, 1, 3, 4], [4, 1, 4, 0], [4, 1, 0, 1], [4, 1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_75_22 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T120_75
  T2 := Q2.T120_75_2
  h1 := (4,4,2,2,2)
  h2 := (4,4,2,2,4)
  D1 := [[4, 2, 2, 3], [4, 2, 3, 0], [4, 2, 4, 2], [4, 2, 0, 4], [4, 2, 1, 1]]
  D2 := [[4, 2, 2, 0], [4, 2, 3, 2], [4, 2, 4, 4], [4, 2, 0, 1], [4, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_75_23 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T120_75
  T2 := Q2.T120_75_2
  h1 := (4,4,3,2,2)
  h2 := (4,4,3,2,4)
  D1 := [[4, 3, 2, 0], [4, 3, 3, 3], [4, 3, 4, 1], [4, 3, 0, 4], [4, 3, 1, 2]]
  D2 := [[4, 3, 2, 2], [4, 3, 3, 0], [4, 3, 4, 3], [4, 3, 0, 1], [4, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_75_24 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T120_75
  T2 := Q2.T120_75_2
  h1 := (4,4,4,2,2)
  h2 := (4,4,4,2,4)
  D1 := [[4, 4, 2, 2], [4, 4, 3, 1], [4, 4, 4, 0], [4, 4, 0, 4], [4, 4, 1, 3]]
  D2 := [[4, 4, 2, 4], [4, 4, 3, 3], [4, 4, 4, 2], [4, 4, 0, 1], [4, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
