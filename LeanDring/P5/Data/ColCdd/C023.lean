/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C044

/-!
# Species-table cell data, stage 2 — column-data-divergent columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
cdd tier, chunk 22: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_147_28_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨28, by decide⟩
  m := 1
  T1 := T147_28
  T2 := Q2.T147_28_2
  h1 := (0,3,2,2,3)
  h2 := (0,3,2,2,2)
  D1 := [[0, 3, 2, 2, 2]]
  D2 := [[0, 3, 2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_28_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨28, by decide⟩
  m := 1
  T1 := T147_28
  T2 := Q2.T147_28_2
  h1 := (0,4,1,1,2)
  h2 := (0,4,1,1,4)
  D1 := [[0, 4, 1, 1, 3]]
  D2 := [[0, 4, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_29_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨29, by decide⟩
  m := 1
  T1 := T147_29
  T2 := Q2.T147_29_2
  h1 := (2,3,2,0,4)
  h2 := (2,3,2,0,0)
  D1 := [[2, 3, 2, 4, 2]]
  D2 := [[2, 3, 2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_29_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨29, by decide⟩
  m := 1
  T1 := T147_29
  T2 := Q2.T147_29_2
  h1 := (3,2,3,1,1)
  h2 := (3,2,3,1,3)
  D1 := [[3, 2, 3, 0, 4]]
  D2 := [[3, 2, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_29_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨29, by decide⟩
  m := 1
  T1 := T147_29
  T2 := Q2.T147_29_2
  h1 := (4,1,4,1,3)
  h2 := (4,1,4,1,1)
  D1 := [[4, 1, 4, 2, 0]]
  D2 := [[4, 1, 4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_30_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨30, by decide⟩
  m := 1
  T1 := T147_30
  T2 := Q2.T147_30_2
  h1 := (1,2,3,2,3)
  h2 := (1,2,3,2,0)
  D1 := [[1, 2, 3, 0, 2]]
  D2 := [[1, 2, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_30_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨30, by decide⟩
  m := 1
  T1 := T147_30
  T2 := Q2.T147_30_2
  h1 := (2,4,1,1,4)
  h2 := (2,4,1,1,3)
  D1 := [[2, 4, 1, 3, 0]]
  D2 := [[2, 4, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_30_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨30, by decide⟩
  m := 1
  T1 := T147_30
  T2 := Q2.T147_30_2
  h1 := (3,1,4,2,1)
  h2 := (3,1,4,2,3)
  D1 := [[3, 1, 4, 4, 2]]
  D2 := [[3, 1, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_30_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨30, by decide⟩
  m := 1
  T1 := T147_30
  T2 := Q2.T147_30_2
  h1 := (4,3,2,0,4)
  h2 := (4,3,2,0,3)
  D1 := [[4, 3, 2, 3, 3]]
  D2 := [[4, 3, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_31_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨31, by decide⟩
  m := 1
  T1 := T147_31
  T2 := Q2.T147_31_2
  h1 := (1,3,2,0,4)
  h2 := (1,3,2,0,0)
  D1 := [[1, 3, 2, 2, 1]]
  D2 := [[1, 3, 2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_31_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨31, by decide⟩
  m := 1
  T1 := T147_31
  T2 := Q2.T147_31_2
  h1 := (2,1,4,3,0)
  h2 := (2,1,4,3,3)
  D1 := [[2, 1, 4, 1, 3]]
  D2 := [[2, 1, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_31_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨31, by decide⟩
  m := 1
  T1 := T147_31
  T2 := Q2.T147_31_2
  h1 := (3,4,1,4,4)
  h2 := (3,4,1,4,3)
  D1 := [[3, 4, 1, 2, 2]]
  D2 := [[3, 4, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_31_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨31, by decide⟩
  m := 1
  T1 := T147_31
  T2 := Q2.T147_31_2
  h1 := (4,2,3,3,1)
  h2 := (4,2,3,3,2)
  D1 := [[4, 2, 3, 0, 3]]
  D2 := [[4, 2, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_32_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨32, by decide⟩
  m := 1
  T1 := T147_32
  T2 := Q2.T147_32_2
  h1 := (1,1,4,4,0)
  h2 := (1,1,4,4,3)
  D1 := [[1, 1, 4, 3, 3]]
  D2 := [[1, 1, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_32_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨32, by decide⟩
  m := 1
  T1 := T147_32
  T2 := Q2.T147_32_2
  h1 := (2,2,3,4,3)
  h2 := (2,2,3,4,4)
  D1 := [[2, 2, 3, 0, 0]]
  D2 := [[2, 2, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_32_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨32, by decide⟩
  m := 1
  T1 := T147_32
  T2 := Q2.T147_32_2
  h1 := (3,3,2,0,0)
  h2 := (3,3,2,0,4)
  D1 := [[3, 3, 2, 1, 2]]
  D2 := [[3, 3, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_32_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨32, by decide⟩
  m := 1
  T1 := T147_32
  T2 := Q2.T147_32_2
  h1 := (4,4,1,2,2)
  h2 := (4,4,1,2,4)
  D1 := [[4, 4, 1, 1, 0]]
  D2 := [[4, 4, 1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_33_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨33, by decide⟩
  m := 1
  T1 := T147_33
  T2 := Q2.T147_33_2
  h1 := (0,1,2,4,0)
  h2 := (0,1,2,4,3)
  D1 := [[0, 1, 2, 4, 3]]
  D2 := [[0, 1, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_33_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨33, by decide⟩
  m := 1
  T1 := T147_33
  T2 := Q2.T147_33_2
  h1 := (0,2,4,3,2)
  h2 := (0,2,4,3,3)
  D1 := [[0, 2, 4, 3, 4]]
  D2 := [[0, 2, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_33_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨33, by decide⟩
  m := 1
  T1 := T147_33
  T2 := Q2.T147_33_2
  h1 := (0,3,1,2,1)
  h2 := (0,3,1,2,0)
  D1 := [[0, 3, 1, 2, 3]]
  D2 := [[0, 3, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_33_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨33, by decide⟩
  m := 1
  T1 := T147_33
  T2 := Q2.T147_33_2
  h1 := (0,4,3,1,2)
  h2 := (0,4,3,1,4)
  D1 := [[0, 4, 3, 1, 0]]
  D2 := [[0, 4, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_34_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨34, by decide⟩
  m := 1
  T1 := T147_34
  T2 := Q2.T147_34_2
  h1 := (2,3,1,0,3)
  h2 := (2,3,1,0,4)
  D1 := [[2, 3, 1, 4, 4]]
  D2 := [[2, 3, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_34_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨34, by decide⟩
  m := 1
  T1 := T147_34
  T2 := Q2.T147_34_2
  h1 := (3,2,4,1,4)
  h2 := (3,2,4,1,1)
  D1 := [[3, 2, 4, 0, 0]]
  D2 := [[3, 2, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_34_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨34, by decide⟩
  m := 1
  T1 := T147_34
  T2 := Q2.T147_34_2
  h1 := (4,1,2,1,3)
  h2 := (4,1,2,1,1)
  D1 := [[4, 1, 2, 2, 2]]
  D2 := [[4, 1, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_35_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨35, by decide⟩
  m := 1
  T1 := T147_35
  T2 := Q2.T147_35_2
  h1 := (1,2,4,2,0)
  h2 := (1,2,4,2,2)
  D1 := [[1, 2, 4, 0, 2]]
  D2 := [[1, 2, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_35_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨35, by decide⟩
  m := 1
  T1 := T147_35
  T2 := Q2.T147_35_2
  h1 := (2,4,3,1,0)
  h2 := (2,4,3,1,4)
  D1 := [[2, 4, 3, 3, 3]]
  D2 := [[2, 4, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_35_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨35, by decide⟩
  m := 1
  T1 := T147_35
  T2 := Q2.T147_35_2
  h1 := (3,1,2,2,3)
  h2 := (3,1,2,2,0)
  D1 := [[3, 1, 2, 4, 1]]
  D2 := [[3, 1, 2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_35_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨35, by decide⟩
  m := 1
  T1 := T147_35
  T2 := Q2.T147_35_2
  h1 := (4,3,1,0,4)
  h2 := (4,3,1,0,3)
  D1 := [[4, 3, 1, 3, 1]]
  D2 := [[4, 3, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_36_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨36, by decide⟩
  m := 1
  T1 := T147_36
  T2 := Q2.T147_36_2
  h1 := (1,3,1,0,1)
  h2 := (1,3,1,0,2)
  D1 := [[1, 3, 1, 2, 1]]
  D2 := [[1, 3, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_36_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨36, by decide⟩
  m := 1
  T1 := T147_36
  T2 := Q2.T147_36_2
  h1 := (2,1,2,3,1)
  h2 := (2,1,2,3,4)
  D1 := [[2, 1, 2, 1, 1]]
  D2 := [[2, 1, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_36_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨36, by decide⟩
  m := 1
  T1 := T147_36
  T2 := Q2.T147_36_2
  h1 := (3,4,3,4,1)
  h2 := (3,4,3,4,0)
  D1 := [[3, 4, 3, 2, 1]]
  D2 := [[3, 4, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_36_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨36, by decide⟩
  m := 1
  T1 := T147_36
  T2 := Q2.T147_36_2
  h1 := (4,2,4,3,1)
  h2 := (4,2,4,3,2)
  D1 := [[4, 2, 4, 0, 1]]
  D2 := [[4, 2, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_37_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨37, by decide⟩
  m := 1
  T1 := T147_37
  T2 := Q2.T147_37_2
  h1 := (1,1,2,4,3)
  h2 := (1,1,2,4,1)
  D1 := [[1, 1, 2, 3, 3]]
  D2 := [[1, 1, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_37_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨37, by decide⟩
  m := 1
  T1 := T147_37
  T2 := Q2.T147_37_2
  h1 := (2,2,4,4,2)
  h2 := (2,2,4,4,3)
  D1 := [[2, 2, 4, 0, 2]]
  D2 := [[2, 2, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_37_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨37, by decide⟩
  m := 1
  T1 := T147_37
  T2 := Q2.T147_37_2
  h1 := (3,3,1,0,3)
  h2 := (3,3,1,0,2)
  D1 := [[3, 3, 1, 1, 3]]
  D2 := [[3, 3, 1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_37_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨37, by decide⟩
  m := 1
  T1 := T147_37
  T2 := Q2.T147_37_2
  h1 := (4,4,3,2,2)
  h2 := (4,4,3,2,4)
  D1 := [[4, 4, 3, 1, 2]]
  D2 := [[4, 4, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_38_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨38, by decide⟩
  m := 1
  T1 := T147_38
  T2 := Q2.T147_38_2
  h1 := (0,1,3,4,1)
  h2 := (0,1,3,4,4)
  D1 := [[0, 1, 3, 4, 3]]
  D2 := [[0, 1, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_38_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨38, by decide⟩
  m := 1
  T1 := T147_38
  T2 := Q2.T147_38_2
  h1 := (0,2,1,3,0)
  h2 := (0,2,1,3,1)
  D1 := [[0, 2, 1, 3, 3]]
  D2 := [[0, 2, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_38_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨38, by decide⟩
  m := 1
  T1 := T147_38
  T2 := Q2.T147_38_2
  h1 := (0,3,4,2,2)
  h2 := (0,3,4,2,1)
  D1 := [[0, 3, 4, 2, 0]]
  D2 := [[0, 3, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_38_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨38, by decide⟩
  m := 1
  T1 := T147_38
  T2 := Q2.T147_38_2
  h1 := (0,4,2,1,2)
  h2 := (0,4,2,1,4)
  D1 := [[0, 4, 2, 1, 4]]
  D2 := [[0, 4, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_39_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨39, by decide⟩
  m := 1
  T1 := T147_39
  T2 := Q2.T147_39_2
  h1 := (2,3,4,0,1)
  h2 := (2,3,4,0,2)
  D1 := [[2, 3, 4, 4, 3]]
  D2 := [[2, 3, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_39_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨39, by decide⟩
  m := 1
  T1 := T147_39
  T2 := Q2.T147_39_2
  h1 := (3,2,1,1,0)
  h2 := (3,2,1,1,2)
  D1 := [[3, 2, 1, 0, 2]]
  D2 := [[3, 2, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_39_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨39, by decide⟩
  m := 1
  T1 := T147_39
  T2 := Q2.T147_39_2
  h1 := (4,1,3,1,3)
  h2 := (4,1,3,1,1)
  D1 := [[4, 1, 3, 2, 1]]
  D2 := [[4, 1, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_40_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨40, by decide⟩
  m := 1
  T1 := T147_40
  T2 := Q2.T147_40_2
  h1 := (1,2,1,2,4)
  h2 := (1,2,1,2,1)
  D1 := [[1, 2, 1, 0, 2]]
  D2 := [[1, 2, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_40_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨40, by decide⟩
  m := 1
  T1 := T147_40
  T2 := Q2.T147_40_2
  h1 := (2,4,2,1,2)
  h2 := (2,4,2,1,1)
  D1 := [[2, 4, 2, 3, 4]]
  D2 := [[2, 4, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_40_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨40, by decide⟩
  m := 1
  T1 := T147_40
  T2 := Q2.T147_40_2
  h1 := (3,1,3,2,2)
  h2 := (3,1,3,2,4)
  D1 := [[3, 1, 3, 4, 4]]
  D2 := [[3, 1, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_40_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨40, by decide⟩
  m := 1
  T1 := T147_40
  T2 := Q2.T147_40_2
  h1 := (4,3,4,0,4)
  h2 := (4,3,4,0,3)
  D1 := [[4, 3, 4, 3, 2]]
  D2 := [[4, 3, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_41_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨41, by decide⟩
  m := 1
  T1 := T147_41
  T2 := Q2.T147_41_2
  h1 := (1,3,4,0,0)
  h2 := (1,3,4,0,1)
  D1 := [[1, 3, 4, 2, 1]]
  D2 := [[1, 3, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_41_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨41, by decide⟩
  m := 1
  T1 := T147_41
  T2 := Q2.T147_41_2
  h1 := (2,1,3,3,3)
  h2 := (2,1,3,3,1)
  D1 := [[2, 1, 3, 1, 2]]
  D2 := [[2, 1, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_41_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨41, by decide⟩
  m := 1
  T1 := T147_41
  T2 := Q2.T147_41_2
  h1 := (3,4,2,4,0)
  h2 := (3,4,2,4,4)
  D1 := [[3, 4, 2, 2, 4]]
  D2 := [[3, 4, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_41_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨41, by decide⟩
  m := 1
  T1 := T147_41
  T2 := Q2.T147_41_2
  h1 := (4,2,1,3,1)
  h2 := (4,2,1,3,2)
  D1 := [[4, 2, 1, 0, 2]]
  D2 := [[4, 2, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_42_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨42, by decide⟩
  m := 1
  T1 := T147_42
  T2 := Q2.T147_42_2
  h1 := (1,1,3,4,4)
  h2 := (1,1,3,4,2)
  D1 := [[1, 1, 3, 3, 3]]
  D2 := [[1, 1, 3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_42_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨42, by decide⟩
  m := 1
  T1 := T147_42
  T2 := Q2.T147_42_2
  h1 := (2,2,1,4,0)
  h2 := (2,2,1,4,1)
  D1 := [[2, 2, 1, 0, 1]]
  D2 := [[2, 2, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_42_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨42, by decide⟩
  m := 1
  T1 := T147_42
  T2 := Q2.T147_42_2
  h1 := (3,3,4,0,4)
  h2 := (3,3,4,0,3)
  D1 := [[3, 3, 4, 1, 0]]
  D2 := [[3, 3, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_42_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨42, by decide⟩
  m := 1
  T1 := T147_42
  T2 := Q2.T147_42_2
  h1 := (4,4,2,2,2)
  h2 := (4,4,2,2,4)
  D1 := [[4, 4, 2, 1, 1]]
  D2 := [[4, 4, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_43_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨43, by decide⟩
  m := 1
  T1 := T147_43
  T2 := Q2.T147_43_2
  h1 := (0,1,1,4,4)
  h2 := (0,1,1,4,2)
  D1 := [[0, 1, 1, 4, 3]]
  D2 := [[0, 1, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_43_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨43, by decide⟩
  m := 1
  T1 := T147_43
  T2 := Q2.T147_43_2
  h1 := (0,2,2,3,4)
  h2 := (0,2,2,3,0)
  D1 := [[0, 2, 2, 3, 0]]
  D2 := [[0, 2, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_43_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨43, by decide⟩
  m := 1
  T1 := T147_43
  T2 := Q2.T147_43_2
  h1 := (0,3,3,2,0)
  h2 := (0,3,3,2,4)
  D1 := [[0, 3, 3, 2, 1]]
  D2 := [[0, 3, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_43_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨43, by decide⟩
  m := 1
  T1 := T147_43
  T2 := Q2.T147_43_2
  h1 := (0,4,4,1,2)
  h2 := (0,4,4,1,4)
  D1 := [[0, 4, 4, 1, 1]]
  D2 := [[0, 4, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_44_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨44, by decide⟩
  m := 1
  T1 := T147_44
  T2 := Q2.T147_44_2
  h1 := (2,3,3,0,0)
  h2 := (2,3,3,0,1)
  D1 := [[2, 3, 3, 4, 0]]
  D2 := [[2, 3, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
