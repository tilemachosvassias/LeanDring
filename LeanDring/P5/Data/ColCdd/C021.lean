/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C041
import LeanDring.P5.Data.EntryK.C042

/-!
# Species-table cell data, stage 2 — column-data-divergent columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
cdd tier, chunk 20: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_143_33_5 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T143_33
  T2 := Q2.T143_33_2
  h1 := (0,1,2,4,0)
  h2 := (0,1,2,4,3)
  D1 := [[0, 1, 4, 4], [0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1], [0, 1, 4, 0]]
  D2 := [[0, 1, 4, 1], [0, 1, 4, 0], [0, 1, 4, 4], [0, 1, 4, 3], [0, 1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_33_10 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T143_33
  T2 := Q2.T143_33_2
  h1 := (0,2,4,3,2)
  h2 := (0,2,4,3,3)
  D1 := [[0, 2, 3, 3], [0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2], [0, 2, 3, 0]]
  D2 := [[0, 2, 3, 2], [0, 2, 3, 0], [0, 2, 3, 3], [0, 2, 3, 1], [0, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_33_15 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T143_33
  T2 := Q2.T143_33_2
  h1 := (0,3,1,2,1)
  h2 := (0,3,1,2,0)
  D1 := [[0, 3, 2, 2], [0, 3, 2, 4], [0, 3, 2, 1], [0, 3, 2, 3], [0, 3, 2, 0]]
  D2 := [[0, 3, 2, 3], [0, 3, 2, 0], [0, 3, 2, 2], [0, 3, 2, 4], [0, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_33_20 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T143_33
  T2 := Q2.T143_33_2
  h1 := (0,4,3,1,2)
  h2 := (0,4,3,1,4)
  D1 := [[0, 4, 1, 1], [0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4], [0, 4, 1, 0]]
  D2 := [[0, 4, 1, 4], [0, 4, 1, 0], [0, 4, 1, 1], [0, 4, 1, 2], [0, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_34_5 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T143_34
  T2 := Q2.T143_34_2
  h1 := (1,4,3,3,1)
  h2 := (1,4,3,3,1)
  D1 := [[1, 4, 4, 1], [1, 4, 4, 2], [1, 4, 4, 3], [1, 4, 4, 4], [1, 4, 4, 0]]
  D2 := [[1, 4, 4, 2], [1, 4, 4, 3], [1, 4, 4, 4], [1, 4, 4, 0], [1, 4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_34_10 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T143_34
  T2 := Q2.T143_34_2
  h1 := (2,3,1,0,3)
  h2 := (2,3,1,0,4)
  D1 := [[2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1]]
  D2 := [[2, 3, 4, 1], [2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_34_20 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T143_34
  T2 := Q2.T143_34_2
  h1 := (4,1,2,1,3)
  h2 := (4,1,2,1,1)
  D1 := [[4, 1, 2, 3], [4, 1, 2, 2], [4, 1, 2, 1], [4, 1, 2, 0], [4, 1, 2, 4]]
  D2 := [[4, 1, 2, 0], [4, 1, 2, 4], [4, 1, 2, 3], [4, 1, 2, 2], [4, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_35_15 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T143_35
  T2 := Q2.T143_35_2
  h1 := (3,1,2,2,3)
  h2 := (3,1,2,2,0)
  D1 := [[3, 1, 4, 2], [3, 1, 4, 1], [3, 1, 4, 0], [3, 1, 4, 4], [3, 1, 4, 3]]
  D2 := [[3, 1, 4, 3], [3, 1, 4, 2], [3, 1, 4, 1], [3, 1, 4, 0], [3, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_35_20 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T143_35
  T2 := Q2.T143_35_2
  h1 := (4,3,1,0,4)
  h2 := (4,3,1,0,3)
  D1 := [[4, 3, 3, 0], [4, 3, 3, 2], [4, 3, 3, 4], [4, 3, 3, 1], [4, 3, 3, 3]]
  D2 := [[4, 3, 3, 1], [4, 3, 3, 3], [4, 3, 3, 0], [4, 3, 3, 2], [4, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_36_5 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T143_36
  T2 := Q2.T143_36_2
  h1 := (1,3,1,0,1)
  h2 := (1,3,1,0,2)
  D1 := [[1, 3, 2, 0], [1, 3, 2, 2], [1, 3, 2, 4], [1, 3, 2, 1], [1, 3, 2, 3]]
  D2 := [[1, 3, 2, 3], [1, 3, 2, 0], [1, 3, 2, 2], [1, 3, 2, 4], [1, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_36_10 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T143_36
  T2 := Q2.T143_36_2
  h1 := (2,1,2,3,1)
  h2 := (2,1,2,3,4)
  D1 := [[2, 1, 1, 2], [2, 1, 1, 1], [2, 1, 1, 0], [2, 1, 1, 4], [2, 1, 1, 3]]
  D2 := [[2, 1, 1, 4], [2, 1, 1, 3], [2, 1, 1, 2], [2, 1, 1, 1], [2, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_36_20 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T143_36
  T2 := Q2.T143_36_2
  h1 := (4,2,4,3,1)
  h2 := (4,2,4,3,2)
  D1 := [[4, 2, 0, 0], [4, 2, 0, 3], [4, 2, 0, 1], [4, 2, 0, 4], [4, 2, 0, 2]]
  D2 := [[4, 2, 0, 4], [4, 2, 0, 2], [4, 2, 0, 0], [4, 2, 0, 3], [4, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_37_5 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T143_37
  T2 := Q2.T143_37_2
  h1 := (1,1,2,4,3)
  h2 := (1,1,2,4,1)
  D1 := [[1, 1, 3, 4], [1, 1, 3, 3], [1, 1, 3, 2], [1, 1, 3, 1], [1, 1, 3, 0]]
  D2 := [[1, 1, 3, 1], [1, 1, 3, 0], [1, 1, 3, 4], [1, 1, 3, 3], [1, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_37_10 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T143_37
  T2 := Q2.T143_37_2
  h1 := (2,2,4,4,2)
  h2 := (2,2,4,4,3)
  D1 := [[2, 2, 0, 1], [2, 2, 0, 4], [2, 2, 0, 2], [2, 2, 0, 0], [2, 2, 0, 3]]
  D2 := [[2, 2, 0, 0], [2, 2, 0, 3], [2, 2, 0, 1], [2, 2, 0, 4], [2, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_37_15 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T143_37
  T2 := Q2.T143_37_2
  h1 := (3,3,1,0,3)
  h2 := (3,3,1,0,2)
  D1 := [[3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0]]
  D2 := [[3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_37_20 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T143_37
  T2 := Q2.T143_37_2
  h1 := (4,4,3,2,2)
  h2 := (4,4,3,2,4)
  D1 := [[4, 4, 1, 3], [4, 4, 1, 4], [4, 4, 1, 0], [4, 4, 1, 1], [4, 4, 1, 2]]
  D2 := [[4, 4, 1, 1], [4, 4, 1, 2], [4, 4, 1, 3], [4, 4, 1, 4], [4, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_95_25 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T143_95
  T2 := Q2.T143_95_2
  h1 := (0,1,2,0,0)
  h2 := (0,1,2,0,0)
  D1 := [[0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0]]
  D2 := [[0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_95_50 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T143_95
  T2 := Q2.T143_95_2
  h1 := (0,2,4,0,2)
  h2 := (0,2,4,0,2)
  D1 := [[0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0]]
  D2 := [[0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_95_75 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T143_95
  T2 := Q2.T143_95_2
  h1 := (0,3,1,0,1)
  h2 := (0,3,1,0,1)
  D1 := [[0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0]]
  D2 := [[0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_95_100 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T143_95
  T2 := Q2.T143_95_2
  h1 := (0,4,3,0,2)
  h2 := (0,4,3,0,2)
  D1 := [[0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0]]
  D2 := [[0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_96_5 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T143_96
  T2 := Q2.T143_96_2
  h1 := (1,4,3,4,2)
  h2 := (1,4,3,4,2)
  D1 := [[1, 4, 0, 1], [1, 4, 0, 2], [1, 4, 0, 3], [1, 4, 0, 4], [1, 4, 0, 0]]
  D2 := [[1, 4, 0, 2], [1, 4, 0, 3], [1, 4, 0, 4], [1, 4, 0, 0], [1, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_96_10 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T143_96
  T2 := Q2.T143_96_2
  h1 := (2,3,1,2,1)
  h2 := (2,3,1,2,2)
  D1 := [[2, 3, 1, 2], [2, 3, 1, 4], [2, 3, 1, 1], [2, 3, 1, 3], [2, 3, 1, 0]]
  D2 := [[2, 3, 1, 0], [2, 3, 1, 2], [2, 3, 1, 4], [2, 3, 1, 1], [2, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_96_20 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T143_96
  T2 := Q2.T143_96_2
  h1 := (4,1,2,0,3)
  h2 := (4,1,2,0,1)
  D1 := [[4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4], [4, 1, 1, 3]]
  D2 := [[4, 1, 1, 4], [4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_97_5 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T143_97
  T2 := Q2.T143_97_2
  h1 := (1,2,4,3,0)
  h2 := (1,2,4,3,0)
  D1 := [[1, 2, 1, 0], [1, 2, 1, 3], [1, 2, 1, 1], [1, 2, 1, 4], [1, 2, 1, 2]]
  D2 := [[1, 2, 1, 3], [1, 2, 1, 1], [1, 2, 1, 4], [1, 2, 1, 2], [1, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_97_10 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T143_97
  T2 := Q2.T143_97_2
  h1 := (2,4,3,3,1)
  h2 := (2,4,3,3,1)
  D1 := [[2, 4, 0, 1], [2, 4, 0, 2], [2, 4, 0, 3], [2, 4, 0, 4], [2, 4, 0, 0]]
  D2 := [[2, 4, 0, 2], [2, 4, 0, 3], [2, 4, 0, 4], [2, 4, 0, 0], [2, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_97_20 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T143_97
  T2 := Q2.T143_97_2
  h1 := (4,3,1,4,0)
  h2 := (4,3,1,4,1)
  D1 := [[4, 3, 2, 0], [4, 3, 2, 2], [4, 3, 2, 4], [4, 3, 2, 1], [4, 3, 2, 3]]
  D2 := [[4, 3, 2, 3], [4, 3, 2, 0], [4, 3, 2, 2], [4, 3, 2, 4], [4, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_98_5 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T143_98
  T2 := Q2.T143_98_2
  h1 := (1,3,1,1,3)
  h2 := (1,3,1,1,3)
  D1 := [[1, 3, 3, 1], [1, 3, 3, 3], [1, 3, 3, 0], [1, 3, 3, 2], [1, 3, 3, 4]]
  D2 := [[1, 3, 3, 3], [1, 3, 3, 0], [1, 3, 3, 2], [1, 3, 3, 4], [1, 3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_98_15 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T143_98
  T2 := Q2.T143_98_2
  h1 := (3,4,3,2,0)
  h2 := (3,4,3,2,1)
  D1 := [[3, 4, 0, 2], [3, 4, 0, 3], [3, 4, 0, 4], [3, 4, 0, 0], [3, 4, 0, 1]]
  D2 := [[3, 4, 0, 4], [3, 4, 0, 0], [3, 4, 0, 1], [3, 4, 0, 2], [3, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_99_5 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T143_99
  T2 := Q2.T143_99_2
  h1 := (1,1,2,0,0)
  h2 := (1,1,2,0,0)
  D1 := [[1, 1, 4, 0], [1, 1, 4, 4], [1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1]]
  D2 := [[1, 1, 4, 4], [1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1], [1, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_99_10 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T143_99
  T2 := Q2.T143_99_2
  h1 := (2,2,4,1,2)
  h2 := (2,2,4,1,2)
  D1 := [[2, 2, 2, 2], [2, 2, 2, 0], [2, 2, 2, 3], [2, 2, 2, 1], [2, 2, 2, 4]]
  D2 := [[2, 2, 2, 0], [2, 2, 2, 3], [2, 2, 2, 1], [2, 2, 2, 4], [2, 2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_99_15 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T143_99
  T2 := Q2.T143_99_2
  h1 := (3,3,1,3,2)
  h2 := (3,3,1,3,2)
  D1 := [[3, 3, 4, 2], [3, 3, 4, 4], [3, 3, 4, 1], [3, 3, 4, 3], [3, 3, 4, 0]]
  D2 := [[3, 3, 4, 4], [3, 3, 4, 1], [3, 3, 4, 3], [3, 3, 4, 0], [3, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_143_99_20 : ColCertDiv where
  rK := ⟨143, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T143_99
  T2 := Q2.T143_99_2
  h1 := (4,4,3,1,1)
  h2 := (4,4,3,1,1)
  D1 := [[4, 4, 0, 1], [4, 4, 0, 2], [4, 4, 0, 3], [4, 4, 0, 4], [4, 4, 0, 0]]
  D2 := [[4, 4, 0, 2], [4, 4, 0, 3], [4, 4, 0, 4], [4, 4, 0, 0], [4, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_144_38_5 : ColCertDiv where
  rK := ⟨144, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T144_38
  T2 := Q2.T144_38_2
  h1 := (0,1,3,4,1)
  h2 := (0,1,3,4,4)
  D1 := [[0, 1, 4, 1], [0, 1, 4, 0], [0, 1, 4, 4], [0, 1, 4, 3], [0, 1, 4, 2]]
  D2 := [[0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1], [0, 1, 4, 0], [0, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_144_38_10 : ColCertDiv where
  rK := ⟨144, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T144_38
  T2 := Q2.T144_38_2
  h1 := (0,2,1,3,0)
  h2 := (0,2,1,3,1)
  D1 := [[0, 2, 3, 2], [0, 2, 3, 0], [0, 2, 3, 3], [0, 2, 3, 1], [0, 2, 3, 4]]
  D2 := [[0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2], [0, 2, 3, 0], [0, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_144_38_15 : ColCertDiv where
  rK := ⟨144, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T144_38
  T2 := Q2.T144_38_2
  h1 := (0,3,4,2,2)
  h2 := (0,3,4,2,1)
  D1 := [[0, 3, 2, 3], [0, 3, 2, 0], [0, 3, 2, 2], [0, 3, 2, 4], [0, 3, 2, 1]]
  D2 := [[0, 3, 2, 4], [0, 3, 2, 1], [0, 3, 2, 3], [0, 3, 2, 0], [0, 3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_144_38_20 : ColCertDiv where
  rK := ⟨144, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T144_38
  T2 := Q2.T144_38_2
  h1 := (0,4,2,1,2)
  h2 := (0,4,2,1,4)
  D1 := [[0, 4, 1, 4], [0, 4, 1, 0], [0, 4, 1, 1], [0, 4, 1, 2], [0, 4, 1, 3]]
  D2 := [[0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4], [0, 4, 1, 0], [0, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_144_39_5 : ColCertDiv where
  rK := ⟨144, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T144_39
  T2 := Q2.T144_39_2
  h1 := (1,4,2,3,2)
  h2 := (1,4,2,3,2)
  D1 := [[1, 4, 4, 0], [1, 4, 4, 1], [1, 4, 4, 2], [1, 4, 4, 3], [1, 4, 4, 4]]
  D2 := [[1, 4, 4, 1], [1, 4, 4, 2], [1, 4, 4, 3], [1, 4, 4, 4], [1, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_144_39_10 : ColCertDiv where
  rK := ⟨144, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T144_39
  T2 := Q2.T144_39_2
  h1 := (2,3,4,0,1)
  h2 := (2,3,4,0,2)
  D1 := [[2, 3, 4, 1], [2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4]]
  D2 := [[2, 3, 4, 4], [2, 3, 4, 1], [2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_144_39_20 : ColCertDiv where
  rK := ⟨144, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T144_39
  T2 := Q2.T144_39_2
  h1 := (4,1,3,1,3)
  h2 := (4,1,3,1,1)
  D1 := [[4, 1, 2, 4], [4, 1, 2, 3], [4, 1, 2, 2], [4, 1, 2, 1], [4, 1, 2, 0]]
  D2 := [[4, 1, 2, 1], [4, 1, 2, 0], [4, 1, 2, 4], [4, 1, 2, 3], [4, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_144_40_15 : ColCertDiv where
  rK := ⟨144, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T144_40
  T2 := Q2.T144_40_2
  h1 := (3,1,3,2,2)
  h2 := (3,1,3,2,4)
  D1 := [[3, 1, 4, 2], [3, 1, 4, 1], [3, 1, 4, 0], [3, 1, 4, 4], [3, 1, 4, 3]]
  D2 := [[3, 1, 4, 3], [3, 1, 4, 2], [3, 1, 4, 1], [3, 1, 4, 0], [3, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_144_40_20 : ColCertDiv where
  rK := ⟨144, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T144_40
  T2 := Q2.T144_40_2
  h1 := (4,3,4,0,4)
  h2 := (4,3,4,0,3)
  D1 := [[4, 3, 3, 0], [4, 3, 3, 2], [4, 3, 3, 4], [4, 3, 3, 1], [4, 3, 3, 3]]
  D2 := [[4, 3, 3, 1], [4, 3, 3, 3], [4, 3, 3, 0], [4, 3, 3, 2], [4, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_144_41_5 : ColCertDiv where
  rK := ⟨144, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T144_41
  T2 := Q2.T144_41_2
  h1 := (1,3,4,0,0)
  h2 := (1,3,4,0,1)
  D1 := [[1, 3, 2, 4], [1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0], [1, 3, 2, 2]]
  D2 := [[1, 3, 2, 2], [1, 3, 2, 4], [1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_144_41_10 : ColCertDiv where
  rK := ⟨144, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T144_41
  T2 := Q2.T144_41_2
  h1 := (2,1,3,3,3)
  h2 := (2,1,3,3,1)
  D1 := [[2, 1, 1, 0], [2, 1, 1, 4], [2, 1, 1, 3], [2, 1, 1, 2], [2, 1, 1, 1]]
  D2 := [[2, 1, 1, 2], [2, 1, 1, 1], [2, 1, 1, 0], [2, 1, 1, 4], [2, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_144_41_20 : ColCertDiv where
  rK := ⟨144, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T144_41
  T2 := Q2.T144_41_2
  h1 := (4,2,1,3,1)
  h2 := (4,2,1,3,2)
  D1 := [[4, 2, 0, 1], [4, 2, 0, 4], [4, 2, 0, 2], [4, 2, 0, 0], [4, 2, 0, 3]]
  D2 := [[4, 2, 0, 0], [4, 2, 0, 3], [4, 2, 0, 1], [4, 2, 0, 4], [4, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_144_42_5 : ColCertDiv where
  rK := ⟨144, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T144_42
  T2 := Q2.T144_42_2
  h1 := (1,1,3,4,4)
  h2 := (1,1,3,4,2)
  D1 := [[1, 1, 3, 1], [1, 1, 3, 0], [1, 1, 3, 4], [1, 1, 3, 3], [1, 1, 3, 2]]
  D2 := [[1, 1, 3, 3], [1, 1, 3, 2], [1, 1, 3, 1], [1, 1, 3, 0], [1, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_144_42_10 : ColCertDiv where
  rK := ⟨144, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T144_42
  T2 := Q2.T144_42_2
  h1 := (2,2,1,4,0)
  h2 := (2,2,1,4,1)
  D1 := [[2, 2, 0, 0], [2, 2, 0, 3], [2, 2, 0, 1], [2, 2, 0, 4], [2, 2, 0, 2]]
  D2 := [[2, 2, 0, 4], [2, 2, 0, 2], [2, 2, 0, 0], [2, 2, 0, 3], [2, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_144_42_15 : ColCertDiv where
  rK := ⟨144, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T144_42
  T2 := Q2.T144_42_2
  h1 := (3,3,4,0,4)
  h2 := (3,3,4,0,3)
  D1 := [[3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1]]
  D2 := [[3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_144_42_20 : ColCertDiv where
  rK := ⟨144, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T144_42
  T2 := Q2.T144_42_2
  h1 := (4,4,2,2,2)
  h2 := (4,4,2,2,4)
  D1 := [[4, 4, 1, 1], [4, 4, 1, 2], [4, 4, 1, 3], [4, 4, 1, 4], [4, 4, 1, 0]]
  D2 := [[4, 4, 1, 4], [4, 4, 1, 0], [4, 4, 1, 1], [4, 4, 1, 2], [4, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_144_100_25 : ColCertDiv where
  rK := ⟨144, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T144_100
  T2 := Q2.T144_100_2
  h1 := (0,1,3,0,0)
  h2 := (0,1,3,0,0)
  D1 := [[0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1]]
  D2 := [[0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_144_100_50 : ColCertDiv where
  rK := ⟨144, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T144_100
  T2 := Q2.T144_100_2
  h1 := (0,2,1,0,3)
  h2 := (0,2,1,0,3)
  D1 := [[0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2]]
  D2 := [[0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_144_100_75 : ColCertDiv where
  rK := ⟨144, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T144_100
  T2 := Q2.T144_100_2
  h1 := (0,3,4,0,4)
  h2 := (0,3,4,0,4)
  D1 := [[0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3]]
  D2 := [[0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_144_100_100 : ColCertDiv where
  rK := ⟨144, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T144_100
  T2 := Q2.T144_100_2
  h1 := (0,4,2,0,3)
  h2 := (0,4,2,0,3)
  D1 := [[0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4]]
  D2 := [[0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_144_101_5 : ColCertDiv where
  rK := ⟨144, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T144_101
  T2 := Q2.T144_101_2
  h1 := (1,4,2,4,3)
  h2 := (1,4,2,4,3)
  D1 := [[1, 4, 0, 0], [1, 4, 0, 1], [1, 4, 0, 2], [1, 4, 0, 3], [1, 4, 0, 4]]
  D2 := [[1, 4, 0, 1], [1, 4, 0, 2], [1, 4, 0, 3], [1, 4, 0, 4], [1, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_144_101_10 : ColCertDiv where
  rK := ⟨144, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T144_101
  T2 := Q2.T144_101_2
  h1 := (2,3,4,2,4)
  h2 := (2,3,4,2,0)
  D1 := [[2, 3, 1, 0], [2, 3, 1, 2], [2, 3, 1, 4], [2, 3, 1, 1], [2, 3, 1, 3]]
  D2 := [[2, 3, 1, 3], [2, 3, 1, 0], [2, 3, 1, 2], [2, 3, 1, 4], [2, 3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_144_101_20 : ColCertDiv where
  rK := ⟨144, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T144_101
  T2 := Q2.T144_101_2
  h1 := (4,1,3,0,3)
  h2 := (4,1,3,0,1)
  D1 := [[4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4]]
  D2 := [[4, 1, 1, 0], [4, 1, 1, 4], [4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_144_102_5 : ColCertDiv where
  rK := ⟨144, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T144_102
  T2 := Q2.T144_102_2
  h1 := (1,2,1,3,1)
  h2 := (1,2,1,3,1)
  D1 := [[1, 2, 1, 2], [1, 2, 1, 0], [1, 2, 1, 3], [1, 2, 1, 1], [1, 2, 1, 4]]
  D2 := [[1, 2, 1, 0], [1, 2, 1, 3], [1, 2, 1, 1], [1, 2, 1, 4], [1, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_144_102_10 : ColCertDiv where
  rK := ⟨144, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T144_102
  T2 := Q2.T144_102_2
  h1 := (2,4,2,3,2)
  h2 := (2,4,2,3,2)
  D1 := [[2, 4, 0, 0], [2, 4, 0, 1], [2, 4, 0, 2], [2, 4, 0, 3], [2, 4, 0, 4]]
  D2 := [[2, 4, 0, 1], [2, 4, 0, 2], [2, 4, 0, 3], [2, 4, 0, 4], [2, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_144_102_20 : ColCertDiv where
  rK := ⟨144, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T144_102
  T2 := Q2.T144_102_2
  h1 := (4,3,4,4,3)
  h2 := (4,3,4,4,4)
  D1 := [[4, 3, 2, 3], [4, 3, 2, 0], [4, 3, 2, 2], [4, 3, 2, 4], [4, 3, 2, 1]]
  D2 := [[4, 3, 2, 1], [4, 3, 2, 3], [4, 3, 2, 0], [4, 3, 2, 2], [4, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_144_103_5 : ColCertDiv where
  rK := ⟨144, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T144_103
  T2 := Q2.T144_103_2
  h1 := (1,3,4,1,1)
  h2 := (1,3,4,1,1)
  D1 := [[1, 3, 3, 4], [1, 3, 3, 1], [1, 3, 3, 3], [1, 3, 3, 0], [1, 3, 3, 2]]
  D2 := [[1, 3, 3, 1], [1, 3, 3, 3], [1, 3, 3, 0], [1, 3, 3, 2], [1, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_144_103_15 : ColCertDiv where
  rK := ⟨144, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T144_103
  T2 := Q2.T144_103_2
  h1 := (3,4,2,2,1)
  h2 := (3,4,2,2,2)
  D1 := [[3, 4, 0, 1], [3, 4, 0, 2], [3, 4, 0, 3], [3, 4, 0, 4], [3, 4, 0, 0]]
  D2 := [[3, 4, 0, 3], [3, 4, 0, 4], [3, 4, 0, 0], [3, 4, 0, 1], [3, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
