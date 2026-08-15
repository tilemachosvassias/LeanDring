/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C027

/-!
# Species-table cell data, stage 2 — column-data-divergent columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
cdd tier, chunk 3: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_118_50_5 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T118_50
  T2 := Q2.T118_50_2
  h1 := (1,2,0,2,2)
  h2 := (1,2,0,2,4)
  D1 := [[1, 0, 2, 2], [1, 0, 1, 3], [1, 0, 0, 4], [1, 0, 4, 0], [1, 0, 3, 1]]
  D2 := [[1, 0, 2, 4], [1, 0, 1, 0], [1, 0, 0, 1], [1, 0, 4, 2], [1, 0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_50_10 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T118_50
  T2 := Q2.T118_50_2
  h1 := (2,4,0,1,1)
  h2 := (2,4,0,1,0)
  D1 := [[2, 0, 4, 2], [2, 0, 2, 0], [2, 0, 0, 3], [2, 0, 3, 1], [2, 0, 1, 4]]
  D2 := [[2, 0, 4, 1], [2, 0, 2, 4], [2, 0, 0, 2], [2, 0, 3, 0], [2, 0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_50_15 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T118_50
  T2 := Q2.T118_50_2
  h1 := (3,1,0,2,0)
  h2 := (3,1,0,2,2)
  D1 := [[3, 0, 1, 0], [3, 0, 3, 1], [3, 0, 0, 2], [3, 0, 2, 3], [3, 0, 4, 4]]
  D2 := [[3, 0, 1, 1], [3, 0, 3, 2], [3, 0, 0, 3], [3, 0, 2, 4], [3, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_50_20 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T118_50
  T2 := Q2.T118_50_2
  h1 := (4,3,0,0,4)
  h2 := (4,3,0,0,3)
  D1 := [[4, 0, 3, 1], [4, 0, 4, 1], [4, 0, 0, 1], [4, 0, 1, 1], [4, 0, 2, 1]]
  D2 := [[4, 0, 3, 4], [4, 0, 4, 4], [4, 0, 0, 4], [4, 0, 1, 4], [4, 0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_65_5 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨65, by decide⟩
  m := 5
  T1 := T118_65
  T2 := Q2.T118_65_2
  h1 := (1,2,0,2,2)
  h2 := (1,2,0,2,4)
  D1 := [[1, 0, 2, 2], [1, 0, 1, 3], [1, 0, 0, 4], [1, 0, 4, 0], [1, 0, 3, 1]]
  D2 := [[1, 0, 2, 4], [1, 0, 1, 0], [1, 0, 0, 1], [1, 0, 4, 2], [1, 0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_65_6 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨65, by decide⟩
  m := 5
  T1 := T118_65
  T2 := Q2.T118_65_2
  h1 := (1,2,1,2,2)
  h2 := (1,2,1,2,4)
  D1 := [[1, 1, 2, 2], [1, 1, 1, 4], [1, 1, 0, 1], [1, 1, 4, 3], [1, 1, 3, 0]]
  D2 := [[1, 1, 2, 4], [1, 1, 1, 1], [1, 1, 0, 3], [1, 1, 4, 0], [1, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_65_7 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨65, by decide⟩
  m := 5
  T1 := T118_65
  T2 := Q2.T118_65_2
  h1 := (1,2,2,2,2)
  h2 := (1,2,2,2,4)
  D1 := [[1, 2, 2, 2], [1, 2, 1, 0], [1, 2, 0, 3], [1, 2, 4, 1], [1, 2, 3, 4]]
  D2 := [[1, 2, 2, 4], [1, 2, 1, 2], [1, 2, 0, 0], [1, 2, 4, 3], [1, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_65_8 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨65, by decide⟩
  m := 5
  T1 := T118_65
  T2 := Q2.T118_65_2
  h1 := (1,2,3,2,2)
  h2 := (1,2,3,2,4)
  D1 := [[1, 3, 2, 2], [1, 3, 1, 1], [1, 3, 0, 0], [1, 3, 4, 4], [1, 3, 3, 3]]
  D2 := [[1, 3, 2, 4], [1, 3, 1, 3], [1, 3, 0, 2], [1, 3, 4, 1], [1, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_65_9 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨65, by decide⟩
  m := 5
  T1 := T118_65
  T2 := Q2.T118_65_2
  h1 := (1,2,4,2,2)
  h2 := (1,2,4,2,4)
  D1 := [[1, 4, 2, 2], [1, 4, 1, 2], [1, 4, 0, 2], [1, 4, 4, 2], [1, 4, 3, 2]]
  D2 := [[1, 4, 2, 4], [1, 4, 1, 4], [1, 4, 0, 4], [1, 4, 4, 4], [1, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_65_10 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨65, by decide⟩
  m := 5
  T1 := T118_65
  T2 := Q2.T118_65_2
  h1 := (2,4,0,1,1)
  h2 := (2,4,0,1,0)
  D1 := [[2, 0, 4, 2], [2, 0, 2, 0], [2, 0, 0, 3], [2, 0, 3, 1], [2, 0, 1, 4]]
  D2 := [[2, 0, 4, 1], [2, 0, 2, 4], [2, 0, 0, 2], [2, 0, 3, 0], [2, 0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_65_11 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨65, by decide⟩
  m := 5
  T1 := T118_65
  T2 := Q2.T118_65_2
  h1 := (2,4,1,1,1)
  h2 := (2,4,1,1,0)
  D1 := [[2, 1, 4, 0], [2, 1, 2, 4], [2, 1, 0, 3], [2, 1, 3, 2], [2, 1, 1, 1]]
  D2 := [[2, 1, 4, 4], [2, 1, 2, 3], [2, 1, 0, 2], [2, 1, 3, 1], [2, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_65_12 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨65, by decide⟩
  m := 5
  T1 := T118_65
  T2 := Q2.T118_65_2
  h1 := (2,4,2,1,1)
  h2 := (2,4,2,1,0)
  D1 := [[2, 2, 4, 3], [2, 2, 2, 3], [2, 2, 0, 3], [2, 2, 3, 3], [2, 2, 1, 3]]
  D2 := [[2, 2, 4, 2], [2, 2, 2, 2], [2, 2, 0, 2], [2, 2, 3, 2], [2, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_65_13 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨65, by decide⟩
  m := 5
  T1 := T118_65
  T2 := Q2.T118_65_2
  h1 := (2,4,3,1,1)
  h2 := (2,4,3,1,0)
  D1 := [[2, 3, 4, 1], [2, 3, 2, 2], [2, 3, 0, 3], [2, 3, 3, 4], [2, 3, 1, 0]]
  D2 := [[2, 3, 4, 0], [2, 3, 2, 1], [2, 3, 0, 2], [2, 3, 3, 3], [2, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_65_14 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨65, by decide⟩
  m := 5
  T1 := T118_65
  T2 := Q2.T118_65_2
  h1 := (2,4,4,1,1)
  h2 := (2,4,4,1,0)
  D1 := [[2, 4, 4, 4], [2, 4, 2, 1], [2, 4, 0, 3], [2, 4, 3, 0], [2, 4, 1, 2]]
  D2 := [[2, 4, 4, 3], [2, 4, 2, 0], [2, 4, 0, 2], [2, 4, 3, 4], [2, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_65_15 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨65, by decide⟩
  m := 5
  T1 := T118_65
  T2 := Q2.T118_65_2
  h1 := (3,1,0,2,0)
  h2 := (3,1,0,2,2)
  D1 := [[3, 0, 1, 0], [3, 0, 3, 1], [3, 0, 0, 2], [3, 0, 2, 3], [3, 0, 4, 4]]
  D2 := [[3, 0, 1, 1], [3, 0, 3, 2], [3, 0, 0, 3], [3, 0, 2, 4], [3, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_65_16 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨65, by decide⟩
  m := 5
  T1 := T118_65
  T2 := Q2.T118_65_2
  h1 := (3,1,1,2,0)
  h2 := (3,1,1,2,2)
  D1 := [[3, 1, 1, 1], [3, 1, 3, 3], [3, 1, 0, 0], [3, 1, 2, 2], [3, 1, 4, 4]]
  D2 := [[3, 1, 1, 2], [3, 1, 3, 4], [3, 1, 0, 1], [3, 1, 2, 3], [3, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_65_17 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨65, by decide⟩
  m := 5
  T1 := T118_65
  T2 := Q2.T118_65_2
  h1 := (3,1,2,2,0)
  h2 := (3,1,2,2,2)
  D1 := [[3, 2, 1, 2], [3, 2, 3, 0], [3, 2, 0, 3], [3, 2, 2, 1], [3, 2, 4, 4]]
  D2 := [[3, 2, 1, 3], [3, 2, 3, 1], [3, 2, 0, 4], [3, 2, 2, 2], [3, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_65_18 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨65, by decide⟩
  m := 5
  T1 := T118_65
  T2 := Q2.T118_65_2
  h1 := (3,1,3,2,0)
  h2 := (3,1,3,2,2)
  D1 := [[3, 3, 1, 3], [3, 3, 3, 2], [3, 3, 0, 1], [3, 3, 2, 0], [3, 3, 4, 4]]
  D2 := [[3, 3, 1, 4], [3, 3, 3, 3], [3, 3, 0, 2], [3, 3, 2, 1], [3, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_65_19 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨65, by decide⟩
  m := 5
  T1 := T118_65
  T2 := Q2.T118_65_2
  h1 := (3,1,4,2,0)
  h2 := (3,1,4,2,2)
  D1 := [[3, 4, 1, 4], [3, 4, 3, 4], [3, 4, 0, 4], [3, 4, 2, 4], [3, 4, 4, 4]]
  D2 := [[3, 4, 1, 0], [3, 4, 3, 0], [3, 4, 0, 0], [3, 4, 2, 0], [3, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_65_20 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨65, by decide⟩
  m := 5
  T1 := T118_65
  T2 := Q2.T118_65_2
  h1 := (4,3,0,0,4)
  h2 := (4,3,0,0,3)
  D1 := [[4, 0, 3, 1], [4, 0, 4, 1], [4, 0, 0, 1], [4, 0, 1, 1], [4, 0, 2, 1]]
  D2 := [[4, 0, 3, 4], [4, 0, 4, 4], [4, 0, 0, 4], [4, 0, 1, 4], [4, 0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_65_21 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨65, by decide⟩
  m := 5
  T1 := T118_65
  T2 := Q2.T118_65_2
  h1 := (4,3,1,0,4)
  h2 := (4,3,1,0,3)
  D1 := [[4, 1, 3, 0], [4, 1, 4, 1], [4, 1, 0, 2], [4, 1, 1, 3], [4, 1, 2, 4]]
  D2 := [[4, 1, 3, 3], [4, 1, 4, 4], [4, 1, 0, 0], [4, 1, 1, 1], [4, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_65_22 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨65, by decide⟩
  m := 5
  T1 := T118_65
  T2 := Q2.T118_65_2
  h1 := (4,3,2,0,4)
  h2 := (4,3,2,0,3)
  D1 := [[4, 2, 3, 4], [4, 2, 4, 1], [4, 2, 0, 3], [4, 2, 1, 0], [4, 2, 2, 2]]
  D2 := [[4, 2, 3, 2], [4, 2, 4, 4], [4, 2, 0, 1], [4, 2, 1, 3], [4, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_65_23 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨65, by decide⟩
  m := 5
  T1 := T118_65
  T2 := Q2.T118_65_2
  h1 := (4,3,3,0,4)
  h2 := (4,3,3,0,3)
  D1 := [[4, 3, 3, 3], [4, 3, 4, 1], [4, 3, 0, 4], [4, 3, 1, 2], [4, 3, 2, 0]]
  D2 := [[4, 3, 3, 1], [4, 3, 4, 4], [4, 3, 0, 2], [4, 3, 1, 0], [4, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_65_24 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨65, by decide⟩
  m := 5
  T1 := T118_65
  T2 := Q2.T118_65_2
  h1 := (4,3,4,0,4)
  h2 := (4,3,4,0,3)
  D1 := [[4, 4, 3, 2], [4, 4, 4, 1], [4, 4, 0, 0], [4, 4, 1, 4], [4, 4, 2, 3]]
  D2 := [[4, 4, 3, 0], [4, 4, 4, 4], [4, 4, 0, 3], [4, 4, 1, 2], [4, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_66_5 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T118_66
  T2 := Q2.T118_66_2
  h1 := (1,2,0,2,1)
  h2 := (1,2,0,2,3)
  D1 := [[1, 0, 2, 1], [1, 0, 1, 2], [1, 0, 0, 3], [1, 0, 4, 4], [1, 0, 3, 0]]
  D2 := [[1, 0, 2, 3], [1, 0, 1, 4], [1, 0, 0, 0], [1, 0, 4, 1], [1, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_66_6 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T118_66
  T2 := Q2.T118_66_2
  h1 := (1,2,1,1,1)
  h2 := (1,2,1,1,3)
  D1 := [[1, 1, 1, 2], [1, 1, 0, 4], [1, 1, 4, 1], [1, 1, 3, 3], [1, 1, 2, 0]]
  D2 := [[1, 1, 1, 4], [1, 1, 0, 1], [1, 1, 4, 3], [1, 1, 3, 0], [1, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_66_7 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T118_66
  T2 := Q2.T118_66_2
  h1 := (1,2,2,0,1)
  h2 := (1,2,2,0,3)
  D1 := [[1, 2, 0, 3], [1, 2, 4, 1], [1, 2, 3, 4], [1, 2, 2, 2], [1, 2, 1, 0]]
  D2 := [[1, 2, 0, 0], [1, 2, 4, 3], [1, 2, 3, 1], [1, 2, 2, 4], [1, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_66_8 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T118_66
  T2 := Q2.T118_66_2
  h1 := (1,2,3,4,1)
  h2 := (1,2,3,4,3)
  D1 := [[1, 3, 4, 4], [1, 3, 3, 3], [1, 3, 2, 2], [1, 3, 1, 1], [1, 3, 0, 0]]
  D2 := [[1, 3, 4, 1], [1, 3, 3, 0], [1, 3, 2, 4], [1, 3, 1, 3], [1, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_66_9 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T118_66
  T2 := Q2.T118_66_2
  h1 := (1,2,4,3,1)
  h2 := (1,2,4,3,3)
  D1 := [[1, 4, 3, 0], [1, 4, 2, 0], [1, 4, 1, 0], [1, 4, 0, 0], [1, 4, 4, 0]]
  D2 := [[1, 4, 3, 2], [1, 4, 2, 2], [1, 4, 1, 2], [1, 4, 0, 2], [1, 4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_66_10 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T118_66
  T2 := Q2.T118_66_2
  h1 := (2,4,0,1,4)
  h2 := (2,4,0,1,3)
  D1 := [[2, 0, 4, 0], [2, 0, 2, 3], [2, 0, 0, 1], [2, 0, 3, 4], [2, 0, 1, 2]]
  D2 := [[2, 0, 4, 4], [2, 0, 2, 2], [2, 0, 0, 0], [2, 0, 3, 3], [2, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_66_11 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T118_66
  T2 := Q2.T118_66_2
  h1 := (2,4,1,0,4)
  h2 := (2,4,1,0,3)
  D1 := [[2, 1, 3, 0], [2, 1, 1, 4], [2, 1, 4, 3], [2, 1, 2, 2], [2, 1, 0, 1]]
  D2 := [[2, 1, 3, 4], [2, 1, 1, 3], [2, 1, 4, 2], [2, 1, 2, 1], [2, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_66_12 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T118_66
  T2 := Q2.T118_66_2
  h1 := (2,4,2,4,4)
  h2 := (2,4,2,4,3)
  D1 := [[2, 2, 2, 0], [2, 2, 0, 0], [2, 2, 3, 0], [2, 2, 1, 0], [2, 2, 4, 0]]
  D2 := [[2, 2, 2, 4], [2, 2, 0, 4], [2, 2, 3, 4], [2, 2, 1, 4], [2, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_66_13 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T118_66
  T2 := Q2.T118_66_2
  h1 := (2,4,3,3,4)
  h2 := (2,4,3,3,3)
  D1 := [[2, 3, 1, 0], [2, 3, 4, 1], [2, 3, 2, 2], [2, 3, 0, 3], [2, 3, 3, 4]]
  D2 := [[2, 3, 1, 4], [2, 3, 4, 0], [2, 3, 2, 1], [2, 3, 0, 2], [2, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_66_14 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T118_66
  T2 := Q2.T118_66_2
  h1 := (2,4,4,2,4)
  h2 := (2,4,4,2,3)
  D1 := [[2, 4, 0, 0], [2, 4, 3, 2], [2, 4, 1, 4], [2, 4, 4, 1], [2, 4, 2, 3]]
  D2 := [[2, 4, 0, 4], [2, 4, 3, 1], [2, 4, 1, 3], [2, 4, 4, 0], [2, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_66_15 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T118_66
  T2 := Q2.T118_66_2
  h1 := (3,1,0,2,2)
  h2 := (3,1,0,2,4)
  D1 := [[3, 0, 1, 2], [3, 0, 3, 3], [3, 0, 0, 4], [3, 0, 2, 0], [3, 0, 4, 1]]
  D2 := [[3, 0, 1, 3], [3, 0, 3, 4], [3, 0, 0, 0], [3, 0, 2, 1], [3, 0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_66_16 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T118_66
  T2 := Q2.T118_66_2
  h1 := (3,1,1,1,2)
  h2 := (3,1,1,1,4)
  D1 := [[3, 1, 0, 1], [3, 1, 2, 3], [3, 1, 4, 0], [3, 1, 1, 2], [3, 1, 3, 4]]
  D2 := [[3, 1, 0, 2], [3, 1, 2, 4], [3, 1, 4, 1], [3, 1, 1, 3], [3, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_66_17 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T118_66
  T2 := Q2.T118_66_2
  h1 := (3,1,2,0,2)
  h2 := (3,1,2,0,4)
  D1 := [[3, 2, 4, 0], [3, 2, 1, 3], [3, 2, 3, 1], [3, 2, 0, 4], [3, 2, 2, 2]]
  D2 := [[3, 2, 4, 1], [3, 2, 1, 4], [3, 2, 3, 2], [3, 2, 0, 0], [3, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_66_18 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T118_66
  T2 := Q2.T118_66_2
  h1 := (3,1,3,4,2)
  h2 := (3,1,3,4,4)
  D1 := [[3, 3, 3, 4], [3, 3, 0, 3], [3, 3, 2, 2], [3, 3, 4, 1], [3, 3, 1, 0]]
  D2 := [[3, 3, 3, 0], [3, 3, 0, 4], [3, 3, 2, 3], [3, 3, 4, 2], [3, 3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_66_19 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T118_66
  T2 := Q2.T118_66_2
  h1 := (3,1,4,3,2)
  h2 := (3,1,4,3,4)
  D1 := [[3, 4, 2, 3], [3, 4, 4, 3], [3, 4, 1, 3], [3, 4, 3, 3], [3, 4, 0, 3]]
  D2 := [[3, 4, 2, 4], [3, 4, 4, 4], [3, 4, 1, 4], [3, 4, 3, 4], [3, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_66_20 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T118_66
  T2 := Q2.T118_66_2
  h1 := (4,3,0,0,0)
  h2 := (4,3,0,0,4)
  D1 := [[4, 0, 3, 2], [4, 0, 4, 2], [4, 0, 0, 2], [4, 0, 1, 2], [4, 0, 2, 2]]
  D2 := [[4, 0, 3, 0], [4, 0, 4, 0], [4, 0, 0, 0], [4, 0, 1, 0], [4, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_66_21 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T118_66
  T2 := Q2.T118_66_2
  h1 := (4,3,1,4,0)
  h2 := (4,3,1,4,4)
  D1 := [[4, 1, 2, 0], [4, 1, 3, 1], [4, 1, 4, 2], [4, 1, 0, 3], [4, 1, 1, 4]]
  D2 := [[4, 1, 2, 3], [4, 1, 3, 4], [4, 1, 4, 0], [4, 1, 0, 1], [4, 1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_66_22 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T118_66
  T2 := Q2.T118_66_2
  h1 := (4,3,2,3,0)
  h2 := (4,3,2,3,4)
  D1 := [[4, 2, 1, 3], [4, 2, 2, 0], [4, 2, 3, 2], [4, 2, 4, 4], [4, 2, 0, 1]]
  D2 := [[4, 2, 1, 1], [4, 2, 2, 3], [4, 2, 3, 0], [4, 2, 4, 2], [4, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_66_23 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T118_66
  T2 := Q2.T118_66_2
  h1 := (4,3,3,2,0)
  h2 := (4,3,3,2,4)
  D1 := [[4, 3, 0, 1], [4, 3, 1, 4], [4, 3, 2, 2], [4, 3, 3, 0], [4, 3, 4, 3]]
  D2 := [[4, 3, 0, 4], [4, 3, 1, 2], [4, 3, 2, 0], [4, 3, 3, 3], [4, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_66_24 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T118_66
  T2 := Q2.T118_66_2
  h1 := (4,3,4,1,0)
  h2 := (4,3,4,1,4)
  D1 := [[4, 4, 4, 4], [4, 4, 0, 3], [4, 4, 1, 2], [4, 4, 2, 1], [4, 4, 3, 0]]
  D2 := [[4, 4, 4, 2], [4, 4, 0, 1], [4, 4, 1, 0], [4, 4, 2, 4], [4, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_68_5 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T118_68
  T2 := Q2.T118_68_2
  h1 := (1,2,0,2,0)
  h2 := (1,2,0,2,2)
  D1 := [[1, 0, 2, 0], [1, 0, 1, 1], [1, 0, 0, 2], [1, 0, 4, 3], [1, 0, 3, 4]]
  D2 := [[1, 0, 2, 2], [1, 0, 1, 3], [1, 0, 0, 4], [1, 0, 4, 0], [1, 0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_68_6 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T118_68
  T2 := Q2.T118_68_2
  h1 := (1,2,1,4,0)
  h2 := (1,2,1,4,2)
  D1 := [[1, 1, 4, 3], [1, 1, 3, 0], [1, 1, 2, 2], [1, 1, 1, 4], [1, 1, 0, 1]]
  D2 := [[1, 1, 4, 0], [1, 1, 3, 2], [1, 1, 2, 4], [1, 1, 1, 1], [1, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_68_7 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T118_68
  T2 := Q2.T118_68_2
  h1 := (1,2,2,1,0)
  h2 := (1,2,2,1,2)
  D1 := [[1, 2, 1, 1], [1, 2, 0, 4], [1, 2, 4, 2], [1, 2, 3, 0], [1, 2, 2, 3]]
  D2 := [[1, 2, 1, 3], [1, 2, 0, 1], [1, 2, 4, 4], [1, 2, 3, 2], [1, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_68_8 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T118_68
  T2 := Q2.T118_68_2
  h1 := (1,2,3,3,0)
  h2 := (1,2,3,3,2)
  D1 := [[1, 3, 3, 4], [1, 3, 2, 3], [1, 3, 1, 2], [1, 3, 0, 1], [1, 3, 4, 0]]
  D2 := [[1, 3, 3, 1], [1, 3, 2, 0], [1, 3, 1, 4], [1, 3, 0, 3], [1, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_68_9 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T118_68
  T2 := Q2.T118_68_2
  h1 := (1,2,4,0,0)
  h2 := (1,2,4,0,2)
  D1 := [[1, 4, 0, 2], [1, 4, 4, 2], [1, 4, 3, 2], [1, 4, 2, 2], [1, 4, 1, 2]]
  D2 := [[1, 4, 0, 4], [1, 4, 4, 4], [1, 4, 3, 4], [1, 4, 2, 4], [1, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_68_10 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T118_68
  T2 := Q2.T118_68_2
  h1 := (2,4,0,1,2)
  h2 := (2,4,0,1,1)
  D1 := [[2, 0, 4, 3], [2, 0, 2, 1], [2, 0, 0, 4], [2, 0, 3, 2], [2, 0, 1, 0]]
  D2 := [[2, 0, 4, 2], [2, 0, 2, 0], [2, 0, 0, 3], [2, 0, 3, 1], [2, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_68_11 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T118_68
  T2 := Q2.T118_68_2
  h1 := (2,4,1,3,2)
  h2 := (2,4,1,3,1)
  D1 := [[2, 1, 1, 2], [2, 1, 4, 1], [2, 1, 2, 0], [2, 1, 0, 4], [2, 1, 3, 3]]
  D2 := [[2, 1, 1, 1], [2, 1, 4, 0], [2, 1, 2, 4], [2, 1, 0, 3], [2, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_68_12 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T118_68
  T2 := Q2.T118_68_2
  h1 := (2,4,2,0,2)
  h2 := (2,4,2,0,1)
  D1 := [[2, 2, 3, 1], [2, 2, 1, 1], [2, 2, 4, 1], [2, 2, 2, 1], [2, 2, 0, 1]]
  D2 := [[2, 2, 3, 0], [2, 2, 1, 0], [2, 2, 4, 0], [2, 2, 2, 0], [2, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_68_13 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T118_68
  T2 := Q2.T118_68_2
  h1 := (2,4,3,2,2)
  h2 := (2,4,3,2,1)
  D1 := [[2, 3, 0, 0], [2, 3, 3, 1], [2, 3, 1, 2], [2, 3, 4, 3], [2, 3, 2, 4]]
  D2 := [[2, 3, 0, 4], [2, 3, 3, 0], [2, 3, 1, 1], [2, 3, 4, 2], [2, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_68_14 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T118_68
  T2 := Q2.T118_68_2
  h1 := (2,4,4,4,2)
  h2 := (2,4,4,4,1)
  D1 := [[2, 4, 2, 4], [2, 4, 0, 1], [2, 4, 3, 3], [2, 4, 1, 0], [2, 4, 4, 2]]
  D2 := [[2, 4, 2, 3], [2, 4, 0, 0], [2, 4, 3, 2], [2, 4, 1, 4], [2, 4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_68_15 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T118_68
  T2 := Q2.T118_68_2
  h1 := (3,1,0,2,4)
  h2 := (3,1,0,2,1)
  D1 := [[3, 0, 1, 4], [3, 0, 3, 0], [3, 0, 0, 1], [3, 0, 2, 2], [3, 0, 4, 3]]
  D2 := [[3, 0, 1, 0], [3, 0, 3, 1], [3, 0, 0, 2], [3, 0, 2, 3], [3, 0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_68_16 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T118_68
  T2 := Q2.T118_68_2
  h1 := (3,1,1,4,4)
  h2 := (3,1,1,4,1)
  D1 := [[3, 1, 3, 4], [3, 1, 0, 1], [3, 1, 2, 3], [3, 1, 4, 0], [3, 1, 1, 2]]
  D2 := [[3, 1, 3, 0], [3, 1, 0, 2], [3, 1, 2, 4], [3, 1, 4, 1], [3, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_68_17 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T118_68
  T2 := Q2.T118_68_2
  h1 := (3,1,2,1,4)
  h2 := (3,1,2,1,1)
  D1 := [[3, 2, 0, 4], [3, 2, 2, 2], [3, 2, 4, 0], [3, 2, 1, 3], [3, 2, 3, 1]]
  D2 := [[3, 2, 0, 0], [3, 2, 2, 3], [3, 2, 4, 1], [3, 2, 1, 4], [3, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_68_18 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T118_68
  T2 := Q2.T118_68_2
  h1 := (3,1,3,3,4)
  h2 := (3,1,3,3,1)
  D1 := [[3, 3, 2, 4], [3, 3, 4, 3], [3, 3, 1, 2], [3, 3, 3, 1], [3, 3, 0, 0]]
  D2 := [[3, 3, 2, 0], [3, 3, 4, 4], [3, 3, 1, 3], [3, 3, 3, 2], [3, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_68_23 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T118_68
  T2 := Q2.T118_68_2
  h1 := (4,3,3,1,1)
  h2 := (4,3,3,1,0)
  D1 := [[4, 3, 4, 1], [4, 3, 0, 4], [4, 3, 1, 2], [4, 3, 2, 0], [4, 3, 3, 3]]
  D2 := [[4, 3, 4, 4], [4, 3, 0, 2], [4, 3, 1, 0], [4, 3, 2, 3], [4, 3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_68_24 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T118_68
  T2 := Q2.T118_68_2
  h1 := (4,3,4,3,1)
  h2 := (4,3,4,3,0)
  D1 := [[4, 4, 1, 2], [4, 4, 2, 1], [4, 4, 3, 0], [4, 4, 4, 4], [4, 4, 0, 3]]
  D2 := [[4, 4, 1, 0], [4, 4, 2, 4], [4, 4, 3, 3], [4, 4, 4, 2], [4, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
