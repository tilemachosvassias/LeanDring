/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C016
import LeanDring.P5.Data.EntryK.C017

/-!
# Species-table cell data, stage 2 — column-data-divergent columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
cdd tier, chunk 38: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_67_35_15 : ColCertDiv where
  rK := ⟨67, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T67_35
  T2 := Q2.T67_35_2
  h1 := (3,1,2,2,3)
  h2 := (3,1,2,2,0)
  D1 := [[3, 2, 1], [3, 2, 3], [3, 2, 0], [3, 2, 2], [3, 2, 4]]
  D2 := [[3, 2, 2], [3, 2, 4], [3, 2, 1], [3, 2, 3], [3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_67_35_20 : ColCertDiv where
  rK := ⟨67, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T67_35
  T2 := Q2.T67_35_2
  h1 := (4,3,1,0,4)
  h2 := (4,3,1,0,3)
  D1 := [[4, 1, 3], [4, 1, 4], [4, 1, 0], [4, 1, 1], [4, 1, 2]]
  D2 := [[4, 1, 1], [4, 1, 2], [4, 1, 3], [4, 1, 4], [4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_67_40_5 : ColCertDiv where
  rK := ⟨67, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T67_40
  T2 := Q2.T67_40_2
  h1 := (1,2,1,2,4)
  h2 := (1,2,1,2,1)
  D1 := [[1, 1, 2], [1, 1, 1], [1, 1, 0], [1, 1, 4], [1, 1, 3]]
  D2 := [[1, 1, 4], [1, 1, 3], [1, 1, 2], [1, 1, 1], [1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_67_40_10 : ColCertDiv where
  rK := ⟨67, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T67_40
  T2 := Q2.T67_40_2
  h1 := (2,4,2,1,2)
  h2 := (2,4,2,1,1)
  D1 := [[2, 2, 4], [2, 2, 2], [2, 2, 0], [2, 2, 3], [2, 2, 1]]
  D2 := [[2, 2, 3], [2, 2, 1], [2, 2, 4], [2, 2, 2], [2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_67_40_15 : ColCertDiv where
  rK := ⟨67, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T67_40
  T2 := Q2.T67_40_2
  h1 := (3,1,3,2,2)
  h2 := (3,1,3,2,4)
  D1 := [[3, 3, 1], [3, 3, 3], [3, 3, 0], [3, 3, 2], [3, 3, 4]]
  D2 := [[3, 3, 2], [3, 3, 4], [3, 3, 1], [3, 3, 3], [3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_67_40_20 : ColCertDiv where
  rK := ⟨67, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T67_40
  T2 := Q2.T67_40_2
  h1 := (4,3,4,0,4)
  h2 := (4,3,4,0,3)
  D1 := [[4, 4, 3], [4, 4, 4], [4, 4, 0], [4, 4, 1], [4, 4, 2]]
  D2 := [[4, 4, 1], [4, 4, 2], [4, 4, 3], [4, 4, 4], [4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_67_45_5 : ColCertDiv where
  rK := ⟨67, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T67_45
  T2 := Q2.T67_45_2
  h1 := (1,2,2,2,1)
  h2 := (1,2,2,2,3)
  D1 := [[1, 2, 3], [1, 2, 2], [1, 2, 1], [1, 2, 0], [1, 2, 4]]
  D2 := [[1, 2, 0], [1, 2, 4], [1, 2, 3], [1, 2, 2], [1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_67_45_10 : ColCertDiv where
  rK := ⟨67, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T67_45
  T2 := Q2.T67_45_2
  h1 := (2,4,4,1,3)
  h2 := (2,4,4,1,2)
  D1 := [[2, 4, 1], [2, 4, 4], [2, 4, 2], [2, 4, 0], [2, 4, 3]]
  D2 := [[2, 4, 0], [2, 4, 3], [2, 4, 1], [2, 4, 4], [2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_67_45_15 : ColCertDiv where
  rK := ⟨67, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T67_45
  T2 := Q2.T67_45_2
  h1 := (3,1,1,2,4)
  h2 := (3,1,1,2,1)
  D1 := [[3, 1, 4], [3, 1, 1], [3, 1, 3], [3, 1, 0], [3, 1, 2]]
  D2 := [[3, 1, 0], [3, 1, 2], [3, 1, 4], [3, 1, 1], [3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_67_45_20 : ColCertDiv where
  rK := ⟨67, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T67_45
  T2 := Q2.T67_45_2
  h1 := (4,3,3,0,4)
  h2 := (4,3,3,0,3)
  D1 := [[4, 3, 2], [4, 3, 3], [4, 3, 4], [4, 3, 0], [4, 3, 1]]
  D2 := [[4, 3, 0], [4, 3, 1], [4, 3, 2], [4, 3, 3], [4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_67_50_5 : ColCertDiv where
  rK := ⟨67, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T67_50
  T2 := Q2.T67_50_2
  h1 := (1,2,0,2,2)
  h2 := (1,2,0,2,4)
  D1 := [[1, 0, 0], [1, 0, 4], [1, 0, 3], [1, 0, 2], [1, 0, 1]]
  D2 := [[1, 0, 2], [1, 0, 1], [1, 0, 0], [1, 0, 4], [1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_67_50_10 : ColCertDiv where
  rK := ⟨67, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T67_50
  T2 := Q2.T67_50_2
  h1 := (2,4,0,1,1)
  h2 := (2,4,0,1,0)
  D1 := [[2, 0, 0], [2, 0, 3], [2, 0, 1], [2, 0, 4], [2, 0, 2]]
  D2 := [[2, 0, 4], [2, 0, 2], [2, 0, 0], [2, 0, 3], [2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_67_50_15 : ColCertDiv where
  rK := ⟨67, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T67_50
  T2 := Q2.T67_50_2
  h1 := (3,1,0,2,0)
  h2 := (3,1,0,2,2)
  D1 := [[3, 0, 0], [3, 0, 2], [3, 0, 4], [3, 0, 1], [3, 0, 3]]
  D2 := [[3, 0, 1], [3, 0, 3], [3, 0, 0], [3, 0, 2], [3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_67_50_20 : ColCertDiv where
  rK := ⟨67, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T67_50
  T2 := Q2.T67_50_2
  h1 := (4,3,0,0,4)
  h2 := (4,3,0,0,3)
  D1 := [[4, 0, 0], [4, 0, 1], [4, 0, 2], [4, 0, 3], [4, 0, 4]]
  D2 := [[4, 0, 3], [4, 0, 4], [4, 0, 0], [4, 0, 1], [4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_69_30_5 : ColCertDiv where
  rK := ⟨69, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T69_30
  T2 := Q2.T69_30_2
  h1 := (1,2,3,2,3)
  h2 := (1,2,3,2,0)
  D1 := [[1, 3, 2], [1, 3, 1], [1, 3, 0], [1, 3, 4], [1, 3, 3]]
  D2 := [[1, 3, 4], [1, 3, 3], [1, 3, 2], [1, 3, 1], [1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_69_30_10 : ColCertDiv where
  rK := ⟨69, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T69_30
  T2 := Q2.T69_30_2
  h1 := (2,4,1,1,4)
  h2 := (2,4,1,1,3)
  D1 := [[2, 1, 0], [2, 1, 3], [2, 1, 1], [2, 1, 4], [2, 1, 2]]
  D2 := [[2, 1, 4], [2, 1, 2], [2, 1, 0], [2, 1, 3], [2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_69_30_15 : ColCertDiv where
  rK := ⟨69, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T69_30
  T2 := Q2.T69_30_2
  h1 := (3,1,4,2,1)
  h2 := (3,1,4,2,3)
  D1 := [[3, 4, 4], [3, 4, 1], [3, 4, 3], [3, 4, 0], [3, 4, 2]]
  D2 := [[3, 4, 0], [3, 4, 2], [3, 4, 4], [3, 4, 1], [3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_69_30_20 : ColCertDiv where
  rK := ⟨69, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T69_30
  T2 := Q2.T69_30_2
  h1 := (4,3,2,0,4)
  h2 := (4,3,2,0,3)
  D1 := [[4, 2, 4], [4, 2, 0], [4, 2, 1], [4, 2, 2], [4, 2, 3]]
  D2 := [[4, 2, 2], [4, 2, 3], [4, 2, 4], [4, 2, 0], [4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_69_35_5 : ColCertDiv where
  rK := ⟨69, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T69_35
  T2 := Q2.T69_35_2
  h1 := (1,2,4,2,0)
  h2 := (1,2,4,2,2)
  D1 := [[1, 4, 0], [1, 4, 4], [1, 4, 3], [1, 4, 2], [1, 4, 1]]
  D2 := [[1, 4, 2], [1, 4, 1], [1, 4, 0], [1, 4, 4], [1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_69_35_10 : ColCertDiv where
  rK := ⟨69, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T69_35
  T2 := Q2.T69_35_2
  h1 := (2,4,3,1,0)
  h2 := (2,4,3,1,4)
  D1 := [[2, 3, 3], [2, 3, 1], [2, 3, 4], [2, 3, 2], [2, 3, 0]]
  D2 := [[2, 3, 2], [2, 3, 0], [2, 3, 3], [2, 3, 1], [2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_69_35_15 : ColCertDiv where
  rK := ⟨69, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T69_35
  T2 := Q2.T69_35_2
  h1 := (3,1,2,2,3)
  h2 := (3,1,2,2,0)
  D1 := [[3, 2, 4], [3, 2, 1], [3, 2, 3], [3, 2, 0], [3, 2, 2]]
  D2 := [[3, 2, 0], [3, 2, 2], [3, 2, 4], [3, 2, 1], [3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_69_35_20 : ColCertDiv where
  rK := ⟨69, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T69_35
  T2 := Q2.T69_35_2
  h1 := (4,3,1,0,4)
  h2 := (4,3,1,0,3)
  D1 := [[4, 1, 3], [4, 1, 4], [4, 1, 0], [4, 1, 1], [4, 1, 2]]
  D2 := [[4, 1, 1], [4, 1, 2], [4, 1, 3], [4, 1, 4], [4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_69_40_5 : ColCertDiv where
  rK := ⟨69, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T69_40
  T2 := Q2.T69_40_2
  h1 := (1,2,1,2,4)
  h2 := (1,2,1,2,1)
  D1 := [[1, 1, 0], [1, 1, 4], [1, 1, 3], [1, 1, 2], [1, 1, 1]]
  D2 := [[1, 1, 2], [1, 1, 1], [1, 1, 0], [1, 1, 4], [1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_69_40_10 : ColCertDiv where
  rK := ⟨69, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T69_40
  T2 := Q2.T69_40_2
  h1 := (2,4,2,1,2)
  h2 := (2,4,2,1,1)
  D1 := [[2, 2, 2], [2, 2, 0], [2, 2, 3], [2, 2, 1], [2, 2, 4]]
  D2 := [[2, 2, 1], [2, 2, 4], [2, 2, 2], [2, 2, 0], [2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_69_40_15 : ColCertDiv where
  rK := ⟨69, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T69_40
  T2 := Q2.T69_40_2
  h1 := (3,1,3,2,2)
  h2 := (3,1,3,2,4)
  D1 := [[3, 3, 1], [3, 3, 3], [3, 3, 0], [3, 3, 2], [3, 3, 4]]
  D2 := [[3, 3, 2], [3, 3, 4], [3, 3, 1], [3, 3, 3], [3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_69_40_20 : ColCertDiv where
  rK := ⟨69, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T69_40
  T2 := Q2.T69_40_2
  h1 := (4,3,4,0,4)
  h2 := (4,3,4,0,3)
  D1 := [[4, 4, 2], [4, 4, 3], [4, 4, 4], [4, 4, 0], [4, 4, 1]]
  D2 := [[4, 4, 0], [4, 4, 1], [4, 4, 2], [4, 4, 3], [4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_69_45_5 : ColCertDiv where
  rK := ⟨69, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T69_45
  T2 := Q2.T69_45_2
  h1 := (1,2,2,2,1)
  h2 := (1,2,2,2,3)
  D1 := [[1, 2, 2], [1, 2, 1], [1, 2, 0], [1, 2, 4], [1, 2, 3]]
  D2 := [[1, 2, 4], [1, 2, 3], [1, 2, 2], [1, 2, 1], [1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_69_45_10 : ColCertDiv where
  rK := ⟨69, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T69_45
  T2 := Q2.T69_45_2
  h1 := (2,4,4,1,3)
  h2 := (2,4,4,1,2)
  D1 := [[2, 4, 3], [2, 4, 1], [2, 4, 4], [2, 4, 2], [2, 4, 0]]
  D2 := [[2, 4, 2], [2, 4, 0], [2, 4, 3], [2, 4, 1], [2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_69_45_15 : ColCertDiv where
  rK := ⟨69, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T69_45
  T2 := Q2.T69_45_2
  h1 := (3,1,1,2,4)
  h2 := (3,1,1,2,1)
  D1 := [[3, 1, 3], [3, 1, 0], [3, 1, 2], [3, 1, 4], [3, 1, 1]]
  D2 := [[3, 1, 4], [3, 1, 1], [3, 1, 3], [3, 1, 0], [3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_69_45_20 : ColCertDiv where
  rK := ⟨69, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T69_45
  T2 := Q2.T69_45_2
  h1 := (4,3,3,0,4)
  h2 := (4,3,3,0,3)
  D1 := [[4, 3, 2], [4, 3, 3], [4, 3, 4], [4, 3, 0], [4, 3, 1]]
  D2 := [[4, 3, 0], [4, 3, 1], [4, 3, 2], [4, 3, 3], [4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_69_50_5 : ColCertDiv where
  rK := ⟨69, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T69_50
  T2 := Q2.T69_50_2
  h1 := (1,2,0,2,2)
  h2 := (1,2,0,2,4)
  D1 := [[1, 0, 1], [1, 0, 0], [1, 0, 4], [1, 0, 3], [1, 0, 2]]
  D2 := [[1, 0, 3], [1, 0, 2], [1, 0, 1], [1, 0, 0], [1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_69_50_10 : ColCertDiv where
  rK := ⟨69, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T69_50
  T2 := Q2.T69_50_2
  h1 := (2,4,0,1,1)
  h2 := (2,4,0,1,0)
  D1 := [[2, 0, 2], [2, 0, 0], [2, 0, 3], [2, 0, 1], [2, 0, 4]]
  D2 := [[2, 0, 1], [2, 0, 4], [2, 0, 2], [2, 0, 0], [2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_69_50_15 : ColCertDiv where
  rK := ⟨69, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T69_50
  T2 := Q2.T69_50_2
  h1 := (3,1,0,2,0)
  h2 := (3,1,0,2,2)
  D1 := [[3, 0, 3], [3, 0, 0], [3, 0, 2], [3, 0, 4], [3, 0, 1]]
  D2 := [[3, 0, 4], [3, 0, 1], [3, 0, 3], [3, 0, 0], [3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_69_50_20 : ColCertDiv where
  rK := ⟨69, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T69_50
  T2 := Q2.T69_50_2
  h1 := (4,3,0,0,4)
  h2 := (4,3,0,0,3)
  D1 := [[4, 0, 4], [4, 0, 0], [4, 0, 1], [4, 0, 2], [4, 0, 3]]
  D2 := [[4, 0, 2], [4, 0, 3], [4, 0, 4], [4, 0, 0], [4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_73_31_5 : ColCertDiv where
  rK := ⟨73, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T73_31
  T2 := Q2.T73_31_2
  h1 := (1,3,2,0,4)
  h2 := (1,3,2,0,0)
  D1 := [[1, 2, 1], [1, 2, 0], [1, 2, 4], [1, 2, 3], [1, 2, 2]]
  D2 := [[1, 2, 2], [1, 2, 1], [1, 2, 0], [1, 2, 4], [1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_73_31_10 : ColCertDiv where
  rK := ⟨73, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T73_31
  T2 := Q2.T73_31_2
  h1 := (2,1,4,3,0)
  h2 := (2,1,4,3,3)
  D1 := [[2, 4, 2], [2, 4, 0], [2, 4, 3], [2, 4, 1], [2, 4, 4]]
  D2 := [[2, 4, 4], [2, 4, 2], [2, 4, 0], [2, 4, 3], [2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_73_31_15 : ColCertDiv where
  rK := ⟨73, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T73_31
  T2 := Q2.T73_31_2
  h1 := (3,4,1,4,4)
  h2 := (3,4,1,4,3)
  D1 := [[3, 1, 3], [3, 1, 0], [3, 1, 2], [3, 1, 4], [3, 1, 1]]
  D2 := [[3, 1, 1], [3, 1, 3], [3, 1, 0], [3, 1, 2], [3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_73_31_20 : ColCertDiv where
  rK := ⟨73, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T73_31
  T2 := Q2.T73_31_2
  h1 := (4,2,3,3,1)
  h2 := (4,2,3,3,2)
  D1 := [[4, 3, 4], [4, 3, 0], [4, 3, 1], [4, 3, 2], [4, 3, 3]]
  D2 := [[4, 3, 3], [4, 3, 4], [4, 3, 0], [4, 3, 1], [4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_73_36_5 : ColCertDiv where
  rK := ⟨73, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T73_36
  T2 := Q2.T73_36_2
  h1 := (1,3,1,0,1)
  h2 := (1,3,1,0,2)
  D1 := [[1, 1, 2], [1, 1, 1], [1, 1, 0], [1, 1, 4], [1, 1, 3]]
  D2 := [[1, 1, 3], [1, 1, 2], [1, 1, 1], [1, 1, 0], [1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_73_36_10 : ColCertDiv where
  rK := ⟨73, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T73_36
  T2 := Q2.T73_36_2
  h1 := (2,1,2,3,1)
  h2 := (2,1,2,3,4)
  D1 := [[2, 2, 4], [2, 2, 2], [2, 2, 0], [2, 2, 3], [2, 2, 1]]
  D2 := [[2, 2, 1], [2, 2, 4], [2, 2, 2], [2, 2, 0], [2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_73_36_15 : ColCertDiv where
  rK := ⟨73, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T73_36
  T2 := Q2.T73_36_2
  h1 := (3,4,3,4,1)
  h2 := (3,4,3,4,0)
  D1 := [[3, 3, 1], [3, 3, 3], [3, 3, 0], [3, 3, 2], [3, 3, 4]]
  D2 := [[3, 3, 4], [3, 3, 1], [3, 3, 3], [3, 3, 0], [3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_73_36_20 : ColCertDiv where
  rK := ⟨73, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T73_36
  T2 := Q2.T73_36_2
  h1 := (4,2,4,3,1)
  h2 := (4,2,4,3,2)
  D1 := [[4, 4, 3], [4, 4, 4], [4, 4, 0], [4, 4, 1], [4, 4, 2]]
  D2 := [[4, 4, 2], [4, 4, 3], [4, 4, 4], [4, 4, 0], [4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_73_41_5 : ColCertDiv where
  rK := ⟨73, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T73_41
  T2 := Q2.T73_41_2
  h1 := (1,3,4,0,0)
  h2 := (1,3,4,0,1)
  D1 := [[1, 4, 2], [1, 4, 1], [1, 4, 0], [1, 4, 4], [1, 4, 3]]
  D2 := [[1, 4, 3], [1, 4, 2], [1, 4, 1], [1, 4, 0], [1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_73_41_10 : ColCertDiv where
  rK := ⟨73, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T73_41
  T2 := Q2.T73_41_2
  h1 := (2,1,3,3,3)
  h2 := (2,1,3,3,1)
  D1 := [[2, 3, 4], [2, 3, 2], [2, 3, 0], [2, 3, 3], [2, 3, 1]]
  D2 := [[2, 3, 1], [2, 3, 4], [2, 3, 2], [2, 3, 0], [2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_73_41_15 : ColCertDiv where
  rK := ⟨73, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T73_41
  T2 := Q2.T73_41_2
  h1 := (3,4,2,4,0)
  h2 := (3,4,2,4,4)
  D1 := [[3, 2, 1], [3, 2, 3], [3, 2, 0], [3, 2, 2], [3, 2, 4]]
  D2 := [[3, 2, 4], [3, 2, 1], [3, 2, 3], [3, 2, 0], [3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_73_41_20 : ColCertDiv where
  rK := ⟨73, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T73_41
  T2 := Q2.T73_41_2
  h1 := (4,2,1,3,1)
  h2 := (4,2,1,3,2)
  D1 := [[4, 1, 3], [4, 1, 4], [4, 1, 0], [4, 1, 1], [4, 1, 2]]
  D2 := [[4, 1, 2], [4, 1, 3], [4, 1, 4], [4, 1, 0], [4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_73_46_5 : ColCertDiv where
  rK := ⟨73, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T73_46
  T2 := Q2.T73_46_2
  h1 := (1,3,3,0,2)
  h2 := (1,3,3,0,3)
  D1 := [[1, 3, 1], [1, 3, 0], [1, 3, 4], [1, 3, 3], [1, 3, 2]]
  D2 := [[1, 3, 2], [1, 3, 1], [1, 3, 0], [1, 3, 4], [1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_73_46_10 : ColCertDiv where
  rK := ⟨73, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T73_46
  T2 := Q2.T73_46_2
  h1 := (2,1,1,3,4)
  h2 := (2,1,1,3,2)
  D1 := [[2, 1, 2], [2, 1, 0], [2, 1, 3], [2, 1, 1], [2, 1, 4]]
  D2 := [[2, 1, 4], [2, 1, 2], [2, 1, 0], [2, 1, 3], [2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_73_46_15 : ColCertDiv where
  rK := ⟨73, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T73_46
  T2 := Q2.T73_46_2
  h1 := (3,4,4,4,2)
  h2 := (3,4,4,4,1)
  D1 := [[3, 4, 3], [3, 4, 0], [3, 4, 2], [3, 4, 4], [3, 4, 1]]
  D2 := [[3, 4, 1], [3, 4, 3], [3, 4, 0], [3, 4, 2], [3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_73_46_20 : ColCertDiv where
  rK := ⟨73, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T73_46
  T2 := Q2.T73_46_2
  h1 := (4,2,2,3,1)
  h2 := (4,2,2,3,2)
  D1 := [[4, 2, 4], [4, 2, 0], [4, 2, 1], [4, 2, 2], [4, 2, 3]]
  D2 := [[4, 2, 3], [4, 2, 4], [4, 2, 0], [4, 2, 1], [4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_73_51_5 : ColCertDiv where
  rK := ⟨73, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T73_51
  T2 := Q2.T73_51_2
  h1 := (1,3,0,0,3)
  h2 := (1,3,0,0,4)
  D1 := [[1, 0, 4], [1, 0, 3], [1, 0, 2], [1, 0, 1], [1, 0, 0]]
  D2 := [[1, 0, 0], [1, 0, 4], [1, 0, 3], [1, 0, 2], [1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_73_51_10 : ColCertDiv where
  rK := ⟨73, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T73_51
  T2 := Q2.T73_51_2
  h1 := (2,1,0,3,2)
  h2 := (2,1,0,3,0)
  D1 := [[2, 0, 3], [2, 0, 1], [2, 0, 4], [2, 0, 2], [2, 0, 0]]
  D2 := [[2, 0, 0], [2, 0, 3], [2, 0, 1], [2, 0, 4], [2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_73_51_15 : ColCertDiv where
  rK := ⟨73, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T73_51
  T2 := Q2.T73_51_2
  h1 := (3,4,0,4,3)
  h2 := (3,4,0,4,2)
  D1 := [[3, 0, 2], [3, 0, 4], [3, 0, 1], [3, 0, 3], [3, 0, 0]]
  D2 := [[3, 0, 0], [3, 0, 2], [3, 0, 4], [3, 0, 1], [3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_73_51_20 : ColCertDiv where
  rK := ⟨73, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T73_51
  T2 := Q2.T73_51_2
  h1 := (4,2,0,3,1)
  h2 := (4,2,0,3,2)
  D1 := [[4, 0, 1], [4, 0, 2], [4, 0, 3], [4, 0, 4], [4, 0, 0]]
  D2 := [[4, 0, 0], [4, 0, 1], [4, 0, 2], [4, 0, 3], [4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_74_31_5 : ColCertDiv where
  rK := ⟨74, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T74_31
  T2 := Q2.T74_31_2
  h1 := (1,3,2,0,4)
  h2 := (1,3,2,0,0)
  D1 := [[1, 2, 1], [1, 2, 0], [1, 2, 4], [1, 2, 3], [1, 2, 2]]
  D2 := [[1, 2, 2], [1, 2, 1], [1, 2, 0], [1, 2, 4], [1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_74_31_10 : ColCertDiv where
  rK := ⟨74, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T74_31
  T2 := Q2.T74_31_2
  h1 := (2,1,4,3,0)
  h2 := (2,1,4,3,3)
  D1 := [[2, 4, 4], [2, 4, 2], [2, 4, 0], [2, 4, 3], [2, 4, 1]]
  D2 := [[2, 4, 1], [2, 4, 4], [2, 4, 2], [2, 4, 0], [2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_74_31_15 : ColCertDiv where
  rK := ⟨74, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T74_31
  T2 := Q2.T74_31_2
  h1 := (3,4,1,4,4)
  h2 := (3,4,1,4,3)
  D1 := [[3, 1, 4], [3, 1, 1], [3, 1, 3], [3, 1, 0], [3, 1, 2]]
  D2 := [[3, 1, 2], [3, 1, 4], [3, 1, 1], [3, 1, 3], [3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_74_31_20 : ColCertDiv where
  rK := ⟨74, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T74_31
  T2 := Q2.T74_31_2
  h1 := (4,2,3,3,1)
  h2 := (4,2,3,3,2)
  D1 := [[4, 3, 1], [4, 3, 2], [4, 3, 3], [4, 3, 4], [4, 3, 0]]
  D2 := [[4, 3, 0], [4, 3, 1], [4, 3, 2], [4, 3, 3], [4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_74_36_5 : ColCertDiv where
  rK := ⟨74, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T74_36
  T2 := Q2.T74_36_2
  h1 := (1,3,1,0,1)
  h2 := (1,3,1,0,2)
  D1 := [[1, 1, 4], [1, 1, 3], [1, 1, 2], [1, 1, 1], [1, 1, 0]]
  D2 := [[1, 1, 0], [1, 1, 4], [1, 1, 3], [1, 1, 2], [1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_74_36_10 : ColCertDiv where
  rK := ⟨74, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T74_36
  T2 := Q2.T74_36_2
  h1 := (2,1,2,3,1)
  h2 := (2,1,2,3,4)
  D1 := [[2, 2, 4], [2, 2, 2], [2, 2, 0], [2, 2, 3], [2, 2, 1]]
  D2 := [[2, 2, 1], [2, 2, 4], [2, 2, 2], [2, 2, 0], [2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
