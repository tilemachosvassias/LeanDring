/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C031

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 55: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_125_81_4 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T125_81
  T2 := Q2.T125_81_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_81_5 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T125_81
  T2 := Q2.T125_81_2
  h1 := (1,0,4,0,0)
  h2 := (1,0,4,0,0)
  D := [[1, 0, 0, 4], [1, 0, 0, 4], [1, 0, 0, 4], [1, 0, 0, 4], [1, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_81_10 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T125_81
  T2 := Q2.T125_81_2
  h1 := (2,0,3,0,0)
  h2 := (2,0,3,0,0)
  D := [[2, 0, 0, 3], [2, 0, 0, 3], [2, 0, 0, 3], [2, 0, 0, 3], [2, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_81_15 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T125_81
  T2 := Q2.T125_81_2
  h1 := (3,0,2,0,0)
  h2 := (3,0,2,0,0)
  D := [[3, 0, 0, 2], [3, 0, 0, 2], [3, 0, 0, 2], [3, 0, 0, 2], [3, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_81_20 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T125_81
  T2 := Q2.T125_81_2
  h1 := (4,0,1,0,0)
  h2 := (4,0,1,0,0)
  D := [[4, 0, 0, 1], [4, 0, 0, 1], [4, 0, 0, 1], [4, 0, 0, 1], [4, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_93_0 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T125_93
  T2 := Q2.T125_93_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_93_1 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T125_93
  T2 := Q2.T125_93_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_93_2 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T125_93
  T2 := Q2.T125_93_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_93_3 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T125_93
  T2 := Q2.T125_93_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_93_4 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T125_93
  T2 := Q2.T125_93_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_93_5 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T125_93
  T2 := Q2.T125_93_2
  h1 := (1,3,2,1,4)
  h2 := (1,3,2,1,4)
  D := [[1, 3, 3, 2], [1, 3, 3, 4], [1, 3, 3, 1], [1, 3, 3, 3], [1, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_96_0 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T125_96
  T2 := Q2.T125_96_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_96_1 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T125_96
  T2 := Q2.T125_96_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_96_2 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T125_96
  T2 := Q2.T125_96_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_96_3 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T125_96
  T2 := Q2.T125_96_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_96_4 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T125_96
  T2 := Q2.T125_96_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_96_5 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T125_96
  T2 := Q2.T125_96_2
  h1 := (1,4,3,4,2)
  h2 := (1,4,3,4,2)
  D := [[1, 4, 0, 0], [1, 4, 0, 1], [1, 4, 0, 2], [1, 4, 0, 3], [1, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_102_0 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T125_102
  T2 := Q2.T125_102_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_102_1 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T125_102
  T2 := Q2.T125_102_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_102_2 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T125_102
  T2 := Q2.T125_102_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_102_3 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T125_102
  T2 := Q2.T125_102_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_102_4 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T125_102
  T2 := Q2.T125_102_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_102_5 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T125_102
  T2 := Q2.T125_102_2
  h1 := (1,2,1,3,1)
  h2 := (1,2,1,3,1)
  D := [[1, 2, 1, 3], [1, 2, 1, 1], [1, 2, 1, 4], [1, 2, 1, 2], [1, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_102_10 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T125_102
  T2 := Q2.T125_102_2
  h1 := (2,4,2,3,2)
  h2 := (2,4,2,3,2)
  D := [[2, 4, 0, 0], [2, 4, 0, 1], [2, 4, 0, 2], [2, 4, 0, 3], [2, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_105_0 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T125_105
  T2 := Q2.T125_105_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_105_1 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T125_105
  T2 := Q2.T125_105_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_105_2 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T125_105
  T2 := Q2.T125_105_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_105_3 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T125_105
  T2 := Q2.T125_105_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_105_4 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T125_105
  T2 := Q2.T125_105_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_105_5 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T125_105
  T2 := Q2.T125_105_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_105_10 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T125_105
  T2 := Q2.T125_105_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_105_15 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T125_105
  T2 := Q2.T125_105_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_105_20 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T125_105
  T2 := Q2.T125_105_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_105_25 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T125_105
  T2 := Q2.T125_105_2
  h1 := (0,1,1,0,0)
  h2 := (0,1,1,0,0)
  D := [[0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_105_50 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T125_105
  T2 := Q2.T125_105_2
  h1 := (0,2,2,0,1)
  h2 := (0,2,2,0,1)
  D := [[0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_105_75 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T125_105
  T2 := Q2.T125_105_2
  h1 := (0,3,3,0,3)
  h2 := (0,3,3,0,3)
  D := [[0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_105_100 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T125_105
  T2 := Q2.T125_105_2
  h1 := (0,4,4,0,1)
  h2 := (0,4,4,0,1)
  D := [[0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_114_0 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T125_114
  T2 := Q2.T125_114_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_114_1 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T125_114
  T2 := Q2.T125_114_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_114_2 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T125_114
  T2 := Q2.T125_114_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_114_3 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T125_114
  T2 := Q2.T125_114_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_114_4 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T125_114
  T2 := Q2.T125_114_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_114_5 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T125_114
  T2 := Q2.T125_114_2
  h1 := (1,1,0,0,0)
  h2 := (1,1,0,0,0)
  D := [[1, 1, 4, 0], [1, 1, 4, 4], [1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_114_10 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T125_114
  T2 := Q2.T125_114_2
  h1 := (2,2,0,1,0)
  h2 := (2,2,0,1,0)
  D := [[2, 2, 2, 1], [2, 2, 2, 4], [2, 2, 2, 2], [2, 2, 2, 0], [2, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_114_15 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T125_114
  T2 := Q2.T125_114_2
  h1 := (3,3,0,3,1)
  h2 := (3,3,0,3,1)
  D := [[3, 3, 4, 4], [3, 3, 4, 1], [3, 3, 4, 3], [3, 3, 4, 0], [3, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_114_20 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T125_114
  T2 := Q2.T125_114_2
  h1 := (4,4,0,1,4)
  h2 := (4,4,0,1,4)
  D := [[4, 4, 0, 0], [4, 4, 0, 1], [4, 4, 0, 2], [4, 4, 0, 3], [4, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_125_0 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨125, by decide⟩
  m := 5
  T1 := T125_125
  T2 := Q2.T125_125_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_125_1 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨125, by decide⟩
  m := 5
  T1 := T125_125
  T2 := Q2.T125_125_2
  h1 := (0,1,1,0,0)
  h2 := (0,1,1,0,0)
  D := [[0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_125_2 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨125, by decide⟩
  m := 5
  T1 := T125_125
  T2 := Q2.T125_125_2
  h1 := (0,2,2,0,1)
  h2 := (0,2,2,0,1)
  D := [[0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_125_3 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨125, by decide⟩
  m := 5
  T1 := T125_125
  T2 := Q2.T125_125_2
  h1 := (0,3,3,0,3)
  h2 := (0,3,3,0,3)
  D := [[0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_125_4 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨125, by decide⟩
  m := 5
  T1 := T125_125
  T2 := Q2.T125_125_2
  h1 := (0,4,4,0,1)
  h2 := (0,4,4,0,1)
  D := [[0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_125_5 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨125, by decide⟩
  m := 5
  T1 := T125_125
  T2 := Q2.T125_125_2
  h1 := (1,0,4,0,1)
  h2 := (1,0,4,0,1)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_125_6 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨125, by decide⟩
  m := 5
  T1 := T125_125
  T2 := Q2.T125_125_2
  h1 := (1,1,0,0,0)
  h2 := (1,1,0,0,0)
  D := [[1, 1, 4, 0], [1, 1, 4, 4], [1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_125_7 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨125, by decide⟩
  m := 5
  T1 := T125_125
  T2 := Q2.T125_125_2
  h1 := (1,2,1,0,0)
  h2 := (1,2,1,0,0)
  D := [[1, 2, 3, 0], [1, 2, 3, 3], [1, 2, 3, 1], [1, 2, 3, 4], [1, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_125_8 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨125, by decide⟩
  m := 5
  T1 := T125_125
  T2 := Q2.T125_125_2
  h1 := (1,3,2,0,1)
  h2 := (1,3,2,0,1)
  D := [[1, 3, 2, 0], [1, 3, 2, 2], [1, 3, 2, 4], [1, 3, 2, 1], [1, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_125_9 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨125, by decide⟩
  m := 5
  T1 := T125_125
  T2 := Q2.T125_125_2
  h1 := (1,4,3,0,3)
  h2 := (1,4,3,0,3)
  D := [[1, 4, 1, 0], [1, 4, 1, 1], [1, 4, 1, 2], [1, 4, 1, 3], [1, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_125_10 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨125, by decide⟩
  m := 5
  T1 := T125_125
  T2 := Q2.T125_125_2
  h1 := (2,0,3,0,2)
  h2 := (2,0,3,0,2)
  D := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_125_11 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨125, by decide⟩
  m := 5
  T1 := T125_125
  T2 := Q2.T125_125_2
  h1 := (2,1,4,0,0)
  h2 := (2,1,4,0,0)
  D := [[2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3], [2, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_125_12 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨125, by decide⟩
  m := 5
  T1 := T125_125
  T2 := Q2.T125_125_2
  h1 := (2,2,0,0,4)
  h2 := (2,2,0,0,4)
  D := [[2, 2, 1, 2], [2, 2, 1, 0], [2, 2, 1, 3], [2, 2, 1, 1], [2, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_125_13 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨125, by decide⟩
  m := 5
  T1 := T125_125
  T2 := Q2.T125_125_2
  h1 := (2,3,1,0,4)
  h2 := (2,3,1,0,4)
  D := [[2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
