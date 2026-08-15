/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C031
import LeanDring.P5.Data.EntryK.C032

/-!
# Species-table cell data, stage 2 — column-data-divergent columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
cdd tier, chunk 10: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_125_52_20 : ColCertDiv where
  rK := ⟨125, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T125_52
  T2 := Q2.T125_52_2
  h1 := (4,4,0,2,2)
  h2 := (4,4,0,2,4)
  D1 := [[4, 4, 1, 4], [4, 4, 1, 0], [4, 4, 1, 1], [4, 4, 1, 2], [4, 4, 1, 3]]
  D2 := [[4, 4, 1, 1], [4, 4, 1, 2], [4, 4, 1, 3], [4, 4, 1, 4], [4, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_125_93_10 : ColCertDiv where
  rK := ⟨125, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T125_93
  T2 := Q2.T125_93_2
  h1 := (2,1,4,0,1)
  h2 := (2,1,4,0,2)
  D1 := [[2, 1, 3, 2], [2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3]]
  D2 := [[2, 1, 3, 3], [2, 1, 3, 2], [2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_125_93_15 : ColCertDiv where
  rK := ⟨125, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T125_93
  T2 := Q2.T125_93_2
  h1 := (3,4,1,2,2)
  h2 := (3,4,1,2,3)
  D1 := [[3, 4, 0, 1], [3, 4, 0, 2], [3, 4, 0, 3], [3, 4, 0, 4], [3, 4, 0, 0]]
  D2 := [[3, 4, 0, 2], [3, 4, 0, 3], [3, 4, 0, 4], [3, 4, 0, 0], [3, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_125_93_20 : ColCertDiv where
  rK := ⟨125, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T125_93
  T2 := Q2.T125_93_2
  h1 := (4,2,3,2,2)
  h2 := (4,2,3,2,4)
  D1 := [[4, 2, 4, 4], [4, 2, 4, 2], [4, 2, 4, 0], [4, 2, 4, 3], [4, 2, 4, 1]]
  D2 := [[4, 2, 4, 1], [4, 2, 4, 4], [4, 2, 4, 2], [4, 2, 4, 0], [4, 2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_125_96_10 : ColCertDiv where
  rK := ⟨125, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T125_96
  T2 := Q2.T125_96_2
  h1 := (2,3,1,2,1)
  h2 := (2,3,1,2,2)
  D1 := [[2, 3, 1, 1], [2, 3, 1, 3], [2, 3, 1, 0], [2, 3, 1, 2], [2, 3, 1, 4]]
  D2 := [[2, 3, 1, 2], [2, 3, 1, 4], [2, 3, 1, 1], [2, 3, 1, 3], [2, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_125_96_15 : ColCertDiv where
  rK := ⟨125, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T125_96
  T2 := Q2.T125_96_2
  h1 := (3,2,4,4,0)
  h2 := (3,2,4,4,2)
  D1 := [[3, 2, 3, 1], [3, 2, 3, 4], [3, 2, 3, 2], [3, 2, 3, 0], [3, 2, 3, 3]]
  D2 := [[3, 2, 3, 3], [3, 2, 3, 1], [3, 2, 3, 4], [3, 2, 3, 2], [3, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_125_96_20 : ColCertDiv where
  rK := ⟨125, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T125_96
  T2 := Q2.T125_96_2
  h1 := (4,1,2,0,3)
  h2 := (4,1,2,0,1)
  D1 := [[4, 1, 1, 4], [4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0]]
  D2 := [[4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4], [4, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_125_102_15 : ColCertDiv where
  rK := ⟨125, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T125_102
  T2 := Q2.T125_102_2
  h1 := (3,1,3,0,1)
  h2 := (3,1,3,0,2)
  D1 := [[3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2], [3, 1, 2, 1], [3, 1, 2, 0]]
  D2 := [[3, 1, 2, 0], [3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2], [3, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_125_102_20 : ColCertDiv where
  rK := ⟨125, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T125_102
  T2 := Q2.T125_102_2
  h1 := (4,3,4,4,3)
  h2 := (4,3,4,4,4)
  D1 := [[4, 3, 2, 0], [4, 3, 2, 2], [4, 3, 2, 4], [4, 3, 2, 1], [4, 3, 2, 3]]
  D2 := [[4, 3, 2, 1], [4, 3, 2, 3], [4, 3, 2, 0], [4, 3, 2, 2], [4, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_126_31_5 : ColCertDiv where
  rK := ⟨126, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T126_31
  T2 := Q2.T126_31_2
  h1 := (1,3,2,0,4)
  h2 := (1,3,2,0,0)
  D1 := [[1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0], [1, 3, 2, 2], [1, 3, 2, 4]]
  D2 := [[1, 3, 2, 2], [1, 3, 2, 4], [1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_126_31_10 : ColCertDiv where
  rK := ⟨126, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T126_31
  T2 := Q2.T126_31_2
  h1 := (2,1,4,3,0)
  h2 := (2,1,4,3,3)
  D1 := [[2, 1, 1, 0], [2, 1, 1, 4], [2, 1, 1, 3], [2, 1, 1, 2], [2, 1, 1, 1]]
  D2 := [[2, 1, 1, 3], [2, 1, 1, 2], [2, 1, 1, 1], [2, 1, 1, 0], [2, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_126_31_15 : ColCertDiv where
  rK := ⟨126, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T126_31
  T2 := Q2.T126_31_2
  h1 := (3,4,1,4,4)
  h2 := (3,4,1,4,3)
  D1 := [[3, 4, 2, 3], [3, 4, 2, 4], [3, 4, 2, 0], [3, 4, 2, 1], [3, 4, 2, 2]]
  D2 := [[3, 4, 2, 2], [3, 4, 2, 3], [3, 4, 2, 4], [3, 4, 2, 0], [3, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_126_31_20 : ColCertDiv where
  rK := ⟨126, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T126_31
  T2 := Q2.T126_31_2
  h1 := (4,2,3,3,1)
  h2 := (4,2,3,3,2)
  D1 := [[4, 2, 0, 0], [4, 2, 0, 3], [4, 2, 0, 1], [4, 2, 0, 4], [4, 2, 0, 2]]
  D2 := [[4, 2, 0, 1], [4, 2, 0, 4], [4, 2, 0, 2], [4, 2, 0, 0], [4, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_126_37_5 : ColCertDiv where
  rK := ⟨126, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T126_37
  T2 := Q2.T126_37_2
  h1 := (1,1,2,4,3)
  h2 := (1,1,2,4,1)
  D1 := [[1, 1, 3, 3], [1, 1, 3, 2], [1, 1, 3, 1], [1, 1, 3, 0], [1, 1, 3, 4]]
  D2 := [[1, 1, 3, 1], [1, 1, 3, 0], [1, 1, 3, 4], [1, 1, 3, 3], [1, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_126_37_10 : ColCertDiv where
  rK := ⟨126, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T126_37
  T2 := Q2.T126_37_2
  h1 := (2,2,4,4,2)
  h2 := (2,2,4,4,3)
  D1 := [[2, 2, 0, 1], [2, 2, 0, 4], [2, 2, 0, 2], [2, 2, 0, 0], [2, 2, 0, 3]]
  D2 := [[2, 2, 0, 2], [2, 2, 0, 0], [2, 2, 0, 3], [2, 2, 0, 1], [2, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_126_37_15 : ColCertDiv where
  rK := ⟨126, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T126_37
  T2 := Q2.T126_37_2
  h1 := (3,3,1,0,3)
  h2 := (3,3,1,0,2)
  D1 := [[3, 3, 1, 0], [3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3]]
  D2 := [[3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_126_37_20 : ColCertDiv where
  rK := ⟨126, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T126_37
  T2 := Q2.T126_37_2
  h1 := (4,4,3,2,2)
  h2 := (4,4,3,2,4)
  D1 := [[4, 4, 1, 1], [4, 4, 1, 2], [4, 4, 1, 3], [4, 4, 1, 4], [4, 4, 1, 0]]
  D2 := [[4, 4, 1, 3], [4, 4, 1, 4], [4, 4, 1, 0], [4, 4, 1, 1], [4, 4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_126_39_10 : ColCertDiv where
  rK := ⟨126, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T126_39
  T2 := Q2.T126_39_2
  h1 := (2,3,4,0,1)
  h2 := (2,3,4,0,2)
  D1 := [[2, 3, 4, 4], [2, 3, 4, 1], [2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2]]
  D2 := [[2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1], [2, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_126_39_15 : ColCertDiv where
  rK := ⟨126, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T126_39
  T2 := Q2.T126_39_2
  h1 := (3,2,1,1,0)
  h2 := (3,2,1,1,2)
  D1 := [[3, 2, 0, 0], [3, 2, 0, 3], [3, 2, 0, 1], [3, 2, 0, 4], [3, 2, 0, 2]]
  D2 := [[3, 2, 0, 2], [3, 2, 0, 0], [3, 2, 0, 3], [3, 2, 0, 1], [3, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_126_39_20 : ColCertDiv where
  rK := ⟨126, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T126_39
  T2 := Q2.T126_39_2
  h1 := (4,1,3,1,3)
  h2 := (4,1,3,1,1)
  D1 := [[4, 1, 2, 2], [4, 1, 2, 1], [4, 1, 2, 0], [4, 1, 2, 4], [4, 1, 2, 3]]
  D2 := [[4, 1, 2, 0], [4, 1, 2, 4], [4, 1, 2, 3], [4, 1, 2, 2], [4, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_126_45_5 : ColCertDiv where
  rK := ⟨126, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T126_45
  T2 := Q2.T126_45_2
  h1 := (1,2,2,2,1)
  h2 := (1,2,2,2,3)
  D1 := [[1, 2, 0, 2], [1, 2, 0, 0], [1, 2, 0, 3], [1, 2, 0, 1], [1, 2, 0, 4]]
  D2 := [[1, 2, 0, 4], [1, 2, 0, 2], [1, 2, 0, 0], [1, 2, 0, 3], [1, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_126_45_10 : ColCertDiv where
  rK := ⟨126, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T126_45
  T2 := Q2.T126_45_2
  h1 := (2,4,4,1,3)
  h2 := (2,4,4,1,2)
  D1 := [[2, 4, 3, 0], [2, 4, 3, 1], [2, 4, 3, 2], [2, 4, 3, 3], [2, 4, 3, 4]]
  D2 := [[2, 4, 3, 4], [2, 4, 3, 0], [2, 4, 3, 1], [2, 4, 3, 2], [2, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_126_45_15 : ColCertDiv where
  rK := ⟨126, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T126_45
  T2 := Q2.T126_45_2
  h1 := (3,1,1,2,4)
  h2 := (3,1,1,2,1)
  D1 := [[3, 1, 4, 2], [3, 1, 4, 1], [3, 1, 4, 0], [3, 1, 4, 4], [3, 1, 4, 3]]
  D2 := [[3, 1, 4, 4], [3, 1, 4, 3], [3, 1, 4, 2], [3, 1, 4, 1], [3, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_126_45_20 : ColCertDiv where
  rK := ⟨126, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T126_45
  T2 := Q2.T126_45_2
  h1 := (4,3,3,0,4)
  h2 := (4,3,3,0,3)
  D1 := [[4, 3, 3, 3], [4, 3, 3, 0], [4, 3, 3, 2], [4, 3, 3, 4], [4, 3, 3, 1]]
  D2 := [[4, 3, 3, 2], [4, 3, 3, 4], [4, 3, 3, 1], [4, 3, 3, 3], [4, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_126_48_5 : ColCertDiv where
  rK := ⟨126, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T126_48
  T2 := Q2.T126_48_2
  h1 := (0,1,0,4,3)
  h2 := (0,1,0,4,1)
  D1 := [[0, 1, 4, 1], [0, 1, 4, 0], [0, 1, 4, 4], [0, 1, 4, 3], [0, 1, 4, 2]]
  D2 := [[0, 1, 4, 4], [0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1], [0, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_126_48_10 : ColCertDiv where
  rK := ⟨126, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T126_48
  T2 := Q2.T126_48_2
  h1 := (0,2,0,3,1)
  h2 := (0,2,0,3,2)
  D1 := [[0, 2, 3, 2], [0, 2, 3, 0], [0, 2, 3, 3], [0, 2, 3, 1], [0, 2, 3, 4]]
  D2 := [[0, 2, 3, 3], [0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2], [0, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_126_48_15 : ColCertDiv where
  rK := ⟨126, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T126_48
  T2 := Q2.T126_48_2
  h1 := (0,3,0,2,4)
  h2 := (0,3,0,2,3)
  D1 := [[0, 3, 2, 3], [0, 3, 2, 0], [0, 3, 2, 2], [0, 3, 2, 4], [0, 3, 2, 1]]
  D2 := [[0, 3, 2, 2], [0, 3, 2, 4], [0, 3, 2, 1], [0, 3, 2, 3], [0, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_126_48_20 : ColCertDiv where
  rK := ⟨126, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T126_48
  T2 := Q2.T126_48_2
  h1 := (0,4,0,1,2)
  h2 := (0,4,0,1,4)
  D1 := [[0, 4, 1, 4], [0, 4, 1, 0], [0, 4, 1, 1], [0, 4, 1, 2], [0, 4, 1, 3]]
  D2 := [[0, 4, 1, 1], [0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4], [0, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_126_93_10 : ColCertDiv where
  rK := ⟨126, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T126_93
  T2 := Q2.T126_93_2
  h1 := (2,1,4,0,1)
  h2 := (2,1,4,0,2)
  D1 := [[2, 1, 3, 2], [2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3]]
  D2 := [[2, 1, 3, 3], [2, 1, 3, 2], [2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_126_93_15 : ColCertDiv where
  rK := ⟨126, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T126_93
  T2 := Q2.T126_93_2
  h1 := (3,4,1,2,2)
  h2 := (3,4,1,2,3)
  D1 := [[3, 4, 0, 2], [3, 4, 0, 3], [3, 4, 0, 4], [3, 4, 0, 0], [3, 4, 0, 1]]
  D2 := [[3, 4, 0, 3], [3, 4, 0, 4], [3, 4, 0, 0], [3, 4, 0, 1], [3, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_126_93_20 : ColCertDiv where
  rK := ⟨126, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T126_93
  T2 := Q2.T126_93_2
  h1 := (4,2,3,2,2)
  h2 := (4,2,3,2,4)
  D1 := [[4, 2, 4, 0], [4, 2, 4, 3], [4, 2, 4, 1], [4, 2, 4, 4], [4, 2, 4, 2]]
  D2 := [[4, 2, 4, 2], [4, 2, 4, 0], [4, 2, 4, 3], [4, 2, 4, 1], [4, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_126_101_10 : ColCertDiv where
  rK := ⟨126, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T126_101
  T2 := Q2.T126_101_2
  h1 := (2,3,4,2,4)
  h2 := (2,3,4,2,0)
  D1 := [[2, 3, 1, 3], [2, 3, 1, 0], [2, 3, 1, 2], [2, 3, 1, 4], [2, 3, 1, 1]]
  D2 := [[2, 3, 1, 4], [2, 3, 1, 1], [2, 3, 1, 3], [2, 3, 1, 0], [2, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_126_101_15 : ColCertDiv where
  rK := ⟨126, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T126_101
  T2 := Q2.T126_101_2
  h1 := (3,2,1,4,1)
  h2 := (3,2,1,4,3)
  D1 := [[3, 2, 3, 2], [3, 2, 3, 0], [3, 2, 3, 3], [3, 2, 3, 1], [3, 2, 3, 4]]
  D2 := [[3, 2, 3, 4], [3, 2, 3, 2], [3, 2, 3, 0], [3, 2, 3, 3], [3, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_126_101_20 : ColCertDiv where
  rK := ⟨126, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T126_101
  T2 := Q2.T126_101_2
  h1 := (4,1,3,0,3)
  h2 := (4,1,3,0,1)
  D1 := [[4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4], [4, 1, 1, 3], [4, 1, 1, 2]]
  D2 := [[4, 1, 1, 4], [4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_126_107_15 : ColCertDiv where
  rK := ⟨126, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T126_107
  T2 := Q2.T126_107_2
  h1 := (3,1,1,0,1)
  h2 := (3,1,1,0,2)
  D1 := [[3, 1, 2, 0], [3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2], [3, 1, 2, 1]]
  D2 := [[3, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_126_107_20 : ColCertDiv where
  rK := ⟨126, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T126_107
  T2 := Q2.T126_107_2
  h1 := (4,3,3,4,2)
  h2 := (4,3,3,4,3)
  D1 := [[4, 3, 2, 0], [4, 3, 2, 2], [4, 3, 2, 4], [4, 3, 2, 1], [4, 3, 2, 3]]
  D2 := [[4, 3, 2, 1], [4, 3, 2, 3], [4, 3, 2, 0], [4, 3, 2, 2], [4, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_3_1 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T127_3
  T2 := Q2.T127_3_2
  h1 := (1,0,2,3,1)
  h2 := (1,0,2,3,1)
  D1 := [[1, 0, 4, 3], [1, 0, 4, 3], [1, 0, 4, 3], [1, 0, 4, 3], [1, 0, 4, 3]]
  D2 := [[1, 0, 4, 2], [1, 0, 4, 2], [1, 0, 4, 2], [1, 0, 4, 2], [1, 0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_3_2 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T127_3
  T2 := Q2.T127_3_2
  h1 := (2,0,4,1,0)
  h2 := (2,0,4,1,0)
  D1 := [[2, 0, 3, 2], [2, 0, 3, 2], [2, 0, 3, 2], [2, 0, 3, 2], [2, 0, 3, 2]]
  D2 := [[2, 0, 3, 0], [2, 0, 3, 0], [2, 0, 3, 0], [2, 0, 3, 0], [2, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_3_3 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T127_3
  T2 := Q2.T127_3_2
  h1 := (3,0,1,4,2)
  h2 := (3,0,1,4,2)
  D1 := [[3, 0, 2, 2], [3, 0, 2, 2], [3, 0, 2, 2], [3, 0, 2, 2], [3, 0, 2, 2]]
  D2 := [[3, 0, 2, 4], [3, 0, 2, 4], [3, 0, 2, 4], [3, 0, 2, 4], [3, 0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_3_4 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T127_3
  T2 := Q2.T127_3_2
  h1 := (4,0,3,2,2)
  h2 := (4,0,3,2,2)
  D1 := [[4, 0, 1, 3], [4, 0, 1, 3], [4, 0, 1, 3], [4, 0, 1, 3], [4, 0, 1, 3]]
  D2 := [[4, 0, 1, 4], [4, 0, 1, 4], [4, 0, 1, 4], [4, 0, 1, 4], [4, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_21_5 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T127_21
  T2 := Q2.T127_21_2
  h1 := (1,0,2,3,2)
  h2 := (1,0,2,3,2)
  D1 := [[1, 0, 4, 4], [1, 0, 4, 4], [1, 0, 4, 4], [1, 0, 4, 4], [1, 0, 4, 4]]
  D2 := [[1, 0, 4, 3], [1, 0, 4, 3], [1, 0, 4, 3], [1, 0, 4, 3], [1, 0, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_21_10 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T127_21
  T2 := Q2.T127_21_2
  h1 := (2,0,4,1,2)
  h2 := (2,0,4,1,2)
  D1 := [[2, 0, 3, 4], [2, 0, 3, 4], [2, 0, 3, 4], [2, 0, 3, 4], [2, 0, 3, 4]]
  D2 := [[2, 0, 3, 2], [2, 0, 3, 2], [2, 0, 3, 2], [2, 0, 3, 2], [2, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_21_15 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T127_21
  T2 := Q2.T127_21_2
  h1 := (3,0,1,4,0)
  h2 := (3,0,1,4,0)
  D1 := [[3, 0, 2, 0], [3, 0, 2, 0], [3, 0, 2, 0], [3, 0, 2, 0], [3, 0, 2, 0]]
  D2 := [[3, 0, 2, 2], [3, 0, 2, 2], [3, 0, 2, 2], [3, 0, 2, 2], [3, 0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_21_20 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T127_21
  T2 := Q2.T127_21_2
  h1 := (4,0,3,2,1)
  h2 := (4,0,3,2,1)
  D1 := [[4, 0, 1, 2], [4, 0, 1, 2], [4, 0, 1, 2], [4, 0, 1, 2], [4, 0, 1, 2]]
  D2 := [[4, 0, 1, 3], [4, 0, 1, 3], [4, 0, 1, 3], [4, 0, 1, 3], [4, 0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_32_5 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T127_32
  T2 := Q2.T127_32_2
  h1 := (1,1,4,4,0)
  h2 := (1,1,4,4,3)
  D1 := [[1, 1, 4, 4], [1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1], [1, 1, 4, 0]]
  D2 := [[1, 1, 4, 0], [1, 1, 4, 4], [1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_32_10 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T127_32
  T2 := Q2.T127_32_2
  h1 := (2,2,3,4,3)
  h2 := (2,2,3,4,4)
  D1 := [[2, 2, 2, 2], [2, 2, 2, 0], [2, 2, 2, 3], [2, 2, 2, 1], [2, 2, 2, 4]]
  D2 := [[2, 2, 2, 4], [2, 2, 2, 2], [2, 2, 2, 0], [2, 2, 2, 3], [2, 2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_32_15 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T127_32
  T2 := Q2.T127_32_2
  h1 := (3,3,2,0,0)
  h2 := (3,3,2,0,4)
  D1 := [[3, 3, 4, 0], [3, 3, 4, 2], [3, 3, 4, 4], [3, 3, 4, 1], [3, 3, 4, 3]]
  D2 := [[3, 3, 4, 3], [3, 3, 4, 0], [3, 3, 4, 2], [3, 3, 4, 4], [3, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_32_20 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T127_32
  T2 := Q2.T127_32_2
  h1 := (4,4,1,2,2)
  h2 := (4,4,1,2,4)
  D1 := [[4, 4, 0, 4], [4, 4, 0, 0], [4, 4, 0, 1], [4, 4, 0, 2], [4, 4, 0, 3]]
  D2 := [[4, 4, 0, 3], [4, 4, 0, 4], [4, 4, 0, 0], [4, 4, 0, 1], [4, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_33_5 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T127_33
  T2 := Q2.T127_33_2
  h1 := (0,1,2,4,0)
  h2 := (0,1,2,4,3)
  D1 := [[0, 1, 4, 2], [0, 1, 4, 1], [0, 1, 4, 0], [0, 1, 4, 4], [0, 1, 4, 3]]
  D2 := [[0, 1, 4, 4], [0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1], [0, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_33_10 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T127_33
  T2 := Q2.T127_33_2
  h1 := (0,2,4,3,2)
  h2 := (0,2,4,3,3)
  D1 := [[0, 2, 3, 4], [0, 2, 3, 2], [0, 2, 3, 0], [0, 2, 3, 3], [0, 2, 3, 1]]
  D2 := [[0, 2, 3, 3], [0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2], [0, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_33_15 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T127_33
  T2 := Q2.T127_33_2
  h1 := (0,3,1,2,1)
  h2 := (0,3,1,2,0)
  D1 := [[0, 3, 2, 1], [0, 3, 2, 3], [0, 3, 2, 0], [0, 3, 2, 2], [0, 3, 2, 4]]
  D2 := [[0, 3, 2, 2], [0, 3, 2, 4], [0, 3, 2, 1], [0, 3, 2, 3], [0, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_33_20 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T127_33
  T2 := Q2.T127_33_2
  h1 := (0,4,3,1,2)
  h2 := (0,4,3,1,4)
  D1 := [[0, 4, 1, 3], [0, 4, 1, 4], [0, 4, 1, 0], [0, 4, 1, 1], [0, 4, 1, 2]]
  D2 := [[0, 4, 1, 1], [0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4], [0, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_40_5 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T127_40
  T2 := Q2.T127_40_2
  h1 := (1,2,1,2,4)
  h2 := (1,2,1,2,1)
  D1 := [[1, 2, 1, 1], [1, 2, 1, 4], [1, 2, 1, 2], [1, 2, 1, 0], [1, 2, 1, 3]]
  D2 := [[1, 2, 1, 0], [1, 2, 1, 3], [1, 2, 1, 1], [1, 2, 1, 4], [1, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_40_10 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T127_40
  T2 := Q2.T127_40_2
  h1 := (2,4,2,1,2)
  h2 := (2,4,2,1,1)
  D1 := [[2, 4, 0, 2], [2, 4, 0, 3], [2, 4, 0, 4], [2, 4, 0, 0], [2, 4, 0, 1]]
  D2 := [[2, 4, 0, 0], [2, 4, 0, 1], [2, 4, 0, 2], [2, 4, 0, 3], [2, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_40_15 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T127_40
  T2 := Q2.T127_40_2
  h1 := (3,1,3,2,2)
  h2 := (3,1,3,2,4)
  D1 := [[3, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2]]
  D2 := [[3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2], [3, 1, 2, 1], [3, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_40_20 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T127_40
  T2 := Q2.T127_40_2
  h1 := (4,3,4,0,4)
  h2 := (4,3,4,0,3)
  D1 := [[4, 3, 2, 3], [4, 3, 2, 0], [4, 3, 2, 2], [4, 3, 2, 4], [4, 3, 2, 1]]
  D2 := [[4, 3, 2, 0], [4, 3, 2, 2], [4, 3, 2, 4], [4, 3, 2, 1], [4, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_46_5 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T127_46
  T2 := Q2.T127_46_2
  h1 := (1,3,3,0,2)
  h2 := (1,3,3,0,3)
  D1 := [[1, 3, 3, 0], [1, 3, 3, 2], [1, 3, 3, 4], [1, 3, 3, 1], [1, 3, 3, 3]]
  D2 := [[1, 3, 3, 2], [1, 3, 3, 4], [1, 3, 3, 1], [1, 3, 3, 3], [1, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_46_15 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T127_46
  T2 := Q2.T127_46_2
  h1 := (3,4,4,4,2)
  h2 := (3,4,4,4,1)
  D1 := [[3, 4, 0, 2], [3, 4, 0, 3], [3, 4, 0, 4], [3, 4, 0, 0], [3, 4, 0, 1]]
  D2 := [[3, 4, 0, 4], [3, 4, 0, 0], [3, 4, 0, 1], [3, 4, 0, 2], [3, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_49_10 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T127_49
  T2 := Q2.T127_49_2
  h1 := (2,3,0,0,2)
  h2 := (2,3,0,0,3)
  D1 := [[2, 3, 1, 0], [2, 3, 1, 2], [2, 3, 1, 4], [2, 3, 1, 1], [2, 3, 1, 3]]
  D2 := [[2, 3, 1, 1], [2, 3, 1, 3], [2, 3, 1, 0], [2, 3, 1, 2], [2, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_49_15 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T127_49
  T2 := Q2.T127_49_2
  h1 := (3,2,0,1,2)
  h2 := (3,2,0,1,4)
  D1 := [[3, 2, 3, 0], [3, 2, 3, 3], [3, 2, 3, 1], [3, 2, 3, 4], [3, 2, 3, 2]]
  D2 := [[3, 2, 3, 2], [3, 2, 3, 0], [3, 2, 3, 3], [3, 2, 3, 1], [3, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
