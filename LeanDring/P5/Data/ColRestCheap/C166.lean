/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C017

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 165: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_73_73_35 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (1,3,2,4,0)
  h2 := (1,3,2,4,0)
  D := [[1, 2, 1], [1, 2, 0], [1, 2, 4], [1, 2, 3], [1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_40 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (1,3,3,1,0)
  h2 := (1,3,3,1,0)
  D := [[1, 3, 1], [1, 3, 0], [1, 3, 4], [1, 3, 3], [1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_45 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (1,3,4,3,0)
  h2 := (1,3,4,3,0)
  D := [[1, 4, 1], [1, 4, 0], [1, 4, 4], [1, 4, 3], [1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_50 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (2,1,0,3,1)
  h2 := (2,1,0,3,2)
  D := [[2, 0, 2], [2, 0, 0], [2, 0, 3], [2, 0, 1], [2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_55 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (2,1,1,0,1)
  h2 := (2,1,1,0,2)
  D := [[2, 1, 2], [2, 1, 0], [2, 1, 3], [2, 1, 1], [2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_60 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (2,1,2,2,1)
  h2 := (2,1,2,2,2)
  D := [[2, 2, 2], [2, 2, 0], [2, 2, 3], [2, 2, 1], [2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_65 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (2,1,3,4,1)
  h2 := (2,1,3,4,2)
  D := [[2, 3, 2], [2, 3, 0], [2, 3, 3], [2, 3, 1], [2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_70 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (2,1,4,1,1)
  h2 := (2,1,4,1,2)
  D := [[2, 4, 2], [2, 4, 0], [2, 4, 3], [2, 4, 1], [2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_75 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (3,4,0,4,4)
  h2 := (3,4,0,4,0)
  D := [[3, 0, 3], [3, 0, 0], [3, 0, 2], [3, 0, 4], [3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_80 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (3,4,1,1,4)
  h2 := (3,4,1,1,0)
  D := [[3, 1, 3], [3, 1, 0], [3, 1, 2], [3, 1, 4], [3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_85 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (3,4,2,3,4)
  h2 := (3,4,2,3,0)
  D := [[3, 2, 3], [3, 2, 0], [3, 2, 2], [3, 2, 4], [3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_90 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (3,4,3,0,4)
  h2 := (3,4,3,0,0)
  D := [[3, 3, 3], [3, 3, 0], [3, 3, 2], [3, 3, 4], [3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_95 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (3,4,4,2,4)
  h2 := (3,4,4,2,0)
  D := [[3, 4, 3], [3, 4, 0], [3, 4, 2], [3, 4, 4], [3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_100 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (4,2,0,3,4)
  h2 := (4,2,0,3,1)
  D := [[4, 0, 4], [4, 0, 0], [4, 0, 1], [4, 0, 2], [4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_105 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (4,2,1,0,4)
  h2 := (4,2,1,0,1)
  D := [[4, 1, 4], [4, 1, 0], [4, 1, 1], [4, 1, 2], [4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_110 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (4,2,2,2,4)
  h2 := (4,2,2,2,1)
  D := [[4, 2, 4], [4, 2, 0], [4, 2, 1], [4, 2, 2], [4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_115 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (4,2,3,4,4)
  h2 := (4,2,3,4,1)
  D := [[4, 3, 4], [4, 3, 0], [4, 3, 1], [4, 3, 2], [4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_120 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (4,2,4,1,4)
  h2 := (4,2,4,1,1)
  D := [[4, 4, 4], [4, 4, 0], [4, 4, 1], [4, 4, 2], [4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_0_0 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨0, by decide⟩
  m := 25
  T1 := T74_0
  T2 := Q2.T74_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_8_0 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T74_8
  T2 := Q2.T74_8_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_8_1 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T74_8
  T2 := Q2.T74_8_2
  h1 := (0,0,1,1,4)
  h2 := (0,0,1,1,4)
  D := [[0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_8_2 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T74_8
  T2 := Q2.T74_8_2
  h1 := (0,0,2,2,3)
  h2 := (0,0,2,2,3)
  D := [[0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_8_3 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T74_8
  T2 := Q2.T74_8_2
  h1 := (0,0,3,3,2)
  h2 := (0,0,3,3,2)
  D := [[0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_8_4 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T74_8
  T2 := Q2.T74_8_2
  h1 := (0,0,4,4,1)
  h2 := (0,0,4,4,1)
  D := [[0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_12_0 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T74_12
  T2 := Q2.T74_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_12_1 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T74_12
  T2 := Q2.T74_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_12_2 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T74_12
  T2 := Q2.T74_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_12_3 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T74_12
  T2 := Q2.T74_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_12_4 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T74_12
  T2 := Q2.T74_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_26_0 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T74_26
  T2 := Q2.T74_26_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_26_1 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T74_26
  T2 := Q2.T74_26_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_26_2 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T74_26
  T2 := Q2.T74_26_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_26_3 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T74_26
  T2 := Q2.T74_26_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_26_4 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T74_26
  T2 := Q2.T74_26_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_26_5 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T74_26
  T2 := Q2.T74_26_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_26_10 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T74_26
  T2 := Q2.T74_26_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_26_15 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T74_26
  T2 := Q2.T74_26_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_26_20 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T74_26
  T2 := Q2.T74_26_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_31_0 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T74_31
  T2 := Q2.T74_31_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_31_1 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T74_31
  T2 := Q2.T74_31_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_31_2 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T74_31
  T2 := Q2.T74_31_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_31_3 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T74_31
  T2 := Q2.T74_31_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_31_4 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T74_31
  T2 := Q2.T74_31_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_36_0 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T74_36
  T2 := Q2.T74_36_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_36_1 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T74_36
  T2 := Q2.T74_36_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_36_2 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T74_36
  T2 := Q2.T74_36_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_36_3 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T74_36
  T2 := Q2.T74_36_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_36_4 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T74_36
  T2 := Q2.T74_36_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_41_0 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T74_41
  T2 := Q2.T74_41_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_41_1 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T74_41
  T2 := Q2.T74_41_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_41_2 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T74_41
  T2 := Q2.T74_41_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_41_3 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T74_41
  T2 := Q2.T74_41_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_41_4 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T74_41
  T2 := Q2.T74_41_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_46_0 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T74_46
  T2 := Q2.T74_46_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_46_1 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T74_46
  T2 := Q2.T74_46_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_46_2 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T74_46
  T2 := Q2.T74_46_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_46_3 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T74_46
  T2 := Q2.T74_46_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_46_4 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T74_46
  T2 := Q2.T74_46_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_51_0 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T74_51
  T2 := Q2.T74_51_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_51_1 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T74_51
  T2 := Q2.T74_51_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
