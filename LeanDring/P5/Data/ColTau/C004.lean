/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C019
import LeanDring.P5.Data.EntryK.C020

/-!
# Species-table cell data, stage 2 — τ-moved columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
tau tier, chunk 3: 24 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_80_13_5 : ColCertDiv where
  rK := ⟨80, by decide⟩
  rH := ⟨13, by decide⟩
  m := 25
  T1 := T80_13
  T2 := Q2.T80_13_2
  h1 := (0,0,1,0,4)
  h2 := (0,0,1,0,4)
  D1 := [[1, 0, 4], [1, 0, 0], [1, 0, 1], [1, 0, 2], [1, 0, 3], [1, 0, 4], [1, 0, 0], [1, 0, 1], [1, 0, 2], [1, 0, 3], [1, 0, 4], [1, 0, 0], [1, 0, 1], [1, 0, 2], [1, 0, 3], [1, 0, 4], [1, 0, 0], [1, 0, 1], [1, 0, 2], [1, 0, 3], [1, 0, 4], [1, 0, 0], [1, 0, 1], [1, 0, 2], [1, 0, 3]]
  D2 := [[1, 0, 4], [1, 0, 0], [1, 0, 1], [1, 0, 2], [1, 0, 3], [1, 0, 4], [1, 0, 0], [1, 0, 1], [1, 0, 2], [1, 0, 3], [1, 0, 4], [1, 0, 0], [1, 0, 1], [1, 0, 2], [1, 0, 3], [1, 0, 4], [1, 0, 0], [1, 0, 1], [1, 0, 2], [1, 0, 3], [1, 0, 4], [1, 0, 0], [1, 0, 1], [1, 0, 2], [1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_80_13_6 : ColCertDiv where
  rK := ⟨80, by decide⟩
  rH := ⟨13, by decide⟩
  m := 25
  T1 := T80_13
  T2 := Q2.T80_13_2
  h1 := (0,0,1,1,4)
  h2 := (0,0,1,1,4)
  D1 := [[1, 1, 4], [1, 1, 0], [1, 1, 1], [1, 1, 2], [1, 1, 3], [1, 1, 0], [1, 1, 1], [1, 1, 2], [1, 1, 3], [1, 1, 4], [1, 1, 1], [1, 1, 2], [1, 1, 3], [1, 1, 4], [1, 1, 0], [1, 1, 2], [1, 1, 3], [1, 1, 4], [1, 1, 0], [1, 1, 1], [1, 1, 3], [1, 1, 4], [1, 1, 0], [1, 1, 1], [1, 1, 2]]
  D2 := [[1, 1, 4], [1, 1, 0], [1, 1, 1], [1, 1, 2], [1, 1, 3], [1, 1, 0], [1, 1, 1], [1, 1, 2], [1, 1, 3], [1, 1, 4], [1, 1, 1], [1, 1, 2], [1, 1, 3], [1, 1, 4], [1, 1, 0], [1, 1, 2], [1, 1, 3], [1, 1, 4], [1, 1, 0], [1, 1, 1], [1, 1, 3], [1, 1, 4], [1, 1, 0], [1, 1, 1], [1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_80_13_7 : ColCertDiv where
  rK := ⟨80, by decide⟩
  rH := ⟨13, by decide⟩
  m := 25
  T1 := T80_13
  T2 := Q2.T80_13_2
  h1 := (0,0,1,2,4)
  h2 := (0,0,1,2,4)
  D1 := [[1, 2, 4], [1, 2, 0], [1, 2, 1], [1, 2, 2], [1, 2, 3], [1, 2, 1], [1, 2, 2], [1, 2, 3], [1, 2, 4], [1, 2, 0], [1, 2, 3], [1, 2, 4], [1, 2, 0], [1, 2, 1], [1, 2, 2], [1, 2, 0], [1, 2, 1], [1, 2, 2], [1, 2, 3], [1, 2, 4], [1, 2, 2], [1, 2, 3], [1, 2, 4], [1, 2, 0], [1, 2, 1]]
  D2 := [[1, 2, 4], [1, 2, 0], [1, 2, 1], [1, 2, 2], [1, 2, 3], [1, 2, 1], [1, 2, 2], [1, 2, 3], [1, 2, 4], [1, 2, 0], [1, 2, 3], [1, 2, 4], [1, 2, 0], [1, 2, 1], [1, 2, 2], [1, 2, 0], [1, 2, 1], [1, 2, 2], [1, 2, 3], [1, 2, 4], [1, 2, 2], [1, 2, 3], [1, 2, 4], [1, 2, 0], [1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_80_13_8 : ColCertDiv where
  rK := ⟨80, by decide⟩
  rH := ⟨13, by decide⟩
  m := 25
  T1 := T80_13
  T2 := Q2.T80_13_2
  h1 := (0,0,1,3,4)
  h2 := (0,0,1,3,4)
  D1 := [[1, 3, 4], [1, 3, 0], [1, 3, 1], [1, 3, 2], [1, 3, 3], [1, 3, 2], [1, 3, 3], [1, 3, 4], [1, 3, 0], [1, 3, 1], [1, 3, 0], [1, 3, 1], [1, 3, 2], [1, 3, 3], [1, 3, 4], [1, 3, 3], [1, 3, 4], [1, 3, 0], [1, 3, 1], [1, 3, 2], [1, 3, 1], [1, 3, 2], [1, 3, 3], [1, 3, 4], [1, 3, 0]]
  D2 := [[1, 3, 4], [1, 3, 0], [1, 3, 1], [1, 3, 2], [1, 3, 3], [1, 3, 2], [1, 3, 3], [1, 3, 4], [1, 3, 0], [1, 3, 1], [1, 3, 0], [1, 3, 1], [1, 3, 2], [1, 3, 3], [1, 3, 4], [1, 3, 3], [1, 3, 4], [1, 3, 0], [1, 3, 1], [1, 3, 2], [1, 3, 1], [1, 3, 2], [1, 3, 3], [1, 3, 4], [1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_85_85_50 : ColCertDiv where
  rK := ⟨85, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T85_85
  T2 := Q2.T85_85_2
  h1 := (2,0,0,3,2)
  h2 := (2,0,0,3,2)
  D1 := [[2, 0, 2], [2, 0, 0], [2, 0, 3], [2, 0, 1], [2, 0, 4]]
  D2 := [[2, 0, 2], [2, 0, 0], [2, 0, 3], [2, 0, 1], [2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_85_85_55 : ColCertDiv where
  rK := ⟨85, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T85_85
  T2 := Q2.T85_85_2
  h1 := (2,0,1,3,2)
  h2 := (2,0,1,3,2)
  D1 := [[2, 1, 2], [2, 1, 0], [2, 1, 3], [2, 1, 1], [2, 1, 4]]
  D2 := [[2, 1, 2], [2, 1, 0], [2, 1, 3], [2, 1, 1], [2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_85_85_60 : ColCertDiv where
  rK := ⟨85, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T85_85
  T2 := Q2.T85_85_2
  h1 := (2,0,2,3,2)
  h2 := (2,0,2,3,2)
  D1 := [[2, 2, 2], [2, 2, 0], [2, 2, 3], [2, 2, 1], [2, 2, 4]]
  D2 := [[2, 2, 2], [2, 2, 0], [2, 2, 3], [2, 2, 1], [2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_85_85_65 : ColCertDiv where
  rK := ⟨85, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T85_85
  T2 := Q2.T85_85_2
  h1 := (2,0,3,3,2)
  h2 := (2,0,3,3,2)
  D1 := [[2, 3, 2], [2, 3, 0], [2, 3, 3], [2, 3, 1], [2, 3, 4]]
  D2 := [[2, 3, 2], [2, 3, 0], [2, 3, 3], [2, 3, 1], [2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_85_85_70 : ColCertDiv where
  rK := ⟨85, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T85_85
  T2 := Q2.T85_85_2
  h1 := (2,0,4,3,2)
  h2 := (2,0,4,3,2)
  D1 := [[2, 4, 2], [2, 4, 0], [2, 4, 3], [2, 4, 1], [2, 4, 4]]
  D2 := [[2, 4, 2], [2, 4, 0], [2, 4, 3], [2, 4, 1], [2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_85_85_75 : ColCertDiv where
  rK := ⟨85, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T85_85
  T2 := Q2.T85_85_2
  h1 := (3,0,0,2,4)
  h2 := (3,0,0,2,4)
  D1 := [[3, 0, 3], [3, 0, 0], [3, 0, 2], [3, 0, 4], [3, 0, 1]]
  D2 := [[3, 0, 3], [3, 0, 0], [3, 0, 2], [3, 0, 4], [3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_85_85_80 : ColCertDiv where
  rK := ⟨85, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T85_85
  T2 := Q2.T85_85_2
  h1 := (3,0,1,2,4)
  h2 := (3,0,1,2,4)
  D1 := [[3, 1, 3], [3, 1, 0], [3, 1, 2], [3, 1, 4], [3, 1, 1]]
  D2 := [[3, 1, 3], [3, 1, 0], [3, 1, 2], [3, 1, 4], [3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_85_85_85 : ColCertDiv where
  rK := ⟨85, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T85_85
  T2 := Q2.T85_85_2
  h1 := (3,0,2,2,4)
  h2 := (3,0,2,2,4)
  D1 := [[3, 2, 3], [3, 2, 0], [3, 2, 2], [3, 2, 4], [3, 2, 1]]
  D2 := [[3, 2, 3], [3, 2, 0], [3, 2, 2], [3, 2, 4], [3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_85_85_90 : ColCertDiv where
  rK := ⟨85, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T85_85
  T2 := Q2.T85_85_2
  h1 := (3,0,3,2,4)
  h2 := (3,0,3,2,4)
  D1 := [[3, 3, 3], [3, 3, 0], [3, 3, 2], [3, 3, 4], [3, 3, 1]]
  D2 := [[3, 3, 3], [3, 3, 0], [3, 3, 2], [3, 3, 4], [3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_85_85_95 : ColCertDiv where
  rK := ⟨85, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T85_85
  T2 := Q2.T85_85_2
  h1 := (3,0,4,2,4)
  h2 := (3,0,4,2,4)
  D1 := [[3, 4, 3], [3, 4, 0], [3, 4, 2], [3, 4, 4], [3, 4, 1]]
  D2 := [[3, 4, 3], [3, 4, 0], [3, 4, 2], [3, 4, 4], [3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_85_85_100 : ColCertDiv where
  rK := ⟨85, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T85_85
  T2 := Q2.T85_85_2
  h1 := (4,0,0,1,0)
  h2 := (4,0,0,1,0)
  D1 := [[4, 0, 4], [4, 0, 0], [4, 0, 1], [4, 0, 2], [4, 0, 3]]
  D2 := [[4, 0, 4], [4, 0, 0], [4, 0, 1], [4, 0, 2], [4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_85_85_105 : ColCertDiv where
  rK := ⟨85, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T85_85
  T2 := Q2.T85_85_2
  h1 := (4,0,1,1,0)
  h2 := (4,0,1,1,0)
  D1 := [[4, 1, 4], [4, 1, 0], [4, 1, 1], [4, 1, 2], [4, 1, 3]]
  D2 := [[4, 1, 4], [4, 1, 0], [4, 1, 1], [4, 1, 2], [4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_85_85_110 : ColCertDiv where
  rK := ⟨85, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T85_85
  T2 := Q2.T85_85_2
  h1 := (4,0,2,1,0)
  h2 := (4,0,2,1,0)
  D1 := [[4, 2, 4], [4, 2, 0], [4, 2, 1], [4, 2, 2], [4, 2, 3]]
  D2 := [[4, 2, 4], [4, 2, 0], [4, 2, 1], [4, 2, 2], [4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_85_85_115 : ColCertDiv where
  rK := ⟨85, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T85_85
  T2 := Q2.T85_85_2
  h1 := (4,0,3,1,0)
  h2 := (4,0,3,1,0)
  D1 := [[4, 3, 4], [4, 3, 0], [4, 3, 1], [4, 3, 2], [4, 3, 3]]
  D2 := [[4, 3, 4], [4, 3, 0], [4, 3, 1], [4, 3, 2], [4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_85_85_120 : ColCertDiv where
  rK := ⟨85, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T85_85
  T2 := Q2.T85_85_2
  h1 := (4,0,4,1,0)
  h2 := (4,0,4,1,0)
  D1 := [[4, 4, 4], [4, 4, 0], [4, 4, 1], [4, 4, 2], [4, 4, 3]]
  D2 := [[4, 4, 4], [4, 4, 0], [4, 4, 1], [4, 4, 2], [4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_86_86_0 : ColCertDiv where
  rK := ⟨86, by decide⟩
  rH := ⟨86, by decide⟩
  m := 5
  T1 := T86_86
  T2 := Q2.T86_86_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D1 := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  D2 := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_86_86_1 : ColCertDiv where
  rK := ⟨86, by decide⟩
  rH := ⟨86, by decide⟩
  m := 5
  T1 := T86_86
  T2 := Q2.T86_86_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D1 := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]
  D2 := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_86_86_2 : ColCertDiv where
  rK := ⟨86, by decide⟩
  rH := ⟨86, by decide⟩
  m := 5
  T1 := T86_86
  T2 := Q2.T86_86_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D1 := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0]]
  D2 := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_86_86_3 : ColCertDiv where
  rK := ⟨86, by decide⟩
  rH := ⟨86, by decide⟩
  m := 5
  T1 := T86_86
  T2 := Q2.T86_86_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D1 := [[0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0]]
  D2 := [[0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_86_86_4 : ColCertDiv where
  rK := ⟨86, by decide⟩
  rH := ⟨86, by decide⟩
  m := 5
  T1 := T86_86
  T2 := Q2.T86_86_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D1 := [[0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0]]
  D2 := [[0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
