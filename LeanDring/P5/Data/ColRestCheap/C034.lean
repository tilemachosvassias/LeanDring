/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C027

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 33: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_118_80_25 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T118_80
  T2 := Q2.T118_80_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 1, 0, 2], [0, 1, 0, 3], [0, 1, 0, 4], [0, 1, 0, 0], [0, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_80_30 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T118_80
  T2 := Q2.T118_80_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 1, 1, 2], [0, 1, 1, 3], [0, 1, 1, 4], [0, 1, 1, 0], [0, 1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_80_35 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T118_80
  T2 := Q2.T118_80_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 1, 2, 2], [0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 2, 0], [0, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_80_40 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T118_80
  T2 := Q2.T118_80_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 1, 3, 2], [0, 1, 3, 3], [0, 1, 3, 4], [0, 1, 3, 0], [0, 1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_80_45 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T118_80
  T2 := Q2.T118_80_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 1, 4, 2], [0, 1, 4, 3], [0, 1, 4, 4], [0, 1, 4, 0], [0, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_80_50 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T118_80
  T2 := Q2.T118_80_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 2, 0, 4], [0, 2, 0, 1], [0, 2, 0, 3], [0, 2, 0, 0], [0, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_80_55 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T118_80
  T2 := Q2.T118_80_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 2, 1, 4], [0, 2, 1, 1], [0, 2, 1, 3], [0, 2, 1, 0], [0, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_80_60 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T118_80
  T2 := Q2.T118_80_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 2, 2, 4], [0, 2, 2, 1], [0, 2, 2, 3], [0, 2, 2, 0], [0, 2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_80_65 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T118_80
  T2 := Q2.T118_80_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 2, 3, 4], [0, 2, 3, 1], [0, 2, 3, 3], [0, 2, 3, 0], [0, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_80_70 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T118_80
  T2 := Q2.T118_80_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 2, 4, 4], [0, 2, 4, 1], [0, 2, 4, 3], [0, 2, 4, 0], [0, 2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_80_75 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T118_80
  T2 := Q2.T118_80_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 3, 0, 1], [0, 3, 0, 4], [0, 3, 0, 2], [0, 3, 0, 0], [0, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_80_80 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T118_80
  T2 := Q2.T118_80_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 3, 1, 1], [0, 3, 1, 4], [0, 3, 1, 2], [0, 3, 1, 0], [0, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_80_85 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T118_80
  T2 := Q2.T118_80_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 3, 2, 1], [0, 3, 2, 4], [0, 3, 2, 2], [0, 3, 2, 0], [0, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_80_90 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T118_80
  T2 := Q2.T118_80_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 3, 3, 1], [0, 3, 3, 4], [0, 3, 3, 2], [0, 3, 3, 0], [0, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_80_95 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T118_80
  T2 := Q2.T118_80_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 3, 4, 1], [0, 3, 4, 4], [0, 3, 4, 2], [0, 3, 4, 0], [0, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_80_100 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T118_80
  T2 := Q2.T118_80_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 4, 0, 3], [0, 4, 0, 2], [0, 4, 0, 1], [0, 4, 0, 0], [0, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_80_105 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T118_80
  T2 := Q2.T118_80_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 4, 1, 3], [0, 4, 1, 2], [0, 4, 1, 1], [0, 4, 1, 0], [0, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_80_110 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T118_80
  T2 := Q2.T118_80_2
  h1 := (0,0,4,2,0)
  h2 := (0,0,4,2,0)
  D := [[0, 4, 2, 3], [0, 4, 2, 2], [0, 4, 2, 1], [0, 4, 2, 0], [0, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_80_115 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T118_80
  T2 := Q2.T118_80_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 4, 3, 3], [0, 4, 3, 2], [0, 4, 3, 1], [0, 4, 3, 0], [0, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_80_120 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T118_80
  T2 := Q2.T118_80_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 4, 4, 3], [0, 4, 4, 2], [0, 4, 4, 1], [0, 4, 4, 0], [0, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_92_0 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T118_92
  T2 := Q2.T118_92_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_92_1 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T118_92
  T2 := Q2.T118_92_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_92_2 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T118_92
  T2 := Q2.T118_92_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_92_3 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T118_92
  T2 := Q2.T118_92_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_92_4 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T118_92
  T2 := Q2.T118_92_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_92_5 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T118_92
  T2 := Q2.T118_92_2
  h1 := (1,2,3,3,2)
  h2 := (1,2,3,3,2)
  D := [[1, 3, 3, 1], [1, 3, 2, 0], [1, 3, 1, 4], [1, 3, 0, 3], [1, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_92_10 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T118_92
  T2 := Q2.T118_92_2
  h1 := (2,4,1,3,3)
  h2 := (2,4,1,3,3)
  D := [[2, 1, 1, 3], [2, 1, 4, 2], [2, 1, 2, 1], [2, 1, 0, 0], [2, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_92_15 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T118_92
  T2 := Q2.T118_92_2
  h1 := (3,1,4,0,1)
  h2 := (3,1,4,0,2)
  D := [[3, 4, 4, 1], [3, 4, 1, 1], [3, 4, 3, 1], [3, 4, 0, 1], [3, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_92_20 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T118_92
  T2 := Q2.T118_92_2
  h1 := (4,3,2,4,1)
  h2 := (4,3,2,4,2)
  D := [[4, 2, 2, 0], [4, 2, 3, 2], [4, 2, 4, 4], [4, 2, 0, 1], [4, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_97_0 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T118_97
  T2 := Q2.T118_97_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_97_1 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T118_97
  T2 := Q2.T118_97_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_97_2 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T118_97
  T2 := Q2.T118_97_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_97_3 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T118_97
  T2 := Q2.T118_97_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_97_4 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T118_97
  T2 := Q2.T118_97_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_97_5 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T118_97
  T2 := Q2.T118_97_2
  h1 := (1,2,4,3,0)
  h2 := (1,2,4,3,0)
  D := [[1, 4, 3, 4], [1, 4, 2, 4], [1, 4, 1, 4], [1, 4, 0, 4], [1, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_97_10 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T118_97
  T2 := Q2.T118_97_2
  h1 := (2,4,3,3,1)
  h2 := (2,4,3,3,1)
  D := [[2, 3, 1, 2], [2, 3, 4, 3], [2, 3, 2, 4], [2, 3, 0, 0], [2, 3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_97_15 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T118_97
  T2 := Q2.T118_97_2
  h1 := (3,1,2,0,1)
  h2 := (3,1,2,0,2)
  D := [[3, 2, 4, 4], [3, 2, 1, 2], [3, 2, 3, 0], [3, 2, 0, 3], [3, 2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_97_20 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T118_97
  T2 := Q2.T118_97_2
  h1 := (4,3,1,4,0)
  h2 := (4,3,1,4,1)
  D := [[4, 1, 2, 0], [4, 1, 3, 1], [4, 1, 4, 2], [4, 1, 0, 3], [4, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_102_0 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T118_102
  T2 := Q2.T118_102_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_102_1 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T118_102
  T2 := Q2.T118_102_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_102_2 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T118_102
  T2 := Q2.T118_102_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_102_3 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T118_102
  T2 := Q2.T118_102_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_102_4 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T118_102
  T2 := Q2.T118_102_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_102_5 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T118_102
  T2 := Q2.T118_102_2
  h1 := (1,2,1,3,1)
  h2 := (1,2,1,3,1)
  D := [[1, 1, 3, 0], [1, 1, 2, 2], [1, 1, 1, 4], [1, 1, 0, 1], [1, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_102_10 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T118_102
  T2 := Q2.T118_102_2
  h1 := (2,4,2,3,2)
  h2 := (2,4,2,3,2)
  D := [[2, 2, 1, 0], [2, 2, 4, 0], [2, 2, 2, 0], [2, 2, 0, 0], [2, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_102_15 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T118_102
  T2 := Q2.T118_102_2
  h1 := (3,1,3,0,1)
  h2 := (3,1,3,0,2)
  D := [[3, 3, 4, 0], [3, 3, 1, 4], [3, 3, 3, 3], [3, 3, 0, 2], [3, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_102_20 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T118_102
  T2 := Q2.T118_102_2
  h1 := (4,3,4,4,3)
  h2 := (4,3,4,4,4)
  D := [[4, 4, 2, 0], [4, 4, 3, 4], [4, 4, 4, 3], [4, 4, 0, 2], [4, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_107_0 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T118_107
  T2 := Q2.T118_107_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_107_1 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T118_107
  T2 := Q2.T118_107_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_107_2 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T118_107
  T2 := Q2.T118_107_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_107_3 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T118_107
  T2 := Q2.T118_107_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_107_4 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T118_107
  T2 := Q2.T118_107_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_107_5 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T118_107
  T2 := Q2.T118_107_2
  h1 := (1,2,2,3,4)
  h2 := (1,2,2,3,4)
  D := [[1, 2, 3, 3], [1, 2, 2, 1], [1, 2, 1, 4], [1, 2, 0, 2], [1, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_107_10 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T118_107
  T2 := Q2.T118_107_2
  h1 := (2,4,4,3,0)
  h2 := (2,4,4,3,0)
  D := [[2, 4, 1, 4], [2, 4, 4, 1], [2, 4, 2, 3], [2, 4, 0, 0], [2, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_107_15 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T118_107
  T2 := Q2.T118_107_2
  h1 := (3,1,1,0,1)
  h2 := (3,1,1,0,2)
  D := [[3, 1, 4, 3], [3, 1, 1, 0], [3, 1, 3, 2], [3, 1, 0, 4], [3, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_107_20 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T118_107
  T2 := Q2.T118_107_2
  h1 := (4,3,3,4,2)
  h2 := (4,3,3,4,3)
  D := [[4, 3, 2, 0], [4, 3, 3, 3], [4, 3, 4, 1], [4, 3, 0, 4], [4, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_112_0 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T118_112
  T2 := Q2.T118_112_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_112_1 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T118_112
  T2 := Q2.T118_112_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_112_2 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T118_112
  T2 := Q2.T118_112_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_112_3 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T118_112
  T2 := Q2.T118_112_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
