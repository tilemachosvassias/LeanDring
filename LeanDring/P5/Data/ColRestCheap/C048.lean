/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C029

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 47: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_121_94_1 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T121_94
  T2 := Q2.T121_94_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_94_2 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T121_94
  T2 := Q2.T121_94_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_94_3 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T121_94
  T2 := Q2.T121_94_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_94_4 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T121_94
  T2 := Q2.T121_94_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_94_5 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T121_94
  T2 := Q2.T121_94_2
  h1 := (1,1,4,0,0)
  h2 := (1,1,4,0,0)
  D := [[1, 1, 4, 2], [1, 1, 4, 1], [1, 1, 4, 0], [1, 1, 4, 4], [1, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_94_10 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T121_94
  T2 := Q2.T121_94_2
  h1 := (2,2,3,1,4)
  h2 := (2,2,3,1,4)
  D := [[2, 2, 2, 0], [2, 2, 2, 3], [2, 2, 2, 1], [2, 2, 2, 4], [2, 2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_94_15 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T121_94
  T2 := Q2.T121_94_2
  h1 := (3,3,2,3,3)
  h2 := (3,3,2,3,3)
  D := [[3, 3, 4, 0], [3, 3, 4, 2], [3, 3, 4, 4], [3, 3, 4, 1], [3, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_94_20 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T121_94
  T2 := Q2.T121_94_2
  h1 := (4,4,1,1,3)
  h2 := (4,4,1,1,3)
  D := [[4, 4, 0, 3], [4, 4, 0, 4], [4, 4, 0, 0], [4, 4, 0, 1], [4, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_97_0 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T121_97
  T2 := Q2.T121_97_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_97_1 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T121_97
  T2 := Q2.T121_97_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_97_2 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T121_97
  T2 := Q2.T121_97_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_97_3 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T121_97
  T2 := Q2.T121_97_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_97_4 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T121_97
  T2 := Q2.T121_97_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_97_5 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T121_97
  T2 := Q2.T121_97_2
  h1 := (1,2,4,3,0)
  h2 := (1,2,4,3,0)
  D := [[1, 2, 1, 1], [1, 2, 1, 4], [1, 2, 1, 2], [1, 2, 1, 0], [1, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_97_10 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T121_97
  T2 := Q2.T121_97_2
  h1 := (2,4,3,3,1)
  h2 := (2,4,3,3,1)
  D := [[2, 4, 0, 1], [2, 4, 0, 2], [2, 4, 0, 3], [2, 4, 0, 4], [2, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_103_0 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T121_103
  T2 := Q2.T121_103_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_103_1 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T121_103
  T2 := Q2.T121_103_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_103_2 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T121_103
  T2 := Q2.T121_103_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_103_3 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T121_103
  T2 := Q2.T121_103_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_103_4 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T121_103
  T2 := Q2.T121_103_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_103_5 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T121_103
  T2 := Q2.T121_103_2
  h1 := (1,3,4,1,1)
  h2 := (1,3,4,1,1)
  D := [[1, 3, 3, 1], [1, 3, 3, 3], [1, 3, 3, 0], [1, 3, 3, 2], [1, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_106_0 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T121_106
  T2 := Q2.T121_106_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_106_1 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T121_106
  T2 := Q2.T121_106_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_106_2 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T121_106
  T2 := Q2.T121_106_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_106_3 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T121_106
  T2 := Q2.T121_106_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_106_4 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T121_106
  T2 := Q2.T121_106_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_106_5 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T121_106
  T2 := Q2.T121_106_2
  h1 := (1,4,4,4,1)
  h2 := (1,4,4,4,1)
  D := [[1, 4, 0, 0], [1, 4, 0, 1], [1, 4, 0, 2], [1, 4, 0, 3], [1, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_110_0 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T121_110
  T2 := Q2.T121_110_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_110_1 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T121_110
  T2 := Q2.T121_110_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_110_2 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T121_110
  T2 := Q2.T121_110_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_110_3 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T121_110
  T2 := Q2.T121_110_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_110_4 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T121_110
  T2 := Q2.T121_110_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_110_5 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T121_110
  T2 := Q2.T121_110_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_110_10 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T121_110
  T2 := Q2.T121_110_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_110_15 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T121_110
  T2 := Q2.T121_110_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_110_20 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T121_110
  T2 := Q2.T121_110_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_110_25 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T121_110
  T2 := Q2.T121_110_2
  h1 := (0,1,0,0,0)
  h2 := (0,1,0,0,0)
  D := [[0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_110_50 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T121_110
  T2 := Q2.T121_110_2
  h1 := (0,2,0,0,0)
  h2 := (0,2,0,0,0)
  D := [[0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_110_75 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T121_110
  T2 := Q2.T121_110_2
  h1 := (0,3,0,0,0)
  h2 := (0,3,0,0,0)
  D := [[0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_110_100 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T121_110
  T2 := Q2.T121_110_2
  h1 := (0,4,0,0,0)
  h2 := (0,4,0,0,0)
  D := [[0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_121_0 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨121, by decide⟩
  m := 5
  T1 := T121_121
  T2 := Q2.T121_121_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_121_1 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨121, by decide⟩
  m := 5
  T1 := T121_121
  T2 := Q2.T121_121_2
  h1 := (0,1,0,0,0)
  h2 := (0,1,0,0,0)
  D := [[0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_121_2 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨121, by decide⟩
  m := 5
  T1 := T121_121
  T2 := Q2.T121_121_2
  h1 := (0,2,0,0,0)
  h2 := (0,2,0,0,0)
  D := [[0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_121_3 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨121, by decide⟩
  m := 5
  T1 := T121_121
  T2 := Q2.T121_121_2
  h1 := (0,3,0,0,0)
  h2 := (0,3,0,0,0)
  D := [[0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_121_4 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨121, by decide⟩
  m := 5
  T1 := T121_121
  T2 := Q2.T121_121_2
  h1 := (0,4,0,0,0)
  h2 := (0,4,0,0,0)
  D := [[0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_121_5 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨121, by decide⟩
  m := 5
  T1 := T121_121
  T2 := Q2.T121_121_2
  h1 := (1,0,4,0,0)
  h2 := (1,0,4,0,0)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_121_6 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨121, by decide⟩
  m := 5
  T1 := T121_121
  T2 := Q2.T121_121_2
  h1 := (1,1,4,0,4)
  h2 := (1,1,4,0,4)
  D := [[1, 1, 4, 1], [1, 1, 4, 0], [1, 1, 4, 4], [1, 1, 4, 3], [1, 1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_121_7 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨121, by decide⟩
  m := 5
  T1 := T121_121
  T2 := Q2.T121_121_2
  h1 := (1,2,4,0,3)
  h2 := (1,2,4,0,3)
  D := [[1, 2, 3, 2], [1, 2, 3, 0], [1, 2, 3, 3], [1, 2, 3, 1], [1, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_121_8 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨121, by decide⟩
  m := 5
  T1 := T121_121
  T2 := Q2.T121_121_2
  h1 := (1,3,4,0,2)
  h2 := (1,3,4,0,2)
  D := [[1, 3, 2, 3], [1, 3, 2, 0], [1, 3, 2, 2], [1, 3, 2, 4], [1, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_121_9 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨121, by decide⟩
  m := 5
  T1 := T121_121
  T2 := Q2.T121_121_2
  h1 := (1,4,4,0,1)
  h2 := (1,4,4,0,1)
  D := [[1, 4, 1, 4], [1, 4, 1, 0], [1, 4, 1, 1], [1, 4, 1, 2], [1, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_121_10 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨121, by decide⟩
  m := 5
  T1 := T121_121
  T2 := Q2.T121_121_2
  h1 := (2,0,3,0,0)
  h2 := (2,0,3,0,0)
  D := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_121_11 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨121, by decide⟩
  m := 5
  T1 := T121_121
  T2 := Q2.T121_121_2
  h1 := (2,1,3,0,3)
  h2 := (2,1,3,0,3)
  D := [[2, 1, 3, 2], [2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_121_12 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨121, by decide⟩
  m := 5
  T1 := T121_121
  T2 := Q2.T121_121_2
  h1 := (2,2,3,0,1)
  h2 := (2,2,3,0,1)
  D := [[2, 2, 1, 4], [2, 2, 1, 2], [2, 2, 1, 0], [2, 2, 1, 3], [2, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_121_13 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨121, by decide⟩
  m := 5
  T1 := T121_121
  T2 := Q2.T121_121_2
  h1 := (2,3,3,0,4)
  h2 := (2,3,3,0,4)
  D := [[2, 3, 4, 1], [2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_121_14 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨121, by decide⟩
  m := 5
  T1 := T121_121
  T2 := Q2.T121_121_2
  h1 := (2,4,3,0,2)
  h2 := (2,4,3,0,2)
  D := [[2, 4, 2, 3], [2, 4, 2, 4], [2, 4, 2, 0], [2, 4, 2, 1], [2, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_121_15 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨121, by decide⟩
  m := 5
  T1 := T121_121
  T2 := Q2.T121_121_2
  h1 := (3,0,2,0,0)
  h2 := (3,0,2,0,0)
  D := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_121_16 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨121, by decide⟩
  m := 5
  T1 := T121_121
  T2 := Q2.T121_121_2
  h1 := (3,1,2,0,2)
  h2 := (3,1,2,0,2)
  D := [[3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2], [3, 1, 2, 1], [3, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_121_17 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨121, by decide⟩
  m := 5
  T1 := T121_121
  T2 := Q2.T121_121_2
  h1 := (3,2,2,0,4)
  h2 := (3,2,2,0,4)
  D := [[3, 2, 4, 3], [3, 2, 4, 1], [3, 2, 4, 4], [3, 2, 4, 2], [3, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_121_18 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨121, by decide⟩
  m := 5
  T1 := T121_121
  T2 := Q2.T121_121_2
  h1 := (3,3,2,0,1)
  h2 := (3,3,2,0,1)
  D := [[3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_121_19 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨121, by decide⟩
  m := 5
  T1 := T121_121
  T2 := Q2.T121_121_2
  h1 := (3,4,2,0,3)
  h2 := (3,4,2,0,3)
  D := [[3, 4, 3, 1], [3, 4, 3, 2], [3, 4, 3, 3], [3, 4, 3, 4], [3, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
