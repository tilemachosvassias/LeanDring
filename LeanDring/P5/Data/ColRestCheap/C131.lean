/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C044

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 130: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_147_121_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨121, by decide⟩
  m := 1
  T1 := T147_121
  T2 := Q2.T147_121_2
  h1 := (4,3,1,0,3)
  h2 := (4,3,1,0,3)
  D := [[4, 3, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_121_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨121, by decide⟩
  m := 1
  T1 := T147_121
  T2 := Q2.T147_121_2
  h1 := (4,4,1,0,4)
  h2 := (4,4,1,0,4)
  D := [[4, 4, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_122_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨122, by decide⟩
  m := 1
  T1 := T147_122
  T2 := Q2.T147_122_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_122_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨122, by decide⟩
  m := 1
  T1 := T147_122
  T2 := Q2.T147_122_2
  h1 := (1,4,0,4,0)
  h2 := (1,4,0,4,0)
  D := [[1, 4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_122_13 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨122, by decide⟩
  m := 1
  T1 := T147_122
  T2 := Q2.T147_122_2
  h1 := (2,3,0,3,0)
  h2 := (2,3,0,3,0)
  D := [[2, 3, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_122_17 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨122, by decide⟩
  m := 1
  T1 := T147_122
  T2 := Q2.T147_122_2
  h1 := (3,2,0,2,0)
  h2 := (3,2,0,2,0)
  D := [[3, 2, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_122_21 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨122, by decide⟩
  m := 1
  T1 := T147_122
  T2 := Q2.T147_122_2
  h1 := (4,1,0,1,0)
  h2 := (4,1,0,1,0)
  D := [[4, 1, 0, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_123_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨123, by decide⟩
  m := 1
  T1 := T147_123
  T2 := Q2.T147_123_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_123_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨123, by decide⟩
  m := 1
  T1 := T147_123
  T2 := Q2.T147_123_2
  h1 := (1,2,0,3,3)
  h2 := (1,2,0,3,3)
  D := [[1, 2, 0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_123_14 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨123, by decide⟩
  m := 1
  T1 := T147_123
  T2 := Q2.T147_123_2
  h1 := (2,4,0,1,2)
  h2 := (2,4,0,1,2)
  D := [[2, 4, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_123_16 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨123, by decide⟩
  m := 1
  T1 := T147_123
  T2 := Q2.T147_123_2
  h1 := (3,1,0,4,2)
  h2 := (3,1,0,4,2)
  D := [[3, 1, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_123_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨123, by decide⟩
  m := 1
  T1 := T147_123
  T2 := Q2.T147_123_2
  h1 := (4,3,0,2,3)
  h2 := (4,3,0,2,3)
  D := [[4, 3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_124_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨124, by decide⟩
  m := 1
  T1 := T147_124
  T2 := Q2.T147_124_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_124_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨124, by decide⟩
  m := 1
  T1 := T147_124
  T2 := Q2.T147_124_2
  h1 := (1,3,0,1,2)
  h2 := (1,3,0,1,2)
  D := [[1, 3, 0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_124_11 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨124, by decide⟩
  m := 1
  T1 := T147_124
  T2 := Q2.T147_124_2
  h1 := (2,1,0,2,2)
  h2 := (2,1,0,2,2)
  D := [[2, 1, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_124_19 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨124, by decide⟩
  m := 1
  T1 := T147_124
  T2 := Q2.T147_124_2
  h1 := (3,4,0,3,0)
  h2 := (3,4,0,3,0)
  D := [[3, 4, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_124_22 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨124, by decide⟩
  m := 1
  T1 := T147_124
  T2 := Q2.T147_124_2
  h1 := (4,2,0,4,1)
  h2 := (4,2,0,4,1)
  D := [[4, 2, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_125_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨125, by decide⟩
  m := 1
  T1 := T147_125
  T2 := Q2.T147_125_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_125_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨125, by decide⟩
  m := 1
  T1 := T147_125
  T2 := Q2.T147_125_2
  h1 := (0,1,1,0,0)
  h2 := (0,1,1,0,0)
  D := [[0, 1, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_125_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨125, by decide⟩
  m := 1
  T1 := T147_125
  T2 := Q2.T147_125_2
  h1 := (0,2,2,0,1)
  h2 := (0,2,2,0,1)
  D := [[0, 2, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_125_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨125, by decide⟩
  m := 1
  T1 := T147_125
  T2 := Q2.T147_125_2
  h1 := (0,3,3,0,3)
  h2 := (0,3,3,0,3)
  D := [[0, 3, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_125_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨125, by decide⟩
  m := 1
  T1 := T147_125
  T2 := Q2.T147_125_2
  h1 := (0,4,4,0,1)
  h2 := (0,4,4,0,1)
  D := [[0, 4, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_125_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨125, by decide⟩
  m := 1
  T1 := T147_125
  T2 := Q2.T147_125_2
  h1 := (1,0,4,0,1)
  h2 := (1,0,4,0,1)
  D := [[1, 0, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_125_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨125, by decide⟩
  m := 1
  T1 := T147_125
  T2 := Q2.T147_125_2
  h1 := (1,1,0,0,0)
  h2 := (1,1,0,0,0)
  D := [[1, 1, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_125_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨125, by decide⟩
  m := 1
  T1 := T147_125
  T2 := Q2.T147_125_2
  h1 := (1,2,1,0,0)
  h2 := (1,2,1,0,0)
  D := [[1, 2, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_125_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨125, by decide⟩
  m := 1
  T1 := T147_125
  T2 := Q2.T147_125_2
  h1 := (1,3,2,0,1)
  h2 := (1,3,2,0,1)
  D := [[1, 3, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_125_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨125, by decide⟩
  m := 1
  T1 := T147_125
  T2 := Q2.T147_125_2
  h1 := (1,4,3,0,3)
  h2 := (1,4,3,0,3)
  D := [[1, 4, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_125_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨125, by decide⟩
  m := 1
  T1 := T147_125
  T2 := Q2.T147_125_2
  h1 := (2,0,3,0,2)
  h2 := (2,0,3,0,2)
  D := [[2, 0, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_125_11 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨125, by decide⟩
  m := 1
  T1 := T147_125
  T2 := Q2.T147_125_2
  h1 := (2,1,4,0,0)
  h2 := (2,1,4,0,0)
  D := [[2, 1, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_125_12 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨125, by decide⟩
  m := 1
  T1 := T147_125
  T2 := Q2.T147_125_2
  h1 := (2,2,0,0,4)
  h2 := (2,2,0,0,4)
  D := [[2, 2, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_125_13 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨125, by decide⟩
  m := 1
  T1 := T147_125
  T2 := Q2.T147_125_2
  h1 := (2,3,1,0,4)
  h2 := (2,3,1,0,4)
  D := [[2, 3, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_125_14 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨125, by decide⟩
  m := 1
  T1 := T147_125
  T2 := Q2.T147_125_2
  h1 := (2,4,2,0,0)
  h2 := (2,4,2,0,0)
  D := [[2, 4, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_125_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨125, by decide⟩
  m := 1
  T1 := T147_125
  T2 := Q2.T147_125_2
  h1 := (3,0,2,0,3)
  h2 := (3,0,2,0,3)
  D := [[3, 0, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_125_16 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨125, by decide⟩
  m := 1
  T1 := T147_125
  T2 := Q2.T147_125_2
  h1 := (3,1,3,0,0)
  h2 := (3,1,3,0,0)
  D := [[3, 1, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_125_17 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨125, by decide⟩
  m := 1
  T1 := T147_125
  T2 := Q2.T147_125_2
  h1 := (3,2,4,0,3)
  h2 := (3,2,4,0,3)
  D := [[3, 2, 4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_125_18 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨125, by decide⟩
  m := 1
  T1 := T147_125
  T2 := Q2.T147_125_2
  h1 := (3,3,0,0,2)
  h2 := (3,3,0,0,2)
  D := [[3, 3, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_125_19 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨125, by decide⟩
  m := 1
  T1 := T147_125
  T2 := Q2.T147_125_2
  h1 := (3,4,1,0,2)
  h2 := (3,4,1,0,2)
  D := [[3, 4, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_125_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨125, by decide⟩
  m := 1
  T1 := T147_125
  T2 := Q2.T147_125_2
  h1 := (4,0,1,0,4)
  h2 := (4,0,1,0,4)
  D := [[4, 0, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_125_21 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨125, by decide⟩
  m := 1
  T1 := T147_125
  T2 := Q2.T147_125_2
  h1 := (4,1,2,0,0)
  h2 := (4,1,2,0,0)
  D := [[4, 1, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_125_22 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨125, by decide⟩
  m := 1
  T1 := T147_125
  T2 := Q2.T147_125_2
  h1 := (4,2,3,0,2)
  h2 := (4,2,3,0,2)
  D := [[4, 2, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_125_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨125, by decide⟩
  m := 1
  T1 := T147_125
  T2 := Q2.T147_125_2
  h1 := (4,3,4,0,0)
  h2 := (4,3,4,0,0)
  D := [[4, 3, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_125_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨125, by decide⟩
  m := 1
  T1 := T147_125
  T2 := Q2.T147_125_2
  h1 := (4,4,0,0,4)
  h2 := (4,4,0,0,4)
  D := [[4, 4, 0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_126_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨126, by decide⟩
  m := 1
  T1 := T147_126
  T2 := Q2.T147_126_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_126_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨126, by decide⟩
  m := 1
  T1 := T147_126
  T2 := Q2.T147_126_2
  h1 := (0,1,0,0,0)
  h2 := (0,1,0,0,0)
  D := [[0, 1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_126_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨126, by decide⟩
  m := 1
  T1 := T147_126
  T2 := Q2.T147_126_2
  h1 := (0,2,0,0,0)
  h2 := (0,2,0,0,0)
  D := [[0, 2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_126_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨126, by decide⟩
  m := 1
  T1 := T147_126
  T2 := Q2.T147_126_2
  h1 := (0,3,0,0,0)
  h2 := (0,3,0,0,0)
  D := [[0, 3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_126_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨126, by decide⟩
  m := 1
  T1 := T147_126
  T2 := Q2.T147_126_2
  h1 := (0,4,0,0,0)
  h2 := (0,4,0,0,0)
  D := [[0, 4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_126_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨126, by decide⟩
  m := 1
  T1 := T147_126
  T2 := Q2.T147_126_2
  h1 := (1,0,2,0,0)
  h2 := (1,0,2,0,0)
  D := [[1, 0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_126_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨126, by decide⟩
  m := 1
  T1 := T147_126
  T2 := Q2.T147_126_2
  h1 := (1,1,2,0,2)
  h2 := (1,1,2,0,2)
  D := [[1, 1, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_126_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨126, by decide⟩
  m := 1
  T1 := T147_126
  T2 := Q2.T147_126_2
  h1 := (1,2,2,0,4)
  h2 := (1,2,2,0,4)
  D := [[1, 2, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_126_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨126, by decide⟩
  m := 1
  T1 := T147_126
  T2 := Q2.T147_126_2
  h1 := (1,3,2,0,1)
  h2 := (1,3,2,0,1)
  D := [[1, 3, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_126_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨126, by decide⟩
  m := 1
  T1 := T147_126
  T2 := Q2.T147_126_2
  h1 := (1,4,2,0,3)
  h2 := (1,4,2,0,3)
  D := [[1, 4, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_126_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨126, by decide⟩
  m := 1
  T1 := T147_126
  T2 := Q2.T147_126_2
  h1 := (2,0,4,0,0)
  h2 := (2,0,4,0,0)
  D := [[2, 0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_126_11 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨126, by decide⟩
  m := 1
  T1 := T147_126
  T2 := Q2.T147_126_2
  h1 := (2,1,4,0,4)
  h2 := (2,1,4,0,4)
  D := [[2, 1, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_126_12 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨126, by decide⟩
  m := 1
  T1 := T147_126
  T2 := Q2.T147_126_2
  h1 := (2,2,4,0,3)
  h2 := (2,2,4,0,3)
  D := [[2, 2, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_126_13 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨126, by decide⟩
  m := 1
  T1 := T147_126
  T2 := Q2.T147_126_2
  h1 := (2,3,4,0,2)
  h2 := (2,3,4,0,2)
  D := [[2, 3, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_126_14 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨126, by decide⟩
  m := 1
  T1 := T147_126
  T2 := Q2.T147_126_2
  h1 := (2,4,4,0,1)
  h2 := (2,4,4,0,1)
  D := [[2, 4, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_126_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨126, by decide⟩
  m := 1
  T1 := T147_126
  T2 := Q2.T147_126_2
  h1 := (3,0,1,0,0)
  h2 := (3,0,1,0,0)
  D := [[3, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_126_16 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨126, by decide⟩
  m := 1
  T1 := T147_126
  T2 := Q2.T147_126_2
  h1 := (3,1,1,0,1)
  h2 := (3,1,1,0,1)
  D := [[3, 1, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_126_17 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨126, by decide⟩
  m := 1
  T1 := T147_126
  T2 := Q2.T147_126_2
  h1 := (3,2,1,0,2)
  h2 := (3,2,1,0,2)
  D := [[3, 2, 1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
