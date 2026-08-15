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
rest tier, chunk 134: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_147_141_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 0, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 0, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 0, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 0, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_11 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 0, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_12 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 0, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_13 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 0, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_14 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 0, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_16 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 0, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_17 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 0, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_18 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 0, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_19 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 0, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_21 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 0, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_22 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (0,0,4,2,0)
  h2 := (0,0,4,2,0)
  D := [[0, 0, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 0, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 0, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_25 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (1,0,0,0,0)
  h2 := (1,0,0,0,0)
  D := [[1, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_30 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (1,0,1,0,0)
  h2 := (1,0,1,0,0)
  D := [[1, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_35 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (1,0,2,0,0)
  h2 := (1,0,2,0,0)
  D := [[1, 0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_40 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (1,0,3,0,0)
  h2 := (1,0,3,0,0)
  D := [[1, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_45 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (1,0,4,0,0)
  h2 := (1,0,4,0,0)
  D := [[1, 0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_50 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (2,0,0,0,0)
  h2 := (2,0,0,0,0)
  D := [[2, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_55 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (2,0,1,0,0)
  h2 := (2,0,1,0,0)
  D := [[2, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_60 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (2,0,2,0,0)
  h2 := (2,0,2,0,0)
  D := [[2, 0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_65 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (2,0,3,0,0)
  h2 := (2,0,3,0,0)
  D := [[2, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_70 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (2,0,4,0,0)
  h2 := (2,0,4,0,0)
  D := [[2, 0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_75 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (3,0,0,0,0)
  h2 := (3,0,0,0,0)
  D := [[3, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_80 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (3,0,1,0,0)
  h2 := (3,0,1,0,0)
  D := [[3, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_85 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (3,0,2,0,0)
  h2 := (3,0,2,0,0)
  D := [[3, 0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_90 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (3,0,3,0,0)
  h2 := (3,0,3,0,0)
  D := [[3, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_95 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (3,0,4,0,0)
  h2 := (3,0,4,0,0)
  D := [[3, 0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_100 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (4,0,0,0,0)
  h2 := (4,0,0,0,0)
  D := [[4, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_105 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (4,0,1,0,0)
  h2 := (4,0,1,0,0)
  D := [[4, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_110 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (4,0,2,0,0)
  h2 := (4,0,2,0,0)
  D := [[4, 0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_115 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (4,0,3,0,0)
  h2 := (4,0,3,0,0)
  D := [[4, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_120 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (4,0,4,0,0)
  h2 := (4,0,4,0,0)
  D := [[4, 0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_142_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨142, by decide⟩
  m := 1
  T1 := T147_142
  T2 := Q2.T147_142_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_142_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨142, by decide⟩
  m := 1
  T1 := T147_142
  T2 := Q2.T147_142_2
  h1 := (1,0,0,0,0)
  h2 := (1,0,0,0,0)
  D := [[1, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_142_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨142, by decide⟩
  m := 1
  T1 := T147_142
  T2 := Q2.T147_142_2
  h1 := (2,0,0,0,0)
  h2 := (2,0,0,0,0)
  D := [[2, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_142_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨142, by decide⟩
  m := 1
  T1 := T147_142
  T2 := Q2.T147_142_2
  h1 := (3,0,0,0,0)
  h2 := (3,0,0,0,0)
  D := [[3, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_142_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨142, by decide⟩
  m := 1
  T1 := T147_142
  T2 := Q2.T147_142_2
  h1 := (4,0,0,0,0)
  h2 := (4,0,0,0,0)
  D := [[4, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_143_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨143, by decide⟩
  m := 1
  T1 := T147_143
  T2 := Q2.T147_143_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_143_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨143, by decide⟩
  m := 1
  T1 := T147_143
  T2 := Q2.T147_143_2
  h1 := (1,0,0,0,0)
  h2 := (1,0,0,0,0)
  D := [[1, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_143_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨143, by decide⟩
  m := 1
  T1 := T147_143
  T2 := Q2.T147_143_2
  h1 := (2,0,0,0,0)
  h2 := (2,0,0,0,0)
  D := [[2, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_143_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨143, by decide⟩
  m := 1
  T1 := T147_143
  T2 := Q2.T147_143_2
  h1 := (3,0,0,0,0)
  h2 := (3,0,0,0,0)
  D := [[3, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_143_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨143, by decide⟩
  m := 1
  T1 := T147_143
  T2 := Q2.T147_143_2
  h1 := (4,0,0,0,0)
  h2 := (4,0,0,0,0)
  D := [[4, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_144_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨144, by decide⟩
  m := 1
  T1 := T147_144
  T2 := Q2.T147_144_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_144_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨144, by decide⟩
  m := 1
  T1 := T147_144
  T2 := Q2.T147_144_2
  h1 := (1,0,0,0,0)
  h2 := (1,0,0,0,0)
  D := [[1, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_144_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨144, by decide⟩
  m := 1
  T1 := T147_144
  T2 := Q2.T147_144_2
  h1 := (2,0,0,0,0)
  h2 := (2,0,0,0,0)
  D := [[2, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_144_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨144, by decide⟩
  m := 1
  T1 := T147_144
  T2 := Q2.T147_144_2
  h1 := (3,0,0,0,0)
  h2 := (3,0,0,0,0)
  D := [[3, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_144_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨144, by decide⟩
  m := 1
  T1 := T147_144
  T2 := Q2.T147_144_2
  h1 := (4,0,0,0,0)
  h2 := (4,0,0,0,0)
  D := [[4, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_145_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨145, by decide⟩
  m := 1
  T1 := T147_145
  T2 := Q2.T147_145_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_145_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨145, by decide⟩
  m := 1
  T1 := T147_145
  T2 := Q2.T147_145_2
  h1 := (0,1,1,0,0)
  h2 := (0,1,1,0,0)
  D := [[0, 1, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_145_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨145, by decide⟩
  m := 1
  T1 := T147_145
  T2 := Q2.T147_145_2
  h1 := (0,2,2,0,1)
  h2 := (0,2,2,0,1)
  D := [[0, 2, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
