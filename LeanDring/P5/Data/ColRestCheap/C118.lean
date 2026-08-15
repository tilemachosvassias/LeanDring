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
rest tier, chunk 117: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_147_67_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (0,0,1,3,2)
  h2 := (0,0,1,3,2)
  D := [[0, 0, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_67_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (0,0,1,3,3)
  h2 := (0,0,1,3,3)
  D := [[0, 0, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_67_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (0,0,1,3,4)
  h2 := (0,0,1,3,4)
  D := [[0, 0, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_67_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 0, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_67_11 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (0,0,2,1,1)
  h2 := (0,0,2,1,1)
  D := [[0, 0, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_67_12 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (0,0,2,1,2)
  h2 := (0,0,2,1,2)
  D := [[0, 0, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_67_13 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (0,0,2,1,3)
  h2 := (0,0,2,1,3)
  D := [[0, 0, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_67_14 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (0,0,2,1,4)
  h2 := (0,0,2,1,4)
  D := [[0, 0, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_67_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 0, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_67_16 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (0,0,3,4,1)
  h2 := (0,0,3,4,1)
  D := [[0, 0, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_67_17 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (0,0,3,4,2)
  h2 := (0,0,3,4,2)
  D := [[0, 0, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_67_18 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (0,0,3,4,3)
  h2 := (0,0,3,4,3)
  D := [[0, 0, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_67_19 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (0,0,3,4,4)
  h2 := (0,0,3,4,4)
  D := [[0, 0, 3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_67_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (0,0,4,2,0)
  h2 := (0,0,4,2,0)
  D := [[0, 0, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_67_21 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (0,0,4,2,1)
  h2 := (0,0,4,2,1)
  D := [[0, 0, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_67_22 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (0,0,4,2,2)
  h2 := (0,0,4,2,2)
  D := [[0, 0, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_67_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (0,0,4,2,3)
  h2 := (0,0,4,2,3)
  D := [[0, 0, 4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_67_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (0,0,4,2,4)
  h2 := (0,0,4,2,4)
  D := [[0, 0, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_67_25 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (1,2,0,2,4)
  h2 := (1,2,0,2,4)
  D := [[1, 2, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_67_30 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (1,2,1,0,4)
  h2 := (1,2,1,0,4)
  D := [[1, 2, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_67_35 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (1,2,2,3,4)
  h2 := (1,2,2,3,4)
  D := [[1, 2, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_67_40 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (1,2,3,1,4)
  h2 := (1,2,3,1,4)
  D := [[1, 2, 3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_67_45 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (1,2,4,4,4)
  h2 := (1,2,4,4,4)
  D := [[1, 2, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_67_50 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (2,4,0,1,0)
  h2 := (2,4,0,1,0)
  D := [[2, 4, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_67_55 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (2,4,1,4,0)
  h2 := (2,4,1,4,0)
  D := [[2, 4, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_67_60 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (2,4,2,2,0)
  h2 := (2,4,2,2,0)
  D := [[2, 4, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_67_65 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (2,4,3,0,0)
  h2 := (2,4,3,0,0)
  D := [[2, 4, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_67_70 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (2,4,4,3,0)
  h2 := (2,4,4,3,0)
  D := [[2, 4, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_68_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨68, by decide⟩
  m := 1
  T1 := T147_68
  T2 := Q2.T147_68_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_68_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨68, by decide⟩
  m := 1
  T1 := T147_68
  T2 := Q2.T147_68_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 0, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_68_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨68, by decide⟩
  m := 1
  T1 := T147_68
  T2 := Q2.T147_68_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 0, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_68_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨68, by decide⟩
  m := 1
  T1 := T147_68
  T2 := Q2.T147_68_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 0, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_68_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨68, by decide⟩
  m := 1
  T1 := T147_68
  T2 := Q2.T147_68_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 0, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_69_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨69, by decide⟩
  m := 1
  T1 := T147_69
  T2 := Q2.T147_69_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_69_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨69, by decide⟩
  m := 1
  T1 := T147_69
  T2 := Q2.T147_69_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 0, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_69_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨69, by decide⟩
  m := 1
  T1 := T147_69
  T2 := Q2.T147_69_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 0, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_69_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨69, by decide⟩
  m := 1
  T1 := T147_69
  T2 := Q2.T147_69_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 0, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_69_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨69, by decide⟩
  m := 1
  T1 := T147_69
  T2 := Q2.T147_69_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 0, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_69_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨69, by decide⟩
  m := 1
  T1 := T147_69
  T2 := Q2.T147_69_2
  h1 := (1,2,0,2,0)
  h2 := (1,2,0,2,0)
  D := [[1, 2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_69_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨69, by decide⟩
  m := 1
  T1 := T147_69
  T2 := Q2.T147_69_2
  h1 := (1,2,1,3,0)
  h2 := (1,2,1,3,0)
  D := [[1, 2, 1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_69_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨69, by decide⟩
  m := 1
  T1 := T147_69
  T2 := Q2.T147_69_2
  h1 := (1,2,2,4,0)
  h2 := (1,2,2,4,0)
  D := [[1, 2, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_69_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨69, by decide⟩
  m := 1
  T1 := T147_69
  T2 := Q2.T147_69_2
  h1 := (1,2,3,0,0)
  h2 := (1,2,3,0,0)
  D := [[1, 2, 3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_69_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨69, by decide⟩
  m := 1
  T1 := T147_69
  T2 := Q2.T147_69_2
  h1 := (1,2,4,1,0)
  h2 := (1,2,4,1,0)
  D := [[1, 2, 4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_69_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨69, by decide⟩
  m := 1
  T1 := T147_69
  T2 := Q2.T147_69_2
  h1 := (2,4,0,1,2)
  h2 := (2,4,0,1,2)
  D := [[2, 4, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_69_11 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨69, by decide⟩
  m := 1
  T1 := T147_69
  T2 := Q2.T147_69_2
  h1 := (2,4,1,2,2)
  h2 := (2,4,1,2,2)
  D := [[2, 4, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_69_12 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨69, by decide⟩
  m := 1
  T1 := T147_69
  T2 := Q2.T147_69_2
  h1 := (2,4,2,3,2)
  h2 := (2,4,2,3,2)
  D := [[2, 4, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_69_13 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨69, by decide⟩
  m := 1
  T1 := T147_69
  T2 := Q2.T147_69_2
  h1 := (2,4,3,4,2)
  h2 := (2,4,3,4,2)
  D := [[2, 4, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_69_14 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨69, by decide⟩
  m := 1
  T1 := T147_69
  T2 := Q2.T147_69_2
  h1 := (2,4,4,0,2)
  h2 := (2,4,4,0,2)
  D := [[2, 4, 4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_70_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨70, by decide⟩
  m := 1
  T1 := T147_70
  T2 := Q2.T147_70_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_70_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨70, by decide⟩
  m := 1
  T1 := T147_70
  T2 := Q2.T147_70_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_70_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨70, by decide⟩
  m := 1
  T1 := T147_70
  T2 := Q2.T147_70_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_70_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨70, by decide⟩
  m := 1
  T1 := T147_70
  T2 := Q2.T147_70_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_70_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨70, by decide⟩
  m := 1
  T1 := T147_70
  T2 := Q2.T147_70_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_71_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨71, by decide⟩
  m := 1
  T1 := T147_71
  T2 := Q2.T147_71_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_71_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨71, by decide⟩
  m := 1
  T1 := T147_71
  T2 := Q2.T147_71_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 0, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_71_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨71, by decide⟩
  m := 1
  T1 := T147_71
  T2 := Q2.T147_71_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 0, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_71_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨71, by decide⟩
  m := 1
  T1 := T147_71
  T2 := Q2.T147_71_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 0, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_71_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨71, by decide⟩
  m := 1
  T1 := T147_71
  T2 := Q2.T147_71_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 0, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_72_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨72, by decide⟩
  m := 1
  T1 := T147_72
  T2 := Q2.T147_72_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_72_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨72, by decide⟩
  m := 1
  T1 := T147_72
  T2 := Q2.T147_72_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 0, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
