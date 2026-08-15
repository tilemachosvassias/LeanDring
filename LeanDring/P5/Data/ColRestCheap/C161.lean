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
rest tier, chunk 160: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_70_41_4 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T70_41
  T2 := Q2.T70_41_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_41_5 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T70_41
  T2 := Q2.T70_41_2
  h1 := (1,3,4,0,0)
  h2 := (1,3,4,0,1)
  D := [[1, 4, 3], [1, 4, 2], [1, 4, 1], [1, 4, 0], [1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_41_10 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T70_41
  T2 := Q2.T70_41_2
  h1 := (2,1,3,3,3)
  h2 := (2,1,3,3,1)
  D := [[2, 3, 4], [2, 3, 2], [2, 3, 0], [2, 3, 3], [2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_41_15 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T70_41
  T2 := Q2.T70_41_2
  h1 := (3,4,2,4,0)
  h2 := (3,4,2,4,4)
  D := [[3, 2, 3], [3, 2, 0], [3, 2, 2], [3, 2, 4], [3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_41_20 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T70_41
  T2 := Q2.T70_41_2
  h1 := (4,2,1,3,1)
  h2 := (4,2,1,3,2)
  D := [[4, 1, 0], [4, 1, 1], [4, 1, 2], [4, 1, 3], [4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_46_0 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T70_46
  T2 := Q2.T70_46_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_46_1 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T70_46
  T2 := Q2.T70_46_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_46_2 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T70_46
  T2 := Q2.T70_46_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_46_3 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T70_46
  T2 := Q2.T70_46_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_46_4 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T70_46
  T2 := Q2.T70_46_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_46_5 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T70_46
  T2 := Q2.T70_46_2
  h1 := (1,3,3,0,2)
  h2 := (1,3,3,0,3)
  D := [[1, 3, 3], [1, 3, 2], [1, 3, 1], [1, 3, 0], [1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_46_10 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T70_46
  T2 := Q2.T70_46_2
  h1 := (2,1,1,3,4)
  h2 := (2,1,1,3,2)
  D := [[2, 1, 2], [2, 1, 0], [2, 1, 3], [2, 1, 1], [2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_46_15 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T70_46
  T2 := Q2.T70_46_2
  h1 := (3,4,4,4,2)
  h2 := (3,4,4,4,1)
  D := [[3, 4, 2], [3, 4, 4], [3, 4, 1], [3, 4, 3], [3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_46_20 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T70_46
  T2 := Q2.T70_46_2
  h1 := (4,2,2,3,1)
  h2 := (4,2,2,3,2)
  D := [[4, 2, 3], [4, 2, 4], [4, 2, 0], [4, 2, 1], [4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_51_0 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T70_51
  T2 := Q2.T70_51_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_51_1 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T70_51
  T2 := Q2.T70_51_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_51_2 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T70_51
  T2 := Q2.T70_51_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_51_3 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T70_51
  T2 := Q2.T70_51_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_51_4 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T70_51
  T2 := Q2.T70_51_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_51_5 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T70_51
  T2 := Q2.T70_51_2
  h1 := (1,3,0,0,3)
  h2 := (1,3,0,0,4)
  D := [[1, 0, 3], [1, 0, 2], [1, 0, 1], [1, 0, 0], [1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_51_10 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T70_51
  T2 := Q2.T70_51_2
  h1 := (2,1,0,3,2)
  h2 := (2,1,0,3,0)
  D := [[2, 0, 1], [2, 0, 4], [2, 0, 2], [2, 0, 0], [2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_51_15 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T70_51
  T2 := Q2.T70_51_2
  h1 := (3,4,0,4,3)
  h2 := (3,4,0,4,2)
  D := [[3, 0, 4], [3, 0, 1], [3, 0, 3], [3, 0, 0], [3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_51_20 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T70_51
  T2 := Q2.T70_51_2
  h1 := (4,2,0,3,1)
  h2 := (4,2,0,3,2)
  D := [[4, 0, 2], [4, 0, 3], [4, 0, 4], [4, 0, 0], [4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_70_0 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T70_70
  T2 := Q2.T70_70_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_70_1 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T70_70
  T2 := Q2.T70_70_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_70_2 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T70_70
  T2 := Q2.T70_70_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_70_3 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T70_70
  T2 := Q2.T70_70_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_70_4 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T70_70
  T2 := Q2.T70_70_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_70_5 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T70_70
  T2 := Q2.T70_70_2
  h1 := (1,3,0,0,3)
  h2 := (1,3,0,0,4)
  D := [[1, 0, 3], [1, 0, 2], [1, 0, 1], [1, 0, 0], [1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_70_6 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T70_70
  T2 := Q2.T70_70_2
  h1 := (1,3,1,0,3)
  h2 := (1,3,1,0,4)
  D := [[1, 1, 0], [1, 1, 4], [1, 1, 3], [1, 1, 2], [1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_70_7 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T70_70
  T2 := Q2.T70_70_2
  h1 := (1,3,2,0,3)
  h2 := (1,3,2,0,4)
  D := [[1, 2, 2], [1, 2, 1], [1, 2, 0], [1, 2, 4], [1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_70_8 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T70_70
  T2 := Q2.T70_70_2
  h1 := (1,3,3,0,3)
  h2 := (1,3,3,0,4)
  D := [[1, 3, 4], [1, 3, 3], [1, 3, 2], [1, 3, 1], [1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_70_9 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T70_70
  T2 := Q2.T70_70_2
  h1 := (1,3,4,0,3)
  h2 := (1,3,4,0,4)
  D := [[1, 4, 1], [1, 4, 0], [1, 4, 4], [1, 4, 3], [1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_70_10 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T70_70
  T2 := Q2.T70_70_2
  h1 := (2,1,0,3,2)
  h2 := (2,1,0,3,0)
  D := [[2, 0, 1], [2, 0, 4], [2, 0, 2], [2, 0, 0], [2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_70_11 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T70_70
  T2 := Q2.T70_70_2
  h1 := (2,1,1,3,2)
  h2 := (2,1,1,3,0)
  D := [[2, 1, 0], [2, 1, 3], [2, 1, 1], [2, 1, 4], [2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_70_12 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T70_70
  T2 := Q2.T70_70_2
  h1 := (2,1,2,3,2)
  h2 := (2,1,2,3,0)
  D := [[2, 2, 4], [2, 2, 2], [2, 2, 0], [2, 2, 3], [2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_70_13 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T70_70
  T2 := Q2.T70_70_2
  h1 := (2,1,3,3,2)
  h2 := (2,1,3,3,0)
  D := [[2, 3, 3], [2, 3, 1], [2, 3, 4], [2, 3, 2], [2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_70_14 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T70_70
  T2 := Q2.T70_70_2
  h1 := (2,1,4,3,2)
  h2 := (2,1,4,3,0)
  D := [[2, 4, 2], [2, 4, 0], [2, 4, 3], [2, 4, 1], [2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_70_15 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T70_70
  T2 := Q2.T70_70_2
  h1 := (3,4,0,4,3)
  h2 := (3,4,0,4,2)
  D := [[3, 0, 4], [3, 0, 1], [3, 0, 3], [3, 0, 0], [3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_70_16 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T70_70
  T2 := Q2.T70_70_2
  h1 := (3,4,1,4,3)
  h2 := (3,4,1,4,2)
  D := [[3, 1, 0], [3, 1, 2], [3, 1, 4], [3, 1, 1], [3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_70_17 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T70_70
  T2 := Q2.T70_70_2
  h1 := (3,4,2,4,3)
  h2 := (3,4,2,4,2)
  D := [[3, 2, 1], [3, 2, 3], [3, 2, 0], [3, 2, 2], [3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_70_18 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T70_70
  T2 := Q2.T70_70_2
  h1 := (3,4,3,4,3)
  h2 := (3,4,3,4,2)
  D := [[3, 3, 2], [3, 3, 4], [3, 3, 1], [3, 3, 3], [3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_70_19 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T70_70
  T2 := Q2.T70_70_2
  h1 := (3,4,4,4,3)
  h2 := (3,4,4,4,2)
  D := [[3, 4, 3], [3, 4, 0], [3, 4, 2], [3, 4, 4], [3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_70_20 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T70_70
  T2 := Q2.T70_70_2
  h1 := (4,2,0,3,1)
  h2 := (4,2,0,3,2)
  D := [[4, 0, 2], [4, 0, 3], [4, 0, 4], [4, 0, 0], [4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_70_21 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T70_70
  T2 := Q2.T70_70_2
  h1 := (4,2,1,3,1)
  h2 := (4,2,1,3,2)
  D := [[4, 1, 0], [4, 1, 1], [4, 1, 2], [4, 1, 3], [4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_70_22 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T70_70
  T2 := Q2.T70_70_2
  h1 := (4,2,2,3,1)
  h2 := (4,2,2,3,2)
  D := [[4, 2, 3], [4, 2, 4], [4, 2, 0], [4, 2, 1], [4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_70_23 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T70_70
  T2 := Q2.T70_70_2
  h1 := (4,2,3,3,1)
  h2 := (4,2,3,3,2)
  D := [[4, 3, 1], [4, 3, 2], [4, 3, 3], [4, 3, 4], [4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_70_70_24 : ColCert where
  rK := ⟨70, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T70_70
  T2 := Q2.T70_70_2
  h1 := (4,2,4,3,1)
  h2 := (4,2,4,3,2)
  D := [[4, 4, 4], [4, 4, 0], [4, 4, 1], [4, 4, 2], [4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_0_0 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨0, by decide⟩
  m := 25
  T1 := T71_0
  T2 := Q2.T71_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_1_0 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨1, by decide⟩
  m := 25
  T1 := T71_1
  T2 := Q2.T71_1_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_1_1 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨1, by decide⟩
  m := 25
  T1 := T71_1
  T2 := Q2.T71_1_2
  h1 := (0,0,1,4,4)
  h2 := (0,0,1,4,4)
  D := [[0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_1_2 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨1, by decide⟩
  m := 25
  T1 := T71_1
  T2 := Q2.T71_1_2
  h1 := (0,0,2,3,3)
  h2 := (0,0,2,3,3)
  D := [[0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_1_3 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨1, by decide⟩
  m := 25
  T1 := T71_1
  T2 := Q2.T71_1_2
  h1 := (0,0,3,2,2)
  h2 := (0,0,3,2,2)
  D := [[0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_1_4 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨1, by decide⟩
  m := 25
  T1 := T71_1
  T2 := Q2.T71_1_2
  h1 := (0,0,4,1,1)
  h2 := (0,0,4,1,1)
  D := [[0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_12_0 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T71_12
  T2 := Q2.T71_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_12_1 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T71_12
  T2 := Q2.T71_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_12_2 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T71_12
  T2 := Q2.T71_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_12_3 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T71_12
  T2 := Q2.T71_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_12_4 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T71_12
  T2 := Q2.T71_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_19_0 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T71_19
  T2 := Q2.T71_19_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
