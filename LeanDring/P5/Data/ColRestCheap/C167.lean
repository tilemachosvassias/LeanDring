/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C017
import LeanDring.P5.Data.EntryK.C018

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 166: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_74_51_2 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T74_51
  T2 := Q2.T74_51_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_51_3 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T74_51
  T2 := Q2.T74_51_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_51_4 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T74_51
  T2 := Q2.T74_51_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_74_0 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨74, by decide⟩
  m := 5
  T1 := T74_74
  T2 := Q2.T74_74_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_74_1 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨74, by decide⟩
  m := 5
  T1 := T74_74
  T2 := Q2.T74_74_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_74_2 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨74, by decide⟩
  m := 5
  T1 := T74_74
  T2 := Q2.T74_74_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_74_3 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨74, by decide⟩
  m := 5
  T1 := T74_74
  T2 := Q2.T74_74_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_74_4 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨74, by decide⟩
  m := 5
  T1 := T74_74
  T2 := Q2.T74_74_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_74_5 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨74, by decide⟩
  m := 5
  T1 := T74_74
  T2 := Q2.T74_74_2
  h1 := (1,3,0,0,0)
  h2 := (1,3,0,0,0)
  D := [[1, 0, 2], [1, 0, 1], [1, 0, 0], [1, 0, 4], [1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_74_6 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨74, by decide⟩
  m := 5
  T1 := T74_74
  T2 := Q2.T74_74_2
  h1 := (1,3,1,1,0)
  h2 := (1,3,1,1,0)
  D := [[1, 1, 3], [1, 1, 2], [1, 1, 1], [1, 1, 0], [1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_74_7 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨74, by decide⟩
  m := 5
  T1 := T74_74
  T2 := Q2.T74_74_2
  h1 := (1,3,2,2,0)
  h2 := (1,3,2,2,0)
  D := [[1, 2, 4], [1, 2, 3], [1, 2, 2], [1, 2, 1], [1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_74_8 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨74, by decide⟩
  m := 5
  T1 := T74_74
  T2 := Q2.T74_74_2
  h1 := (1,3,3,3,0)
  h2 := (1,3,3,3,0)
  D := [[1, 3, 0], [1, 3, 4], [1, 3, 3], [1, 3, 2], [1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_74_9 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨74, by decide⟩
  m := 5
  T1 := T74_74
  T2 := Q2.T74_74_2
  h1 := (1,3,4,4,0)
  h2 := (1,3,4,4,0)
  D := [[1, 4, 1], [1, 4, 0], [1, 4, 4], [1, 4, 3], [1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_74_10 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨74, by decide⟩
  m := 5
  T1 := T74_74
  T2 := Q2.T74_74_2
  h1 := (2,1,0,3,1)
  h2 := (2,1,0,3,2)
  D := [[2, 0, 4], [2, 0, 2], [2, 0, 0], [2, 0, 3], [2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_74_11 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨74, by decide⟩
  m := 5
  T1 := T74_74
  T2 := Q2.T74_74_2
  h1 := (2,1,1,4,1)
  h2 := (2,1,1,4,2)
  D := [[2, 1, 1], [2, 1, 4], [2, 1, 2], [2, 1, 0], [2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_74_12 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨74, by decide⟩
  m := 5
  T1 := T74_74
  T2 := Q2.T74_74_2
  h1 := (2,1,2,0,1)
  h2 := (2,1,2,0,2)
  D := [[2, 2, 3], [2, 2, 1], [2, 2, 4], [2, 2, 2], [2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_74_13 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨74, by decide⟩
  m := 5
  T1 := T74_74
  T2 := Q2.T74_74_2
  h1 := (2,1,3,1,1)
  h2 := (2,1,3,1,2)
  D := [[2, 3, 0], [2, 3, 3], [2, 3, 1], [2, 3, 4], [2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_74_14 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨74, by decide⟩
  m := 5
  T1 := T74_74
  T2 := Q2.T74_74_2
  h1 := (2,1,4,2,1)
  h2 := (2,1,4,2,2)
  D := [[2, 4, 2], [2, 4, 0], [2, 4, 3], [2, 4, 1], [2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_74_15 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨74, by decide⟩
  m := 5
  T1 := T74_74
  T2 := Q2.T74_74_2
  h1 := (3,4,0,4,4)
  h2 := (3,4,0,4,0)
  D := [[3, 0, 1], [3, 0, 3], [3, 0, 0], [3, 0, 2], [3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_74_16 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨74, by decide⟩
  m := 5
  T1 := T74_74
  T2 := Q2.T74_74_2
  h1 := (3,4,1,0,4)
  h2 := (3,4,1,0,0)
  D := [[3, 1, 4], [3, 1, 1], [3, 1, 3], [3, 1, 0], [3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_74_17 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨74, by decide⟩
  m := 5
  T1 := T74_74
  T2 := Q2.T74_74_2
  h1 := (3,4,2,1,4)
  h2 := (3,4,2,1,0)
  D := [[3, 2, 2], [3, 2, 4], [3, 2, 1], [3, 2, 3], [3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_74_18 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨74, by decide⟩
  m := 5
  T1 := T74_74
  T2 := Q2.T74_74_2
  h1 := (3,4,3,2,4)
  h2 := (3,4,3,2,0)
  D := [[3, 3, 0], [3, 3, 2], [3, 3, 4], [3, 3, 1], [3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_74_19 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨74, by decide⟩
  m := 5
  T1 := T74_74
  T2 := Q2.T74_74_2
  h1 := (3,4,4,3,4)
  h2 := (3,4,4,3,0)
  D := [[3, 4, 3], [3, 4, 0], [3, 4, 2], [3, 4, 4], [3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_74_20 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨74, by decide⟩
  m := 5
  T1 := T74_74
  T2 := Q2.T74_74_2
  h1 := (4,2,0,3,4)
  h2 := (4,2,0,3,1)
  D := [[4, 0, 3], [4, 0, 4], [4, 0, 0], [4, 0, 1], [4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_74_21 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨74, by decide⟩
  m := 5
  T1 := T74_74
  T2 := Q2.T74_74_2
  h1 := (4,2,1,4,4)
  h2 := (4,2,1,4,1)
  D := [[4, 1, 2], [4, 1, 3], [4, 1, 4], [4, 1, 0], [4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_74_22 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨74, by decide⟩
  m := 5
  T1 := T74_74
  T2 := Q2.T74_74_2
  h1 := (4,2,2,0,4)
  h2 := (4,2,2,0,1)
  D := [[4, 2, 1], [4, 2, 2], [4, 2, 3], [4, 2, 4], [4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_74_23 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨74, by decide⟩
  m := 5
  T1 := T74_74
  T2 := Q2.T74_74_2
  h1 := (4,2,3,1,4)
  h2 := (4,2,3,1,1)
  D := [[4, 3, 0], [4, 3, 1], [4, 3, 2], [4, 3, 3], [4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_74_74_24 : ColCert where
  rK := ⟨74, by decide⟩
  rH := ⟨74, by decide⟩
  m := 5
  T1 := T74_74
  T2 := Q2.T74_74_2
  h1 := (4,2,4,2,4)
  h2 := (4,2,4,2,1)
  D := [[4, 4, 4], [4, 4, 0], [4, 4, 1], [4, 4, 2], [4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_0_0 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨0, by decide⟩
  m := 25
  T1 := T75_0
  T2 := Q2.T75_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_9_0 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨9, by decide⟩
  m := 25
  T1 := T75_9
  T2 := Q2.T75_9_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_9_1 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨9, by decide⟩
  m := 25
  T1 := T75_9
  T2 := Q2.T75_9_2
  h1 := (0,0,1,0,4)
  h2 := (0,0,1,0,4)
  D := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_9_2 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨9, by decide⟩
  m := 25
  T1 := T75_9
  T2 := Q2.T75_9_2
  h1 := (0,0,2,0,3)
  h2 := (0,0,2,0,3)
  D := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_9_3 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨9, by decide⟩
  m := 25
  T1 := T75_9
  T2 := Q2.T75_9_2
  h1 := (0,0,3,0,2)
  h2 := (0,0,3,0,2)
  D := [[0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_9_4 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨9, by decide⟩
  m := 25
  T1 := T75_9
  T2 := Q2.T75_9_2
  h1 := (0,0,4,0,1)
  h2 := (0,0,4,0,1)
  D := [[0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_12_0 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T75_12
  T2 := Q2.T75_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_12_1 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T75_12
  T2 := Q2.T75_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_12_2 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T75_12
  T2 := Q2.T75_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_12_3 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T75_12
  T2 := Q2.T75_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_12_4 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T75_12
  T2 := Q2.T75_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_27_0 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨27, by decide⟩
  m := 25
  T1 := T75_27
  T2 := Q2.T75_27_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_27_1 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨27, by decide⟩
  m := 25
  T1 := T75_27
  T2 := Q2.T75_27_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_27_2 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨27, by decide⟩
  m := 25
  T1 := T75_27
  T2 := Q2.T75_27_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_27_3 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨27, by decide⟩
  m := 25
  T1 := T75_27
  T2 := Q2.T75_27_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_27_4 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨27, by decide⟩
  m := 25
  T1 := T75_27
  T2 := Q2.T75_27_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_27_5 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨27, by decide⟩
  m := 25
  T1 := T75_27
  T2 := Q2.T75_27_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_27_10 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨27, by decide⟩
  m := 25
  T1 := T75_27
  T2 := Q2.T75_27_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_27_15 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨27, by decide⟩
  m := 25
  T1 := T75_27
  T2 := Q2.T75_27_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_27_20 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨27, by decide⟩
  m := 25
  T1 := T75_27
  T2 := Q2.T75_27_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_32_0 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T75_32
  T2 := Q2.T75_32_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_32_1 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T75_32
  T2 := Q2.T75_32_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_32_2 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T75_32
  T2 := Q2.T75_32_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_32_3 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T75_32
  T2 := Q2.T75_32_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_32_4 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T75_32
  T2 := Q2.T75_32_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_32_5 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T75_32
  T2 := Q2.T75_32_2
  h1 := (1,1,4,4,0)
  h2 := (1,1,4,4,3)
  D := [[1, 4, 2], [1, 4, 1], [1, 4, 0], [1, 4, 4], [1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_32_10 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T75_32
  T2 := Q2.T75_32_2
  h1 := (2,2,3,4,3)
  h2 := (2,2,3,4,4)
  D := [[2, 3, 0], [2, 3, 3], [2, 3, 1], [2, 3, 4], [2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_32_15 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T75_32
  T2 := Q2.T75_32_2
  h1 := (3,3,2,0,0)
  h2 := (3,3,2,0,4)
  D := [[3, 2, 4], [3, 2, 1], [3, 2, 3], [3, 2, 0], [3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_32_20 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T75_32
  T2 := Q2.T75_32_2
  h1 := (4,4,1,2,2)
  h2 := (4,4,1,2,4)
  D := [[4, 1, 4], [4, 1, 0], [4, 1, 1], [4, 1, 2], [4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_37_0 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T75_37
  T2 := Q2.T75_37_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_37_1 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T75_37
  T2 := Q2.T75_37_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_37_2 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T75_37
  T2 := Q2.T75_37_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
