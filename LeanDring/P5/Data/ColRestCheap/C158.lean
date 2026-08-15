/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C016

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 157: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_68_24_15 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨24, by decide⟩
  m := 25
  T1 := T68_24
  T2 := Q2.T68_24_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_24_20 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨24, by decide⟩
  m := 25
  T1 := T68_24
  T2 := Q2.T68_24_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_30_0 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T68_30
  T2 := Q2.T68_30_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_30_1 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T68_30
  T2 := Q2.T68_30_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_30_2 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T68_30
  T2 := Q2.T68_30_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_30_3 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T68_30
  T2 := Q2.T68_30_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_30_4 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T68_30
  T2 := Q2.T68_30_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_30_5 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T68_30
  T2 := Q2.T68_30_2
  h1 := (1,2,3,2,3)
  h2 := (1,2,3,2,0)
  D := [[1, 3, 2], [1, 3, 1], [1, 3, 0], [1, 3, 4], [1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_30_10 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T68_30
  T2 := Q2.T68_30_2
  h1 := (2,4,1,1,4)
  h2 := (2,4,1,1,3)
  D := [[2, 1, 2], [2, 1, 0], [2, 1, 3], [2, 1, 1], [2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_30_15 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T68_30
  T2 := Q2.T68_30_2
  h1 := (3,1,4,2,1)
  h2 := (3,1,4,2,3)
  D := [[3, 4, 0], [3, 4, 2], [3, 4, 4], [3, 4, 1], [3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_30_20 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T68_30
  T2 := Q2.T68_30_2
  h1 := (4,3,2,0,4)
  h2 := (4,3,2,0,3)
  D := [[4, 2, 1], [4, 2, 2], [4, 2, 3], [4, 2, 4], [4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_35_0 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T68_35
  T2 := Q2.T68_35_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_35_1 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T68_35
  T2 := Q2.T68_35_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_35_2 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T68_35
  T2 := Q2.T68_35_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_35_3 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T68_35
  T2 := Q2.T68_35_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_35_4 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T68_35
  T2 := Q2.T68_35_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_35_5 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T68_35
  T2 := Q2.T68_35_2
  h1 := (1,2,4,2,0)
  h2 := (1,2,4,2,2)
  D := [[1, 4, 3], [1, 4, 2], [1, 4, 1], [1, 4, 0], [1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_35_10 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T68_35
  T2 := Q2.T68_35_2
  h1 := (2,4,3,1,0)
  h2 := (2,4,3,1,4)
  D := [[2, 3, 0], [2, 3, 3], [2, 3, 1], [2, 3, 4], [2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_35_15 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T68_35
  T2 := Q2.T68_35_2
  h1 := (3,1,2,2,3)
  h2 := (3,1,2,2,0)
  D := [[3, 2, 1], [3, 2, 3], [3, 2, 0], [3, 2, 2], [3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_35_20 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T68_35
  T2 := Q2.T68_35_2
  h1 := (4,3,1,0,4)
  h2 := (4,3,1,0,3)
  D := [[4, 1, 1], [4, 1, 2], [4, 1, 3], [4, 1, 4], [4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_40_0 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T68_40
  T2 := Q2.T68_40_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_40_1 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T68_40
  T2 := Q2.T68_40_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_40_2 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T68_40
  T2 := Q2.T68_40_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_40_3 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T68_40
  T2 := Q2.T68_40_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_40_4 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T68_40
  T2 := Q2.T68_40_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_40_5 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T68_40
  T2 := Q2.T68_40_2
  h1 := (1,2,1,2,4)
  h2 := (1,2,1,2,1)
  D := [[1, 1, 3], [1, 1, 2], [1, 1, 1], [1, 1, 0], [1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_40_10 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T68_40
  T2 := Q2.T68_40_2
  h1 := (2,4,2,1,2)
  h2 := (2,4,2,1,1)
  D := [[2, 2, 2], [2, 2, 0], [2, 2, 3], [2, 2, 1], [2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_40_15 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T68_40
  T2 := Q2.T68_40_2
  h1 := (3,1,3,2,2)
  h2 := (3,1,3,2,4)
  D := [[3, 3, 2], [3, 3, 4], [3, 3, 1], [3, 3, 3], [3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_40_20 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T68_40
  T2 := Q2.T68_40_2
  h1 := (4,3,4,0,4)
  h2 := (4,3,4,0,3)
  D := [[4, 4, 3], [4, 4, 4], [4, 4, 0], [4, 4, 1], [4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_45_0 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T68_45
  T2 := Q2.T68_45_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_45_1 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T68_45
  T2 := Q2.T68_45_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_45_2 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T68_45
  T2 := Q2.T68_45_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_45_3 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T68_45
  T2 := Q2.T68_45_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_45_4 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T68_45
  T2 := Q2.T68_45_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_45_5 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T68_45
  T2 := Q2.T68_45_2
  h1 := (1,2,2,2,1)
  h2 := (1,2,2,2,3)
  D := [[1, 2, 2], [1, 2, 1], [1, 2, 0], [1, 2, 4], [1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_45_10 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T68_45
  T2 := Q2.T68_45_2
  h1 := (2,4,4,1,3)
  h2 := (2,4,4,1,2)
  D := [[2, 4, 1], [2, 4, 4], [2, 4, 2], [2, 4, 0], [2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_45_15 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T68_45
  T2 := Q2.T68_45_2
  h1 := (3,1,1,2,4)
  h2 := (3,1,1,2,1)
  D := [[3, 1, 2], [3, 1, 4], [3, 1, 1], [3, 1, 3], [3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_45_20 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T68_45
  T2 := Q2.T68_45_2
  h1 := (4,3,3,0,4)
  h2 := (4,3,3,0,3)
  D := [[4, 3, 0], [4, 3, 1], [4, 3, 2], [4, 3, 3], [4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_50_0 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T68_50
  T2 := Q2.T68_50_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_50_1 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T68_50
  T2 := Q2.T68_50_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_50_2 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T68_50
  T2 := Q2.T68_50_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_50_3 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T68_50
  T2 := Q2.T68_50_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_50_4 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T68_50
  T2 := Q2.T68_50_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_50_5 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T68_50
  T2 := Q2.T68_50_2
  h1 := (1,2,0,2,2)
  h2 := (1,2,0,2,4)
  D := [[1, 0, 0], [1, 0, 4], [1, 0, 3], [1, 0, 2], [1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_50_10 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T68_50
  T2 := Q2.T68_50_2
  h1 := (2,4,0,1,1)
  h2 := (2,4,0,1,0)
  D := [[2, 0, 0], [2, 0, 3], [2, 0, 1], [2, 0, 4], [2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_50_15 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T68_50
  T2 := Q2.T68_50_2
  h1 := (3,1,0,2,0)
  h2 := (3,1,0,2,2)
  D := [[3, 0, 0], [3, 0, 2], [3, 0, 4], [3, 0, 1], [3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_50_20 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T68_50
  T2 := Q2.T68_50_2
  h1 := (4,3,0,0,4)
  h2 := (4,3,0,0,3)
  D := [[4, 0, 0], [4, 0, 1], [4, 0, 2], [4, 0, 3], [4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_68_0 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T68_68
  T2 := Q2.T68_68_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_68_1 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T68_68
  T2 := Q2.T68_68_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_68_2 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T68_68
  T2 := Q2.T68_68_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_68_3 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T68_68
  T2 := Q2.T68_68_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_68_4 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T68_68
  T2 := Q2.T68_68_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_68_5 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T68_68
  T2 := Q2.T68_68_2
  h1 := (1,2,0,2,0)
  h2 := (1,2,0,2,2)
  D := [[1, 0, 3], [1, 0, 2], [1, 0, 1], [1, 0, 0], [1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_68_6 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T68_68
  T2 := Q2.T68_68_2
  h1 := (1,2,1,4,0)
  h2 := (1,2,1,4,2)
  D := [[1, 1, 4], [1, 1, 3], [1, 1, 2], [1, 1, 1], [1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_68_7 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T68_68
  T2 := Q2.T68_68_2
  h1 := (1,2,2,1,0)
  h2 := (1,2,2,1,2)
  D := [[1, 2, 0], [1, 2, 4], [1, 2, 3], [1, 2, 2], [1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_68_8 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T68_68
  T2 := Q2.T68_68_2
  h1 := (1,2,3,3,0)
  h2 := (1,2,3,3,2)
  D := [[1, 3, 1], [1, 3, 0], [1, 3, 4], [1, 3, 3], [1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_68_9 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T68_68
  T2 := Q2.T68_68_2
  h1 := (1,2,4,0,0)
  h2 := (1,2,4,0,2)
  D := [[1, 4, 2], [1, 4, 1], [1, 4, 0], [1, 4, 4], [1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_68_10 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T68_68
  T2 := Q2.T68_68_2
  h1 := (2,4,0,1,2)
  h2 := (2,4,0,1,1)
  D := [[2, 0, 1], [2, 0, 4], [2, 0, 2], [2, 0, 0], [2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_68_11 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T68_68
  T2 := Q2.T68_68_2
  h1 := (2,4,1,3,2)
  h2 := (2,4,1,3,1)
  D := [[2, 1, 3], [2, 1, 1], [2, 1, 4], [2, 1, 2], [2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_68_12 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T68_68
  T2 := Q2.T68_68_2
  h1 := (2,4,2,0,2)
  h2 := (2,4,2,0,1)
  D := [[2, 2, 0], [2, 2, 3], [2, 2, 1], [2, 2, 4], [2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
