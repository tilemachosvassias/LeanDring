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
rest tier, chunk 154: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_66_19_15 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T66_19
  T2 := Q2.T66_19_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_19_20 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T66_19
  T2 := Q2.T66_19_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_30_0 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T66_30
  T2 := Q2.T66_30_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_30_1 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T66_30
  T2 := Q2.T66_30_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_30_2 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T66_30
  T2 := Q2.T66_30_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_30_3 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T66_30
  T2 := Q2.T66_30_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_30_4 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T66_30
  T2 := Q2.T66_30_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_30_5 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T66_30
  T2 := Q2.T66_30_2
  h1 := (1,2,3,2,3)
  h2 := (1,2,3,2,0)
  D := [[1, 3, 1], [1, 3, 0], [1, 3, 4], [1, 3, 3], [1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_30_10 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T66_30
  T2 := Q2.T66_30_2
  h1 := (2,4,1,1,4)
  h2 := (2,4,1,1,3)
  D := [[2, 1, 4], [2, 1, 2], [2, 1, 0], [2, 1, 3], [2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_30_15 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T66_30
  T2 := Q2.T66_30_2
  h1 := (3,1,4,2,1)
  h2 := (3,1,4,2,3)
  D := [[3, 4, 4], [3, 4, 1], [3, 4, 3], [3, 4, 0], [3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_30_20 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T66_30
  T2 := Q2.T66_30_2
  h1 := (4,3,2,0,4)
  h2 := (4,3,2,0,3)
  D := [[4, 2, 1], [4, 2, 2], [4, 2, 3], [4, 2, 4], [4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_35_0 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T66_35
  T2 := Q2.T66_35_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_35_1 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T66_35
  T2 := Q2.T66_35_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_35_2 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T66_35
  T2 := Q2.T66_35_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_35_3 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T66_35
  T2 := Q2.T66_35_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_35_4 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T66_35
  T2 := Q2.T66_35_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_35_5 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T66_35
  T2 := Q2.T66_35_2
  h1 := (1,2,4,2,0)
  h2 := (1,2,4,2,2)
  D := [[1, 4, 3], [1, 4, 2], [1, 4, 1], [1, 4, 0], [1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_35_10 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T66_35
  T2 := Q2.T66_35_2
  h1 := (2,4,3,1,0)
  h2 := (2,4,3,1,4)
  D := [[2, 3, 2], [2, 3, 0], [2, 3, 3], [2, 3, 1], [2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_35_15 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T66_35
  T2 := Q2.T66_35_2
  h1 := (3,1,2,2,3)
  h2 := (3,1,2,2,0)
  D := [[3, 2, 2], [3, 2, 4], [3, 2, 1], [3, 2, 3], [3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_35_20 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T66_35
  T2 := Q2.T66_35_2
  h1 := (4,3,1,0,4)
  h2 := (4,3,1,0,3)
  D := [[4, 1, 3], [4, 1, 4], [4, 1, 0], [4, 1, 1], [4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_40_0 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T66_40
  T2 := Q2.T66_40_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_40_1 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T66_40
  T2 := Q2.T66_40_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_40_2 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T66_40
  T2 := Q2.T66_40_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_40_3 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T66_40
  T2 := Q2.T66_40_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_40_4 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T66_40
  T2 := Q2.T66_40_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_40_5 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T66_40
  T2 := Q2.T66_40_2
  h1 := (1,2,1,2,4)
  h2 := (1,2,1,2,1)
  D := [[1, 1, 3], [1, 1, 2], [1, 1, 1], [1, 1, 0], [1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_40_10 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T66_40
  T2 := Q2.T66_40_2
  h1 := (2,4,2,1,2)
  h2 := (2,4,2,1,1)
  D := [[2, 2, 0], [2, 2, 3], [2, 2, 1], [2, 2, 4], [2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_40_15 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T66_40
  T2 := Q2.T66_40_2
  h1 := (3,1,3,2,2)
  h2 := (3,1,3,2,4)
  D := [[3, 3, 1], [3, 3, 3], [3, 3, 0], [3, 3, 2], [3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_40_20 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T66_40
  T2 := Q2.T66_40_2
  h1 := (4,3,4,0,4)
  h2 := (4,3,4,0,3)
  D := [[4, 4, 1], [4, 4, 2], [4, 4, 3], [4, 4, 4], [4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_45_0 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T66_45
  T2 := Q2.T66_45_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_45_1 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T66_45
  T2 := Q2.T66_45_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_45_2 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T66_45
  T2 := Q2.T66_45_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_45_3 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T66_45
  T2 := Q2.T66_45_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_45_4 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T66_45
  T2 := Q2.T66_45_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_45_5 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T66_45
  T2 := Q2.T66_45_2
  h1 := (1,2,2,2,1)
  h2 := (1,2,2,2,3)
  D := [[1, 2, 1], [1, 2, 0], [1, 2, 4], [1, 2, 3], [1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_45_10 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T66_45
  T2 := Q2.T66_45_2
  h1 := (2,4,4,1,3)
  h2 := (2,4,4,1,2)
  D := [[2, 4, 0], [2, 4, 3], [2, 4, 1], [2, 4, 4], [2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_45_15 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T66_45
  T2 := Q2.T66_45_2
  h1 := (3,1,1,2,4)
  h2 := (3,1,1,2,1)
  D := [[3, 1, 2], [3, 1, 4], [3, 1, 1], [3, 1, 3], [3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_45_20 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T66_45
  T2 := Q2.T66_45_2
  h1 := (4,3,3,0,4)
  h2 := (4,3,3,0,3)
  D := [[4, 3, 2], [4, 3, 3], [4, 3, 4], [4, 3, 0], [4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_50_0 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T66_50
  T2 := Q2.T66_50_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_50_1 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T66_50
  T2 := Q2.T66_50_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_50_2 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T66_50
  T2 := Q2.T66_50_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_50_3 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T66_50
  T2 := Q2.T66_50_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_50_4 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T66_50
  T2 := Q2.T66_50_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_50_5 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T66_50
  T2 := Q2.T66_50_2
  h1 := (1,2,0,2,2)
  h2 := (1,2,0,2,4)
  D := [[1, 0, 2], [1, 0, 1], [1, 0, 0], [1, 0, 4], [1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_50_10 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T66_50
  T2 := Q2.T66_50_2
  h1 := (2,4,0,1,1)
  h2 := (2,4,0,1,0)
  D := [[2, 0, 4], [2, 0, 2], [2, 0, 0], [2, 0, 3], [2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_50_15 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T66_50
  T2 := Q2.T66_50_2
  h1 := (3,1,0,2,0)
  h2 := (3,1,0,2,2)
  D := [[3, 0, 1], [3, 0, 3], [3, 0, 0], [3, 0, 2], [3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_50_20 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T66_50
  T2 := Q2.T66_50_2
  h1 := (4,3,0,0,4)
  h2 := (4,3,0,0,3)
  D := [[4, 0, 3], [4, 0, 4], [4, 0, 0], [4, 0, 1], [4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_66_0 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T66_66
  T2 := Q2.T66_66_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_66_1 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T66_66
  T2 := Q2.T66_66_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_66_2 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T66_66
  T2 := Q2.T66_66_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_66_3 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T66_66
  T2 := Q2.T66_66_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_66_4 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T66_66
  T2 := Q2.T66_66_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_66_5 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T66_66
  T2 := Q2.T66_66_2
  h1 := (1,2,0,2,1)
  h2 := (1,2,0,2,3)
  D := [[1, 0, 1], [1, 0, 0], [1, 0, 4], [1, 0, 3], [1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_66_6 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T66_66
  T2 := Q2.T66_66_2
  h1 := (1,2,1,1,1)
  h2 := (1,2,1,1,3)
  D := [[1, 1, 0], [1, 1, 4], [1, 1, 3], [1, 1, 2], [1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_66_7 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T66_66
  T2 := Q2.T66_66_2
  h1 := (1,2,2,0,1)
  h2 := (1,2,2,0,3)
  D := [[1, 2, 4], [1, 2, 3], [1, 2, 2], [1, 2, 1], [1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_66_8 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T66_66
  T2 := Q2.T66_66_2
  h1 := (1,2,3,4,1)
  h2 := (1,2,3,4,3)
  D := [[1, 3, 3], [1, 3, 2], [1, 3, 1], [1, 3, 0], [1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_66_9 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T66_66
  T2 := Q2.T66_66_2
  h1 := (1,2,4,3,1)
  h2 := (1,2,4,3,3)
  D := [[1, 4, 2], [1, 4, 1], [1, 4, 0], [1, 4, 4], [1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_66_10 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T66_66
  T2 := Q2.T66_66_2
  h1 := (2,4,0,1,4)
  h2 := (2,4,0,1,3)
  D := [[2, 0, 2], [2, 0, 0], [2, 0, 3], [2, 0, 1], [2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_66_11 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T66_66
  T2 := Q2.T66_66_2
  h1 := (2,4,1,0,4)
  h2 := (2,4,1,0,3)
  D := [[2, 1, 0], [2, 1, 3], [2, 1, 1], [2, 1, 4], [2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_66_12 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T66_66
  T2 := Q2.T66_66_2
  h1 := (2,4,2,4,4)
  h2 := (2,4,2,4,3)
  D := [[2, 2, 3], [2, 2, 1], [2, 2, 4], [2, 2, 2], [2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
