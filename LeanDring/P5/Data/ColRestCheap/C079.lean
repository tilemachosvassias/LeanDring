/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C037

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 78: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_136_84_10 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T136_84
  T2 := Q2.T136_84_2
  h1 := (2,0,2,0,0)
  h2 := (2,0,2,0,0)
  D := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_84_15 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T136_84
  T2 := Q2.T136_84_2
  h1 := (3,0,3,0,0)
  h2 := (3,0,3,0,0)
  D := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_84_20 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T136_84
  T2 := Q2.T136_84_2
  h1 := (4,0,4,0,0)
  h2 := (4,0,4,0,0)
  D := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_91_0 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T136_91
  T2 := Q2.T136_91_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_91_1 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T136_91
  T2 := Q2.T136_91_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_91_2 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T136_91
  T2 := Q2.T136_91_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_91_3 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T136_91
  T2 := Q2.T136_91_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_91_4 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T136_91
  T2 := Q2.T136_91_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_91_5 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T136_91
  T2 := Q2.T136_91_2
  h1 := (1,4,1,4,4)
  h2 := (1,4,1,4,4)
  D := [[1, 4, 0, 0], [1, 4, 0, 1], [1, 4, 0, 2], [1, 4, 0, 3], [1, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_98_0 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T136_98
  T2 := Q2.T136_98_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_98_1 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T136_98
  T2 := Q2.T136_98_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_98_2 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T136_98
  T2 := Q2.T136_98_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_98_3 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T136_98
  T2 := Q2.T136_98_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_98_4 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T136_98
  T2 := Q2.T136_98_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_98_5 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T136_98
  T2 := Q2.T136_98_2
  h1 := (1,3,1,1,3)
  h2 := (1,3,1,1,3)
  D := [[1, 3, 3, 2], [1, 3, 3, 4], [1, 3, 3, 1], [1, 3, 3, 3], [1, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_102_0 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T136_102
  T2 := Q2.T136_102_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_102_1 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T136_102
  T2 := Q2.T136_102_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_102_2 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T136_102
  T2 := Q2.T136_102_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_102_3 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T136_102
  T2 := Q2.T136_102_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_102_4 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T136_102
  T2 := Q2.T136_102_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_102_5 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T136_102
  T2 := Q2.T136_102_2
  h1 := (1,2,1,3,1)
  h2 := (1,2,1,3,1)
  D := [[1, 2, 1, 3], [1, 2, 1, 1], [1, 2, 1, 4], [1, 2, 1, 2], [1, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_102_10 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T136_102
  T2 := Q2.T136_102_2
  h1 := (2,4,2,3,2)
  h2 := (2,4,2,3,2)
  D := [[2, 4, 0, 4], [2, 4, 0, 0], [2, 4, 0, 1], [2, 4, 0, 2], [2, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_109_0 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T136_109
  T2 := Q2.T136_109_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_109_1 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T136_109
  T2 := Q2.T136_109_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_109_2 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T136_109
  T2 := Q2.T136_109_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_109_3 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T136_109
  T2 := Q2.T136_109_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_109_4 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T136_109
  T2 := Q2.T136_109_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_109_5 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T136_109
  T2 := Q2.T136_109_2
  h1 := (1,1,1,0,0)
  h2 := (1,1,1,0,0)
  D := [[1, 1, 4, 0], [1, 1, 4, 4], [1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_109_10 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T136_109
  T2 := Q2.T136_109_2
  h1 := (2,2,2,1,1)
  h2 := (2,2,2,1,1)
  D := [[2, 2, 2, 3], [2, 2, 2, 1], [2, 2, 2, 4], [2, 2, 2, 2], [2, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_109_15 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T136_109
  T2 := Q2.T136_109_2
  h1 := (3,3,3,3,4)
  h2 := (3,3,3,3,4)
  D := [[3, 3, 4, 0], [3, 3, 4, 2], [3, 3, 4, 4], [3, 3, 4, 1], [3, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_109_20 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T136_109
  T2 := Q2.T136_109_2
  h1 := (4,4,4,1,0)
  h2 := (4,4,4,1,0)
  D := [[4, 4, 0, 2], [4, 4, 0, 3], [4, 4, 0, 4], [4, 4, 0, 0], [4, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_110_0 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T136_110
  T2 := Q2.T136_110_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_110_1 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T136_110
  T2 := Q2.T136_110_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_110_2 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T136_110
  T2 := Q2.T136_110_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_110_3 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T136_110
  T2 := Q2.T136_110_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_110_4 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T136_110
  T2 := Q2.T136_110_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_110_5 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T136_110
  T2 := Q2.T136_110_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_110_10 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T136_110
  T2 := Q2.T136_110_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_110_15 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T136_110
  T2 := Q2.T136_110_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_110_20 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T136_110
  T2 := Q2.T136_110_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_110_25 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T136_110
  T2 := Q2.T136_110_2
  h1 := (0,1,0,0,0)
  h2 := (0,1,0,0,0)
  D := [[0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_110_50 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T136_110
  T2 := Q2.T136_110_2
  h1 := (0,2,0,0,0)
  h2 := (0,2,0,0,0)
  D := [[0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_110_75 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T136_110
  T2 := Q2.T136_110_2
  h1 := (0,3,0,0,0)
  h2 := (0,3,0,0,0)
  D := [[0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_110_100 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T136_110
  T2 := Q2.T136_110_2
  h1 := (0,4,0,0,0)
  h2 := (0,4,0,0,0)
  D := [[0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_136_0 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨136, by decide⟩
  m := 5
  T1 := T136_136
  T2 := Q2.T136_136_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_136_1 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨136, by decide⟩
  m := 5
  T1 := T136_136
  T2 := Q2.T136_136_2
  h1 := (0,1,0,0,0)
  h2 := (0,1,0,0,0)
  D := [[0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_136_2 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨136, by decide⟩
  m := 5
  T1 := T136_136
  T2 := Q2.T136_136_2
  h1 := (0,2,0,0,0)
  h2 := (0,2,0,0,0)
  D := [[0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_136_3 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨136, by decide⟩
  m := 5
  T1 := T136_136
  T2 := Q2.T136_136_2
  h1 := (0,3,0,0,0)
  h2 := (0,3,0,0,0)
  D := [[0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_136_4 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨136, by decide⟩
  m := 5
  T1 := T136_136
  T2 := Q2.T136_136_2
  h1 := (0,4,0,0,0)
  h2 := (0,4,0,0,0)
  D := [[0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_136_5 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨136, by decide⟩
  m := 5
  T1 := T136_136
  T2 := Q2.T136_136_2
  h1 := (1,0,1,0,0)
  h2 := (1,0,1,0,0)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_136_6 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨136, by decide⟩
  m := 5
  T1 := T136_136
  T2 := Q2.T136_136_2
  h1 := (1,1,1,0,1)
  h2 := (1,1,1,0,1)
  D := [[1, 1, 4, 1], [1, 1, 4, 0], [1, 1, 4, 4], [1, 1, 4, 3], [1, 1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_136_7 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨136, by decide⟩
  m := 5
  T1 := T136_136
  T2 := Q2.T136_136_2
  h1 := (1,2,1,0,2)
  h2 := (1,2,1,0,2)
  D := [[1, 2, 3, 2], [1, 2, 3, 0], [1, 2, 3, 3], [1, 2, 3, 1], [1, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_136_8 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨136, by decide⟩
  m := 5
  T1 := T136_136
  T2 := Q2.T136_136_2
  h1 := (1,3,1,0,3)
  h2 := (1,3,1,0,3)
  D := [[1, 3, 2, 3], [1, 3, 2, 0], [1, 3, 2, 2], [1, 3, 2, 4], [1, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_136_9 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨136, by decide⟩
  m := 5
  T1 := T136_136
  T2 := Q2.T136_136_2
  h1 := (1,4,1,0,4)
  h2 := (1,4,1,0,4)
  D := [[1, 4, 1, 4], [1, 4, 1, 0], [1, 4, 1, 1], [1, 4, 1, 2], [1, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_136_10 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨136, by decide⟩
  m := 5
  T1 := T136_136
  T2 := Q2.T136_136_2
  h1 := (2,0,2,0,0)
  h2 := (2,0,2,0,0)
  D := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_136_11 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨136, by decide⟩
  m := 5
  T1 := T136_136
  T2 := Q2.T136_136_2
  h1 := (2,1,2,0,2)
  h2 := (2,1,2,0,2)
  D := [[2, 1, 3, 4], [2, 1, 3, 3], [2, 1, 3, 2], [2, 1, 3, 1], [2, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_136_12 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨136, by decide⟩
  m := 5
  T1 := T136_136
  T2 := Q2.T136_136_2
  h1 := (2,2,2,0,4)
  h2 := (2,2,2,0,4)
  D := [[2, 2, 1, 3], [2, 2, 1, 1], [2, 2, 1, 4], [2, 2, 1, 2], [2, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_136_13 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨136, by decide⟩
  m := 5
  T1 := T136_136
  T2 := Q2.T136_136_2
  h1 := (2,3,2,0,1)
  h2 := (2,3,2,0,1)
  D := [[2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1], [2, 3, 4, 3], [2, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_136_14 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨136, by decide⟩
  m := 5
  T1 := T136_136
  T2 := Q2.T136_136_2
  h1 := (2,4,2,0,3)
  h2 := (2,4,2,0,3)
  D := [[2, 4, 2, 1], [2, 4, 2, 2], [2, 4, 2, 3], [2, 4, 2, 4], [2, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_136_15 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨136, by decide⟩
  m := 5
  T1 := T136_136
  T2 := Q2.T136_136_2
  h1 := (3,0,3,0,0)
  h2 := (3,0,3,0,0)
  D := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
