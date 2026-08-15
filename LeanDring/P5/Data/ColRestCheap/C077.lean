/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C036
import LeanDring.P5.Data.EntryK.C037

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 76: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_135_95_0 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T135_95
  T2 := Q2.T135_95_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_95_1 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T135_95
  T2 := Q2.T135_95_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_95_2 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T135_95
  T2 := Q2.T135_95_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_95_3 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T135_95
  T2 := Q2.T135_95_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_95_4 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T135_95
  T2 := Q2.T135_95_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_95_5 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T135_95
  T2 := Q2.T135_95_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_95_10 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T135_95
  T2 := Q2.T135_95_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_95_15 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T135_95
  T2 := Q2.T135_95_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_95_20 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T135_95
  T2 := Q2.T135_95_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_103_0 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T135_103
  T2 := Q2.T135_103_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_103_1 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T135_103
  T2 := Q2.T135_103_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_103_2 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T135_103
  T2 := Q2.T135_103_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_103_3 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T135_103
  T2 := Q2.T135_103_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_103_4 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T135_103
  T2 := Q2.T135_103_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_103_15 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T135_103
  T2 := Q2.T135_103_2
  h1 := (3,4,2,2,1)
  h2 := (3,4,2,2,2)
  D := [[3, 4, 0, 2], [3, 4, 0, 3], [3, 4, 0, 4], [3, 4, 0, 0], [3, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_107_0 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T135_107
  T2 := Q2.T135_107_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_107_1 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T135_107
  T2 := Q2.T135_107_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_107_2 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T135_107
  T2 := Q2.T135_107_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_107_3 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T135_107
  T2 := Q2.T135_107_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_107_4 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T135_107
  T2 := Q2.T135_107_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_114_0 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T135_114
  T2 := Q2.T135_114_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_114_1 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T135_114
  T2 := Q2.T135_114_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_114_2 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T135_114
  T2 := Q2.T135_114_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_114_3 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T135_114
  T2 := Q2.T135_114_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_114_4 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T135_114
  T2 := Q2.T135_114_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_114_5 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T135_114
  T2 := Q2.T135_114_2
  h1 := (1,1,0,0,0)
  h2 := (1,1,0,0,0)
  D := [[1, 1, 4, 4], [1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1], [1, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_114_10 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T135_114
  T2 := Q2.T135_114_2
  h1 := (2,2,0,1,0)
  h2 := (2,2,0,1,0)
  D := [[2, 2, 2, 3], [2, 2, 2, 1], [2, 2, 2, 4], [2, 2, 2, 2], [2, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_114_15 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T135_114
  T2 := Q2.T135_114_2
  h1 := (3,3,0,3,1)
  h2 := (3,3,0,3,1)
  D := [[3, 3, 4, 3], [3, 3, 4, 0], [3, 3, 4, 2], [3, 3, 4, 4], [3, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_114_20 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T135_114
  T2 := Q2.T135_114_2
  h1 := (4,4,0,1,4)
  h2 := (4,4,0,1,4)
  D := [[4, 4, 0, 0], [4, 4, 0, 1], [4, 4, 0, 2], [4, 4, 0, 3], [4, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_135_0 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨135, by decide⟩
  m := 5
  T1 := T135_135
  T2 := Q2.T135_135_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_135_1 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨135, by decide⟩
  m := 5
  T1 := T135_135
  T2 := Q2.T135_135_2
  h1 := (0,1,2,0,4)
  h2 := (0,1,2,0,0)
  D := [[0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_135_2 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨135, by decide⟩
  m := 5
  T1 := T135_135
  T2 := Q2.T135_135_2
  h1 := (0,2,4,0,0)
  h2 := (0,2,4,0,2)
  D := [[0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_135_3 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨135, by decide⟩
  m := 5
  T1 := T135_135
  T2 := Q2.T135_135_2
  h1 := (0,3,1,0,3)
  h2 := (0,3,1,0,1)
  D := [[0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_135_4 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨135, by decide⟩
  m := 5
  T1 := T135_135
  T2 := Q2.T135_135_2
  h1 := (0,4,3,0,3)
  h2 := (0,4,3,0,2)
  D := [[0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_135_5 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨135, by decide⟩
  m := 5
  T1 := T135_135
  T2 := Q2.T135_135_2
  h1 := (1,0,3,0,3)
  h2 := (1,0,3,0,2)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_135_6 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨135, by decide⟩
  m := 5
  T1 := T135_135
  T2 := Q2.T135_135_2
  h1 := (1,1,0,0,0)
  h2 := (1,1,0,0,0)
  D := [[1, 1, 4, 4], [1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1], [1, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_135_7 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨135, by decide⟩
  m := 5
  T1 := T135_135
  T2 := Q2.T135_135_2
  h1 := (1,2,2,0,4)
  h2 := (1,2,2,0,0)
  D := [[1, 2, 3, 3], [1, 2, 3, 1], [1, 2, 3, 4], [1, 2, 3, 2], [1, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_135_8 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨135, by decide⟩
  m := 5
  T1 := T135_135
  T2 := Q2.T135_135_2
  h1 := (1,3,4,0,0)
  h2 := (1,3,4,0,2)
  D := [[1, 3, 2, 2], [1, 3, 2, 4], [1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_135_9 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨135, by decide⟩
  m := 5
  T1 := T135_135
  T2 := Q2.T135_135_2
  h1 := (1,4,1,0,3)
  h2 := (1,4,1,0,1)
  D := [[1, 4, 1, 1], [1, 4, 1, 2], [1, 4, 1, 3], [1, 4, 1, 4], [1, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_135_10 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨135, by decide⟩
  m := 5
  T1 := T135_135
  T2 := Q2.T135_135_2
  h1 := (2,0,1,0,1)
  h2 := (2,0,1,0,4)
  D := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_135_11 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨135, by decide⟩
  m := 5
  T1 := T135_135
  T2 := Q2.T135_135_2
  h1 := (2,1,3,0,1)
  h2 := (2,1,3,0,0)
  D := [[2, 1, 3, 4], [2, 1, 3, 3], [2, 1, 3, 2], [2, 1, 3, 1], [2, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_135_12 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨135, by decide⟩
  m := 5
  T1 := T135_135
  T2 := Q2.T135_135_2
  h1 := (2,2,0,0,3)
  h2 := (2,2,0,0,3)
  D := [[2, 2, 1, 3], [2, 2, 1, 1], [2, 2, 1, 4], [2, 2, 1, 2], [2, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_135_13 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨135, by decide⟩
  m := 5
  T1 := T135_135
  T2 := Q2.T135_135_2
  h1 := (2,3,2,0,2)
  h2 := (2,3,2,0,3)
  D := [[2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1], [2, 3, 4, 3], [2, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_135_14 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨135, by decide⟩
  m := 5
  T1 := T135_135
  T2 := Q2.T135_135_2
  h1 := (2,4,4,0,3)
  h2 := (2,4,4,0,0)
  D := [[2, 4, 2, 1], [2, 4, 2, 2], [2, 4, 2, 3], [2, 4, 2, 4], [2, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_135_15 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨135, by decide⟩
  m := 5
  T1 := T135_135
  T2 := Q2.T135_135_2
  h1 := (3,0,4,0,4)
  h2 := (3,0,4,0,1)
  D := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_135_16 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨135, by decide⟩
  m := 5
  T1 := T135_135
  T2 := Q2.T135_135_2
  h1 := (3,1,1,0,2)
  h2 := (3,1,1,0,0)
  D := [[3, 1, 2, 0], [3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2], [3, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_135_17 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨135, by decide⟩
  m := 5
  T1 := T135_135
  T2 := Q2.T135_135_2
  h1 := (3,2,3,0,2)
  h2 := (3,2,3,0,1)
  D := [[3, 2, 4, 0], [3, 2, 4, 3], [3, 2, 4, 1], [3, 2, 4, 4], [3, 2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_135_18 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨135, by decide⟩
  m := 5
  T1 := T135_135
  T2 := Q2.T135_135_2
  h1 := (3,3,0,0,4)
  h2 := (3,3,0,0,4)
  D := [[3, 3, 1, 0], [3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_135_19 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨135, by decide⟩
  m := 5
  T1 := T135_135
  T2 := Q2.T135_135_2
  h1 := (3,4,2,0,3)
  h2 := (3,4,2,0,4)
  D := [[3, 4, 3, 0], [3, 4, 3, 1], [3, 4, 3, 2], [3, 4, 3, 3], [3, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_135_20 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨135, by decide⟩
  m := 5
  T1 := T135_135
  T2 := Q2.T135_135_2
  h1 := (4,0,2,0,2)
  h2 := (4,0,2,0,3)
  D := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_135_21 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨135, by decide⟩
  m := 5
  T1 := T135_135
  T2 := Q2.T135_135_2
  h1 := (4,1,4,0,3)
  h2 := (4,1,4,0,0)
  D := [[4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4], [4, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_135_22 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨135, by decide⟩
  m := 5
  T1 := T135_135
  T2 := Q2.T135_135_2
  h1 := (4,2,1,0,1)
  h2 := (4,2,1,0,4)
  D := [[4, 2, 2, 4], [4, 2, 2, 2], [4, 2, 2, 0], [4, 2, 2, 3], [4, 2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_135_23 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨135, by decide⟩
  m := 5
  T1 := T135_135
  T2 := Q2.T135_135_2
  h1 := (4,3,3,0,1)
  h2 := (4,3,3,0,0)
  D := [[4, 3, 3, 1], [4, 3, 3, 3], [4, 3, 3, 0], [4, 3, 3, 2], [4, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_135_24 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨135, by decide⟩
  m := 5
  T1 := T135_135
  T2 := Q2.T135_135_2
  h1 := (4,4,0,0,3)
  h2 := (4,4,0,0,3)
  D := [[4, 4, 4, 3], [4, 4, 4, 4], [4, 4, 4, 0], [4, 4, 4, 1], [4, 4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_0_0 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨0, by decide⟩
  m := 5
  T1 := T136_0
  T2 := Q2.T136_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_5_0 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T136_5
  T2 := Q2.T136_5_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_5_1 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T136_5
  T2 := Q2.T136_5_2
  h1 := (1,0,1,4,4)
  h2 := (1,0,1,4,4)
  D := [[1, 0, 4, 0], [1, 0, 4, 0], [1, 0, 4, 0], [1, 0, 4, 0], [1, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_5_2 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T136_5
  T2 := Q2.T136_5_2
  h1 := (2,0,2,3,2)
  h2 := (2,0,2,3,2)
  D := [[2, 0, 3, 1], [2, 0, 3, 1], [2, 0, 3, 1], [2, 0, 3, 1], [2, 0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_5_3 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T136_5
  T2 := Q2.T136_5_2
  h1 := (3,0,3,2,4)
  h2 := (3,0,3,2,4)
  D := [[3, 0, 2, 3], [3, 0, 2, 3], [3, 0, 2, 3], [3, 0, 2, 3], [3, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_5_4 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T136_5
  T2 := Q2.T136_5_2
  h1 := (4,0,4,1,0)
  h2 := (4,0,4,1,0)
  D := [[4, 0, 1, 1], [4, 0, 1, 1], [4, 0, 1, 1], [4, 0, 1, 1], [4, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
