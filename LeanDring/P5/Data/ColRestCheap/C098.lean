/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C041

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 97: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_142_30_2 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T142_30
  T2 := Q2.T142_30_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_30_3 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T142_30
  T2 := Q2.T142_30_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_30_4 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T142_30
  T2 := Q2.T142_30_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_30_20 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T142_30
  T2 := Q2.T142_30_2
  h1 := (4,3,2,0,4)
  h2 := (4,3,2,0,3)
  D := [[4, 3, 3, 4], [4, 3, 3, 1], [4, 3, 3, 3], [4, 3, 3, 0], [4, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_31_0 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T142_31
  T2 := Q2.T142_31_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_31_1 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T142_31
  T2 := Q2.T142_31_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_31_2 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T142_31
  T2 := Q2.T142_31_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_31_3 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T142_31
  T2 := Q2.T142_31_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_31_4 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T142_31
  T2 := Q2.T142_31_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_31_10 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T142_31
  T2 := Q2.T142_31_2
  h1 := (2,1,4,3,0)
  h2 := (2,1,4,3,3)
  D := [[2, 1, 1, 1], [2, 1, 1, 0], [2, 1, 1, 4], [2, 1, 1, 3], [2, 1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_31_20 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T142_31
  T2 := Q2.T142_31_2
  h1 := (4,2,3,3,1)
  h2 := (4,2,3,3,2)
  D := [[4, 2, 0, 3], [4, 2, 0, 1], [4, 2, 0, 4], [4, 2, 0, 2], [4, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_32_0 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T142_32
  T2 := Q2.T142_32_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_32_1 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T142_32
  T2 := Q2.T142_32_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_32_2 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T142_32
  T2 := Q2.T142_32_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_32_3 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T142_32
  T2 := Q2.T142_32_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_32_4 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T142_32
  T2 := Q2.T142_32_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_32_5 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T142_32
  T2 := Q2.T142_32_2
  h1 := (1,1,4,4,0)
  h2 := (1,1,4,4,3)
  D := [[1, 1, 3, 1], [1, 1, 3, 0], [1, 1, 3, 4], [1, 1, 3, 3], [1, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_32_10 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T142_32
  T2 := Q2.T142_32_2
  h1 := (2,2,3,4,3)
  h2 := (2,2,3,4,4)
  D := [[2, 2, 0, 0], [2, 2, 0, 3], [2, 2, 0, 1], [2, 2, 0, 4], [2, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_32_15 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T142_32
  T2 := Q2.T142_32_2
  h1 := (3,3,2,0,0)
  h2 := (3,3,2,0,4)
  D := [[3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_32_20 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T142_32
  T2 := Q2.T142_32_2
  h1 := (4,4,1,2,2)
  h2 := (4,4,1,2,4)
  D := [[4, 4, 1, 1], [4, 4, 1, 2], [4, 4, 1, 3], [4, 4, 1, 4], [4, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_53_0 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T142_53
  T2 := Q2.T142_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_53_1 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T142_53
  T2 := Q2.T142_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_53_2 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T142_53
  T2 := Q2.T142_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_53_3 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T142_53
  T2 := Q2.T142_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_53_4 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T142_53
  T2 := Q2.T142_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_53_5 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T142_53
  T2 := Q2.T142_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_53_10 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T142_53
  T2 := Q2.T142_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_53_15 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T142_53
  T2 := Q2.T142_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_53_20 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T142_53
  T2 := Q2.T142_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_54_0 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T142_54
  T2 := Q2.T142_54_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_54_1 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T142_54
  T2 := Q2.T142_54_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_54_2 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T142_54
  T2 := Q2.T142_54_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_54_3 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T142_54
  T2 := Q2.T142_54_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_54_4 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T142_54
  T2 := Q2.T142_54_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_54_5 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T142_54
  T2 := Q2.T142_54_2
  h1 := (1,0,0,4,4)
  h2 := (1,0,0,4,4)
  D := [[1, 0, 4, 0], [1, 0, 4, 0], [1, 0, 4, 0], [1, 0, 4, 0], [1, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_54_10 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T142_54
  T2 := Q2.T142_54_2
  h1 := (2,0,0,3,2)
  h2 := (2,0,0,3,2)
  D := [[2, 0, 3, 1], [2, 0, 3, 1], [2, 0, 3, 1], [2, 0, 3, 1], [2, 0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_54_15 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T142_54
  T2 := Q2.T142_54_2
  h1 := (3,0,0,2,4)
  h2 := (3,0,0,2,4)
  D := [[3, 0, 2, 3], [3, 0, 2, 3], [3, 0, 2, 3], [3, 0, 2, 3], [3, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_54_20 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T142_54
  T2 := Q2.T142_54_2
  h1 := (4,0,0,1,0)
  h2 := (4,0,0,1,0)
  D := [[4, 0, 1, 1], [4, 0, 1, 1], [4, 0, 1, 1], [4, 0, 1, 1], [4, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_90_0 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T142_90
  T2 := Q2.T142_90_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_90_1 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T142_90
  T2 := Q2.T142_90_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_90_2 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T142_90
  T2 := Q2.T142_90_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_90_3 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T142_90
  T2 := Q2.T142_90_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_90_4 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T142_90
  T2 := Q2.T142_90_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_90_5 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T142_90
  T2 := Q2.T142_90_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_90_10 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T142_90
  T2 := Q2.T142_90_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_90_15 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T142_90
  T2 := Q2.T142_90_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_90_20 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T142_90
  T2 := Q2.T142_90_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_91_0 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T142_91
  T2 := Q2.T142_91_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_91_1 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T142_91
  T2 := Q2.T142_91_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_91_2 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T142_91
  T2 := Q2.T142_91_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_91_3 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T142_91
  T2 := Q2.T142_91_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_91_4 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T142_91
  T2 := Q2.T142_91_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_91_20 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T142_91
  T2 := Q2.T142_91_2
  h1 := (4,1,4,0,3)
  h2 := (4,1,4,0,1)
  D := [[4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4], [4, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_92_0 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T142_92
  T2 := Q2.T142_92_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_92_1 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T142_92
  T2 := Q2.T142_92_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_92_2 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T142_92
  T2 := Q2.T142_92_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_92_3 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T142_92
  T2 := Q2.T142_92_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_92_4 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T142_92
  T2 := Q2.T142_92_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_93_0 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T142_93
  T2 := Q2.T142_93_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_142_93_1 : ColCert where
  rK := ⟨142, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T142_93
  T2 := Q2.T142_93_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
