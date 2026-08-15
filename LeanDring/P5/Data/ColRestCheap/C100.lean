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
rest tier, chunk 99: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_143_33_2 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T143_33
  T2 := Q2.T143_33_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_33_3 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T143_33
  T2 := Q2.T143_33_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_33_4 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T143_33
  T2 := Q2.T143_33_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_34_0 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T143_34
  T2 := Q2.T143_34_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_34_1 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T143_34
  T2 := Q2.T143_34_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_34_2 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T143_34
  T2 := Q2.T143_34_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_34_3 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T143_34
  T2 := Q2.T143_34_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_34_4 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T143_34
  T2 := Q2.T143_34_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_34_15 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T143_34
  T2 := Q2.T143_34_2
  h1 := (3,2,4,1,4)
  h2 := (3,2,4,1,1)
  D := [[3, 2, 0, 4], [3, 2, 0, 2], [3, 2, 0, 0], [3, 2, 0, 3], [3, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_35_0 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T143_35
  T2 := Q2.T143_35_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_35_1 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T143_35
  T2 := Q2.T143_35_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_35_2 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T143_35
  T2 := Q2.T143_35_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_35_3 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T143_35
  T2 := Q2.T143_35_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_35_4 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T143_35
  T2 := Q2.T143_35_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_35_5 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T143_35
  T2 := Q2.T143_35_2
  h1 := (1,2,4,2,0)
  h2 := (1,2,4,2,2)
  D := [[1, 2, 0, 1], [1, 2, 0, 4], [1, 2, 0, 2], [1, 2, 0, 0], [1, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_35_10 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T143_35
  T2 := Q2.T143_35_2
  h1 := (2,4,3,1,0)
  h2 := (2,4,3,1,4)
  D := [[2, 4, 3, 4], [2, 4, 3, 0], [2, 4, 3, 1], [2, 4, 3, 2], [2, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_36_0 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T143_36
  T2 := Q2.T143_36_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_36_1 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T143_36
  T2 := Q2.T143_36_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_36_2 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T143_36
  T2 := Q2.T143_36_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_36_3 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T143_36
  T2 := Q2.T143_36_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_36_4 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T143_36
  T2 := Q2.T143_36_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_36_15 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T143_36
  T2 := Q2.T143_36_2
  h1 := (3,4,3,4,1)
  h2 := (3,4,3,4,0)
  D := [[3, 4, 2, 2], [3, 4, 2, 3], [3, 4, 2, 4], [3, 4, 2, 0], [3, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_37_0 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T143_37
  T2 := Q2.T143_37_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_37_1 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T143_37
  T2 := Q2.T143_37_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_37_2 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T143_37
  T2 := Q2.T143_37_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_37_3 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T143_37
  T2 := Q2.T143_37_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_37_4 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T143_37
  T2 := Q2.T143_37_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_53_0 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T143_53
  T2 := Q2.T143_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_53_1 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T143_53
  T2 := Q2.T143_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_53_2 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T143_53
  T2 := Q2.T143_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_53_3 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T143_53
  T2 := Q2.T143_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_53_4 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T143_53
  T2 := Q2.T143_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_53_5 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T143_53
  T2 := Q2.T143_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_53_10 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T143_53
  T2 := Q2.T143_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_53_15 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T143_53
  T2 := Q2.T143_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_53_20 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T143_53
  T2 := Q2.T143_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_54_0 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T143_54
  T2 := Q2.T143_54_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_54_1 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T143_54
  T2 := Q2.T143_54_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_54_2 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T143_54
  T2 := Q2.T143_54_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_54_3 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T143_54
  T2 := Q2.T143_54_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_54_4 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T143_54
  T2 := Q2.T143_54_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_54_5 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T143_54
  T2 := Q2.T143_54_2
  h1 := (1,0,0,4,4)
  h2 := (1,0,0,4,4)
  D := [[1, 0, 4, 0], [1, 0, 4, 0], [1, 0, 4, 0], [1, 0, 4, 0], [1, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_54_10 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T143_54
  T2 := Q2.T143_54_2
  h1 := (2,0,0,3,2)
  h2 := (2,0,0,3,2)
  D := [[2, 0, 3, 1], [2, 0, 3, 1], [2, 0, 3, 1], [2, 0, 3, 1], [2, 0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_54_15 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T143_54
  T2 := Q2.T143_54_2
  h1 := (3,0,0,2,4)
  h2 := (3,0,0,2,4)
  D := [[3, 0, 2, 3], [3, 0, 2, 3], [3, 0, 2, 3], [3, 0, 2, 3], [3, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_54_20 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T143_54
  T2 := Q2.T143_54_2
  h1 := (4,0,0,1,0)
  h2 := (4,0,0,1,0)
  D := [[4, 0, 1, 1], [4, 0, 1, 1], [4, 0, 1, 1], [4, 0, 1, 1], [4, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_95_0 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T143_95
  T2 := Q2.T143_95_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_95_1 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T143_95
  T2 := Q2.T143_95_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_95_2 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T143_95
  T2 := Q2.T143_95_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_95_3 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T143_95
  T2 := Q2.T143_95_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_95_4 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T143_95
  T2 := Q2.T143_95_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_95_5 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T143_95
  T2 := Q2.T143_95_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_95_10 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T143_95
  T2 := Q2.T143_95_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_95_15 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T143_95
  T2 := Q2.T143_95_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_95_20 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T143_95
  T2 := Q2.T143_95_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_96_0 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T143_96
  T2 := Q2.T143_96_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_96_1 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T143_96
  T2 := Q2.T143_96_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_96_2 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T143_96
  T2 := Q2.T143_96_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_96_3 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T143_96
  T2 := Q2.T143_96_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_96_4 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T143_96
  T2 := Q2.T143_96_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_96_15 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T143_96
  T2 := Q2.T143_96_2
  h1 := (3,2,4,4,0)
  h2 := (3,2,4,4,2)
  D := [[3, 2, 3, 1], [3, 2, 3, 4], [3, 2, 3, 2], [3, 2, 3, 0], [3, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
