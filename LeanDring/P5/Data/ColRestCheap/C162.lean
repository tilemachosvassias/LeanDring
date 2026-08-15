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
rest tier, chunk 161: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_71_19_1 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T71_19
  T2 := Q2.T71_19_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_19_2 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T71_19
  T2 := Q2.T71_19_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_19_3 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T71_19
  T2 := Q2.T71_19_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_19_4 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T71_19
  T2 := Q2.T71_19_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_19_5 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T71_19
  T2 := Q2.T71_19_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_19_10 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T71_19
  T2 := Q2.T71_19_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_19_15 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T71_19
  T2 := Q2.T71_19_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_19_20 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T71_19
  T2 := Q2.T71_19_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_31_0 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T71_31
  T2 := Q2.T71_31_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_31_1 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T71_31
  T2 := Q2.T71_31_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_31_2 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T71_31
  T2 := Q2.T71_31_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_31_3 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T71_31
  T2 := Q2.T71_31_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_31_4 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T71_31
  T2 := Q2.T71_31_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_31_5 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T71_31
  T2 := Q2.T71_31_2
  h1 := (1,3,2,0,4)
  h2 := (1,3,2,0,0)
  D := [[1, 2, 0], [1, 2, 4], [1, 2, 3], [1, 2, 2], [1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_31_10 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T71_31
  T2 := Q2.T71_31_2
  h1 := (2,1,4,3,0)
  h2 := (2,1,4,3,3)
  D := [[2, 4, 1], [2, 4, 4], [2, 4, 2], [2, 4, 0], [2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_31_15 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T71_31
  T2 := Q2.T71_31_2
  h1 := (3,4,1,4,4)
  h2 := (3,4,1,4,3)
  D := [[3, 1, 3], [3, 1, 0], [3, 1, 2], [3, 1, 4], [3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_31_20 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T71_31
  T2 := Q2.T71_31_2
  h1 := (4,2,3,3,1)
  h2 := (4,2,3,3,2)
  D := [[4, 3, 1], [4, 3, 2], [4, 3, 3], [4, 3, 4], [4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_36_0 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T71_36
  T2 := Q2.T71_36_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_36_1 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T71_36
  T2 := Q2.T71_36_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_36_2 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T71_36
  T2 := Q2.T71_36_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_36_3 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T71_36
  T2 := Q2.T71_36_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_36_4 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T71_36
  T2 := Q2.T71_36_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_36_5 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T71_36
  T2 := Q2.T71_36_2
  h1 := (1,3,1,0,1)
  h2 := (1,3,1,0,2)
  D := [[1, 1, 2], [1, 1, 1], [1, 1, 0], [1, 1, 4], [1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_36_10 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T71_36
  T2 := Q2.T71_36_2
  h1 := (2,1,2,3,1)
  h2 := (2,1,2,3,4)
  D := [[2, 2, 2], [2, 2, 0], [2, 2, 3], [2, 2, 1], [2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_36_15 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T71_36
  T2 := Q2.T71_36_2
  h1 := (3,4,3,4,1)
  h2 := (3,4,3,4,0)
  D := [[3, 3, 0], [3, 3, 2], [3, 3, 4], [3, 3, 1], [3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_36_20 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T71_36
  T2 := Q2.T71_36_2
  h1 := (4,2,4,3,1)
  h2 := (4,2,4,3,2)
  D := [[4, 4, 1], [4, 4, 2], [4, 4, 3], [4, 4, 4], [4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_41_0 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T71_41
  T2 := Q2.T71_41_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_41_1 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T71_41
  T2 := Q2.T71_41_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_41_2 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T71_41
  T2 := Q2.T71_41_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_41_3 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T71_41
  T2 := Q2.T71_41_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_41_4 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T71_41
  T2 := Q2.T71_41_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_41_5 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T71_41
  T2 := Q2.T71_41_2
  h1 := (1,3,4,0,0)
  h2 := (1,3,4,0,1)
  D := [[1, 4, 2], [1, 4, 1], [1, 4, 0], [1, 4, 4], [1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_41_10 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T71_41
  T2 := Q2.T71_41_2
  h1 := (2,1,3,3,3)
  h2 := (2,1,3,3,1)
  D := [[2, 3, 1], [2, 3, 4], [2, 3, 2], [2, 3, 0], [2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_41_15 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T71_41
  T2 := Q2.T71_41_2
  h1 := (3,4,2,4,0)
  h2 := (3,4,2,4,4)
  D := [[3, 2, 2], [3, 2, 4], [3, 2, 1], [3, 2, 3], [3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_41_20 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T71_41
  T2 := Q2.T71_41_2
  h1 := (4,2,1,3,1)
  h2 := (4,2,1,3,2)
  D := [[4, 1, 0], [4, 1, 1], [4, 1, 2], [4, 1, 3], [4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_46_0 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T71_46
  T2 := Q2.T71_46_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_46_1 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T71_46
  T2 := Q2.T71_46_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_46_2 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T71_46
  T2 := Q2.T71_46_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_46_3 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T71_46
  T2 := Q2.T71_46_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_46_4 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T71_46
  T2 := Q2.T71_46_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_46_5 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T71_46
  T2 := Q2.T71_46_2
  h1 := (1,3,3,0,2)
  h2 := (1,3,3,0,3)
  D := [[1, 3, 0], [1, 3, 4], [1, 3, 3], [1, 3, 2], [1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_46_10 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T71_46
  T2 := Q2.T71_46_2
  h1 := (2,1,1,3,4)
  h2 := (2,1,1,3,2)
  D := [[2, 1, 4], [2, 1, 2], [2, 1, 0], [2, 1, 3], [2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_46_15 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T71_46
  T2 := Q2.T71_46_2
  h1 := (3,4,4,4,2)
  h2 := (3,4,4,4,1)
  D := [[3, 4, 2], [3, 4, 4], [3, 4, 1], [3, 4, 3], [3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_46_20 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T71_46
  T2 := Q2.T71_46_2
  h1 := (4,2,2,3,1)
  h2 := (4,2,2,3,2)
  D := [[4, 2, 4], [4, 2, 0], [4, 2, 1], [4, 2, 2], [4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_51_0 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T71_51
  T2 := Q2.T71_51_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_51_1 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T71_51
  T2 := Q2.T71_51_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_51_2 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T71_51
  T2 := Q2.T71_51_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_51_3 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T71_51
  T2 := Q2.T71_51_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_51_4 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T71_51
  T2 := Q2.T71_51_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_51_5 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T71_51
  T2 := Q2.T71_51_2
  h1 := (1,3,0,0,3)
  h2 := (1,3,0,0,4)
  D := [[1, 0, 1], [1, 0, 0], [1, 0, 4], [1, 0, 3], [1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_51_10 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T71_51
  T2 := Q2.T71_51_2
  h1 := (2,1,0,3,2)
  h2 := (2,1,0,3,0)
  D := [[2, 0, 2], [2, 0, 0], [2, 0, 3], [2, 0, 1], [2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_51_15 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T71_51
  T2 := Q2.T71_51_2
  h1 := (3,4,0,4,3)
  h2 := (3,4,0,4,2)
  D := [[3, 0, 3], [3, 0, 0], [3, 0, 2], [3, 0, 4], [3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_51_20 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T71_51
  T2 := Q2.T71_51_2
  h1 := (4,2,0,3,1)
  h2 := (4,2,0,3,2)
  D := [[4, 0, 4], [4, 0, 0], [4, 0, 1], [4, 0, 2], [4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_71_0 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T71_71
  T2 := Q2.T71_71_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_71_1 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T71_71
  T2 := Q2.T71_71_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_71_2 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T71_71
  T2 := Q2.T71_71_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_71_3 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T71_71
  T2 := Q2.T71_71_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_71_4 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T71_71
  T2 := Q2.T71_71_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_71_5 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T71_71
  T2 := Q2.T71_71_2
  h1 := (1,3,0,0,1)
  h2 := (1,3,0,0,2)
  D := [[1, 0, 4], [1, 0, 3], [1, 0, 2], [1, 0, 1], [1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_71_6 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T71_71
  T2 := Q2.T71_71_2
  h1 := (1,3,1,4,1)
  h2 := (1,3,1,4,2)
  D := [[1, 1, 2], [1, 1, 1], [1, 1, 0], [1, 1, 4], [1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
