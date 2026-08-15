/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C036

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 73: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_134_10_2 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T134_10
  T2 := Q2.T134_10_2
  h1 := (0,0,0,2,3)
  h2 := (0,0,0,2,3)
  D := [[0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_10_3 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T134_10
  T2 := Q2.T134_10_2
  h1 := (0,0,0,3,2)
  h2 := (0,0,0,3,2)
  D := [[0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_10_4 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T134_10
  T2 := Q2.T134_10_2
  h1 := (0,0,0,4,1)
  h2 := (0,0,0,4,1)
  D := [[0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_12_0 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T134_12
  T2 := Q2.T134_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_12_1 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T134_12
  T2 := Q2.T134_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_12_2 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T134_12
  T2 := Q2.T134_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_12_3 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T134_12
  T2 := Q2.T134_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_12_4 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T134_12
  T2 := Q2.T134_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_22_0 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T134_22
  T2 := Q2.T134_22_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_22_1 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T134_22
  T2 := Q2.T134_22_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_22_2 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T134_22
  T2 := Q2.T134_22_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_22_3 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T134_22
  T2 := Q2.T134_22_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_22_4 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T134_22
  T2 := Q2.T134_22_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_28_0 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T134_28
  T2 := Q2.T134_28_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_28_1 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T134_28
  T2 := Q2.T134_28_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_28_2 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T134_28
  T2 := Q2.T134_28_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_28_3 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T134_28
  T2 := Q2.T134_28_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_28_4 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T134_28
  T2 := Q2.T134_28_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_28_5 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T134_28
  T2 := Q2.T134_28_2
  h1 := (0,1,4,4,2)
  h2 := (0,1,4,4,0)
  D := [[0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1], [0, 1, 4, 0], [0, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_28_10 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T134_28
  T2 := Q2.T134_28_2
  h1 := (0,2,3,3,3)
  h2 := (0,2,3,3,4)
  D := [[0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2], [0, 2, 3, 0], [0, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_28_15 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T134_28
  T2 := Q2.T134_28_2
  h1 := (0,3,2,2,3)
  h2 := (0,3,2,2,2)
  D := [[0, 3, 2, 4], [0, 3, 2, 1], [0, 3, 2, 3], [0, 3, 2, 0], [0, 3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_28_20 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T134_28
  T2 := Q2.T134_28_2
  h1 := (0,4,1,1,2)
  h2 := (0,4,1,1,4)
  D := [[0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4], [0, 4, 1, 0], [0, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_37_0 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T134_37
  T2 := Q2.T134_37_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_37_1 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T134_37
  T2 := Q2.T134_37_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_37_2 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T134_37
  T2 := Q2.T134_37_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_37_3 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T134_37
  T2 := Q2.T134_37_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_37_4 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T134_37
  T2 := Q2.T134_37_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_40_0 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T134_40
  T2 := Q2.T134_40_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_40_1 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T134_40
  T2 := Q2.T134_40_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_40_2 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T134_40
  T2 := Q2.T134_40_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_40_3 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T134_40
  T2 := Q2.T134_40_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_40_4 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T134_40
  T2 := Q2.T134_40_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_40_5 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T134_40
  T2 := Q2.T134_40_2
  h1 := (1,2,1,2,4)
  h2 := (1,2,1,2,1)
  D := [[1, 2, 4, 3], [1, 2, 4, 1], [1, 2, 4, 4], [1, 2, 4, 2], [1, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_40_10 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T134_40
  T2 := Q2.T134_40_2
  h1 := (2,4,2,1,2)
  h2 := (2,4,2,1,1)
  D := [[2, 4, 1, 0], [2, 4, 1, 1], [2, 4, 1, 2], [2, 4, 1, 3], [2, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_44_0 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T134_44
  T2 := Q2.T134_44_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_44_1 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T134_44
  T2 := Q2.T134_44_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_44_2 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T134_44
  T2 := Q2.T134_44_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_44_3 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T134_44
  T2 := Q2.T134_44_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_44_4 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T134_44
  T2 := Q2.T134_44_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_44_10 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T134_44
  T2 := Q2.T134_44_2
  h1 := (2,3,3,0,0)
  h2 := (2,3,3,0,1)
  D := [[2, 3, 2, 3], [2, 3, 2, 0], [2, 3, 2, 2], [2, 3, 2, 4], [2, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_51_0 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T134_51
  T2 := Q2.T134_51_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_51_1 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T134_51
  T2 := Q2.T134_51_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_51_2 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T134_51
  T2 := Q2.T134_51_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_51_3 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T134_51
  T2 := Q2.T134_51_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_51_4 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T134_51
  T2 := Q2.T134_51_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_53_0 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T134_53
  T2 := Q2.T134_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_53_1 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T134_53
  T2 := Q2.T134_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_53_2 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T134_53
  T2 := Q2.T134_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_53_3 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T134_53
  T2 := Q2.T134_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_53_4 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T134_53
  T2 := Q2.T134_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_53_5 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T134_53
  T2 := Q2.T134_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_53_10 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T134_53
  T2 := Q2.T134_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_53_15 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T134_53
  T2 := Q2.T134_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_53_20 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T134_53
  T2 := Q2.T134_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_83_0 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T134_83
  T2 := Q2.T134_83_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_83_1 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T134_83
  T2 := Q2.T134_83_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_83_2 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T134_83
  T2 := Q2.T134_83_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_83_3 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T134_83
  T2 := Q2.T134_83_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_83_4 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T134_83
  T2 := Q2.T134_83_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_90_0 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T134_90
  T2 := Q2.T134_90_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
