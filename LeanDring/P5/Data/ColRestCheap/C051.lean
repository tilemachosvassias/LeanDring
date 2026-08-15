/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C030

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 50: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_122_122_21 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨122, by decide⟩
  m := 5
  T1 := T122_122
  T2 := Q2.T122_122_2
  h1 := (4,1,0,1,0)
  h2 := (4,1,0,1,0)
  D := [[4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_122_22 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨122, by decide⟩
  m := 5
  T1 := T122_122
  T2 := Q2.T122_122_2
  h1 := (4,2,4,1,2)
  h2 := (4,2,4,1,0)
  D := [[4, 2, 2, 1], [4, 2, 2, 4], [4, 2, 2, 2], [4, 2, 2, 0], [4, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_122_23 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨122, by decide⟩
  m := 5
  T1 := T122_122
  T2 := Q2.T122_122_2
  h1 := (4,3,3,1,3)
  h2 := (4,3,3,1,4)
  D := [[4, 3, 3, 4], [4, 3, 3, 1], [4, 3, 3, 3], [4, 3, 3, 0], [4, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_122_24 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨122, by decide⟩
  m := 5
  T1 := T122_122
  T2 := Q2.T122_122_2
  h1 := (4,4,2,1,3)
  h2 := (4,4,2,1,2)
  D := [[4, 4, 4, 2], [4, 4, 4, 3], [4, 4, 4, 4], [4, 4, 4, 0], [4, 4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_0_0 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨0, by decide⟩
  m := 5
  T1 := T123_0
  T2 := Q2.T123_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_2_0 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T123_2
  T2 := Q2.T123_2_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_10_0 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T123_10
  T2 := Q2.T123_10_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_10_1 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T123_10
  T2 := Q2.T123_10_2
  h1 := (0,0,0,1,4)
  h2 := (0,0,0,1,4)
  D := [[0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_10_2 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T123_10
  T2 := Q2.T123_10_2
  h1 := (0,0,0,2,3)
  h2 := (0,0,0,2,3)
  D := [[0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_10_3 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T123_10
  T2 := Q2.T123_10_2
  h1 := (0,0,0,3,2)
  h2 := (0,0,0,3,2)
  D := [[0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_10_4 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T123_10
  T2 := Q2.T123_10_2
  h1 := (0,0,0,4,1)
  h2 := (0,0,0,4,1)
  D := [[0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_12_0 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T123_12
  T2 := Q2.T123_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_12_1 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T123_12
  T2 := Q2.T123_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_12_2 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T123_12
  T2 := Q2.T123_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_12_3 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T123_12
  T2 := Q2.T123_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_12_4 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T123_12
  T2 := Q2.T123_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_20_0 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T123_20
  T2 := Q2.T123_20_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_20_1 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T123_20
  T2 := Q2.T123_20_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_20_2 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T123_20
  T2 := Q2.T123_20_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_20_3 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T123_20
  T2 := Q2.T123_20_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_20_4 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T123_20
  T2 := Q2.T123_20_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_29_0 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T123_29
  T2 := Q2.T123_29_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_29_1 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T123_29
  T2 := Q2.T123_29_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_29_2 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T123_29
  T2 := Q2.T123_29_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_29_3 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T123_29
  T2 := Q2.T123_29_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_29_4 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T123_29
  T2 := Q2.T123_29_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_29_20 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T123_29
  T2 := Q2.T123_29_2
  h1 := (4,1,4,1,3)
  h2 := (4,1,4,1,1)
  D := [[4, 1, 0, 3], [4, 1, 0, 2], [4, 1, 0, 1], [4, 1, 0, 0], [4, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_37_0 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T123_37
  T2 := Q2.T123_37_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_37_1 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T123_37
  T2 := Q2.T123_37_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_37_2 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T123_37
  T2 := Q2.T123_37_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_37_3 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T123_37
  T2 := Q2.T123_37_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_37_4 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T123_37
  T2 := Q2.T123_37_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_38_0 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T123_38
  T2 := Q2.T123_38_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_38_1 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T123_38
  T2 := Q2.T123_38_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_38_2 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T123_38
  T2 := Q2.T123_38_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_38_3 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T123_38
  T2 := Q2.T123_38_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_38_4 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T123_38
  T2 := Q2.T123_38_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_46_0 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T123_46
  T2 := Q2.T123_46_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_46_1 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T123_46
  T2 := Q2.T123_46_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_46_2 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T123_46
  T2 := Q2.T123_46_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_46_3 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T123_46
  T2 := Q2.T123_46_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_46_4 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T123_46
  T2 := Q2.T123_46_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_46_5 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T123_46
  T2 := Q2.T123_46_2
  h1 := (1,3,3,0,2)
  h2 := (1,3,3,0,3)
  D := [[1, 3, 4, 4], [1, 3, 4, 1], [1, 3, 4, 3], [1, 3, 4, 0], [1, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_50_0 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T123_50
  T2 := Q2.T123_50_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_50_1 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T123_50
  T2 := Q2.T123_50_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_50_2 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T123_50
  T2 := Q2.T123_50_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_50_3 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T123_50
  T2 := Q2.T123_50_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_50_4 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T123_50
  T2 := Q2.T123_50_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_53_0 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T123_53
  T2 := Q2.T123_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_53_1 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T123_53
  T2 := Q2.T123_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_53_2 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T123_53
  T2 := Q2.T123_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_53_3 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T123_53
  T2 := Q2.T123_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_53_4 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T123_53
  T2 := Q2.T123_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_53_5 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T123_53
  T2 := Q2.T123_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_53_10 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T123_53
  T2 := Q2.T123_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_53_15 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T123_53
  T2 := Q2.T123_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_53_20 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T123_53
  T2 := Q2.T123_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_81_0 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T123_81
  T2 := Q2.T123_81_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_81_1 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T123_81
  T2 := Q2.T123_81_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_123_81_2 : ColCert where
  rK := ⟨123, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T123_81
  T2 := Q2.T123_81_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
