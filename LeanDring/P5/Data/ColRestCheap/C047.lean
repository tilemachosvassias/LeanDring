/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C029

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 46: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_121_10_4 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T121_10
  T2 := Q2.T121_10_2
  h1 := (0,0,0,4,1)
  h2 := (0,0,0,4,1)
  D := [[0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_12_0 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T121_12
  T2 := Q2.T121_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_12_1 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T121_12
  T2 := Q2.T121_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_12_2 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T121_12
  T2 := Q2.T121_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_12_3 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T121_12
  T2 := Q2.T121_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_12_4 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T121_12
  T2 := Q2.T121_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_20_0 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T121_20
  T2 := Q2.T121_20_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_20_1 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T121_20
  T2 := Q2.T121_20_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_20_2 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T121_20
  T2 := Q2.T121_20_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_20_3 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T121_20
  T2 := Q2.T121_20_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_20_4 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T121_20
  T2 := Q2.T121_20_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_20_5 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T121_20
  T2 := Q2.T121_20_2
  h1 := (1,0,4,1,1)
  h2 := (1,0,4,1,1)
  D := [[1, 0, 1, 0], [1, 0, 1, 0], [1, 0, 1, 0], [1, 0, 1, 0], [1, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_20_10 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T121_20
  T2 := Q2.T121_20_2
  h1 := (2,0,3,2,3)
  h2 := (2,0,3,2,3)
  D := [[2, 0, 2, 4], [2, 0, 2, 4], [2, 0, 2, 4], [2, 0, 2, 4], [2, 0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_20_15 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T121_20
  T2 := Q2.T121_20_2
  h1 := (3,0,2,3,1)
  h2 := (3,0,2,3,1)
  D := [[3, 0, 3, 2], [3, 0, 3, 2], [3, 0, 3, 2], [3, 0, 3, 2], [3, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_20_20 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T121_20
  T2 := Q2.T121_20_2
  h1 := (4,0,1,4,0)
  h2 := (4,0,1,4,0)
  D := [[4, 0, 4, 4], [4, 0, 4, 4], [4, 0, 4, 4], [4, 0, 4, 4], [4, 0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_32_0 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T121_32
  T2 := Q2.T121_32_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_32_1 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T121_32
  T2 := Q2.T121_32_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_32_2 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T121_32
  T2 := Q2.T121_32_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_32_3 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T121_32
  T2 := Q2.T121_32_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_32_4 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T121_32
  T2 := Q2.T121_32_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_35_0 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T121_35
  T2 := Q2.T121_35_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_35_1 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T121_35
  T2 := Q2.T121_35_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_35_2 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T121_35
  T2 := Q2.T121_35_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_35_3 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T121_35
  T2 := Q2.T121_35_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_35_4 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T121_35
  T2 := Q2.T121_35_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_41_0 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T121_41
  T2 := Q2.T121_41_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_41_1 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T121_41
  T2 := Q2.T121_41_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_41_2 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T121_41
  T2 := Q2.T121_41_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_41_3 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T121_41
  T2 := Q2.T121_41_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_41_4 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T121_41
  T2 := Q2.T121_41_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_44_0 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T121_44
  T2 := Q2.T121_44_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_44_1 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T121_44
  T2 := Q2.T121_44_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_44_2 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T121_44
  T2 := Q2.T121_44_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_44_3 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T121_44
  T2 := Q2.T121_44_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_44_4 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T121_44
  T2 := Q2.T121_44_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_44_5 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T121_44
  T2 := Q2.T121_44_2
  h1 := (1,4,4,3,0)
  h2 := (1,4,4,3,0)
  D := [[1, 4, 4, 0], [1, 4, 4, 1], [1, 4, 4, 2], [1, 4, 4, 3], [1, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_48_0 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T121_48
  T2 := Q2.T121_48_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_48_1 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T121_48
  T2 := Q2.T121_48_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_48_2 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T121_48
  T2 := Q2.T121_48_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_48_3 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T121_48
  T2 := Q2.T121_48_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_48_4 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T121_48
  T2 := Q2.T121_48_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_53_0 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T121_53
  T2 := Q2.T121_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_53_1 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T121_53
  T2 := Q2.T121_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_53_2 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T121_53
  T2 := Q2.T121_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_53_3 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T121_53
  T2 := Q2.T121_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_53_4 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T121_53
  T2 := Q2.T121_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_53_5 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T121_53
  T2 := Q2.T121_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_53_10 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T121_53
  T2 := Q2.T121_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_53_15 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T121_53
  T2 := Q2.T121_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_53_20 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T121_53
  T2 := Q2.T121_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_81_0 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T121_81
  T2 := Q2.T121_81_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_81_1 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T121_81
  T2 := Q2.T121_81_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_81_2 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T121_81
  T2 := Q2.T121_81_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_81_3 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T121_81
  T2 := Q2.T121_81_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_81_4 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T121_81
  T2 := Q2.T121_81_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_81_5 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T121_81
  T2 := Q2.T121_81_2
  h1 := (1,0,4,0,0)
  h2 := (1,0,4,0,0)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_81_10 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T121_81
  T2 := Q2.T121_81_2
  h1 := (2,0,3,0,0)
  h2 := (2,0,3,0,0)
  D := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_81_15 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T121_81
  T2 := Q2.T121_81_2
  h1 := (3,0,2,0,0)
  h2 := (3,0,2,0,0)
  D := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_81_20 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T121_81
  T2 := Q2.T121_81_2
  h1 := (4,0,1,0,0)
  h2 := (4,0,1,0,0)
  D := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_121_94_0 : ColCert where
  rK := ⟨121, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T121_94
  T2 := Q2.T121_94_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
