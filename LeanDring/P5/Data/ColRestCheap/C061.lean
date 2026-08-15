/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C032
import LeanDring.P5.Data.EntryK.C033

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 60: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_127_127_5 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨127, by decide⟩
  m := 5
  T1 := T127_127
  T2 := Q2.T127_127_2
  h1 := (1,0,2,4,4)
  h2 := (1,0,2,4,0)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_127_6 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨127, by decide⟩
  m := 5
  T1 := T127_127
  T2 := Q2.T127_127_2
  h1 := (1,1,4,4,0)
  h2 := (1,1,4,4,2)
  D := [[1, 1, 4, 4], [1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1], [1, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_127_7 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨127, by decide⟩
  m := 5
  T1 := T127_127
  T2 := Q2.T127_127_2
  h1 := (1,2,1,4,3)
  h2 := (1,2,1,4,1)
  D := [[1, 2, 3, 3], [1, 2, 3, 1], [1, 2, 3, 4], [1, 2, 3, 2], [1, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_127_8 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨127, by decide⟩
  m := 5
  T1 := T127_127
  T2 := Q2.T127_127_2
  h1 := (1,3,3,4,3)
  h2 := (1,3,3,4,2)
  D := [[1, 3, 2, 2], [1, 3, 2, 4], [1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_127_9 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨127, by decide⟩
  m := 5
  T1 := T127_127
  T2 := Q2.T127_127_2
  h1 := (1,4,0,4,0)
  h2 := (1,4,0,4,0)
  D := [[1, 4, 1, 1], [1, 4, 1, 2], [1, 4, 1, 3], [1, 4, 1, 4], [1, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_127_10 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨127, by decide⟩
  m := 5
  T1 := T127_127
  T2 := Q2.T127_127_2
  h1 := (2,0,4,3,2)
  h2 := (2,0,4,3,4)
  D := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_127_11 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨127, by decide⟩
  m := 5
  T1 := T127_127
  T2 := Q2.T127_127_2
  h1 := (2,1,1,3,0)
  h2 := (2,1,1,3,3)
  D := [[2, 1, 3, 3], [2, 1, 3, 2], [2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_127_12 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨127, by decide⟩
  m := 5
  T1 := T127_127
  T2 := Q2.T127_127_2
  h1 := (2,2,3,3,0)
  h2 := (2,2,3,3,4)
  D := [[2, 2, 1, 1], [2, 2, 1, 4], [2, 2, 1, 2], [2, 2, 1, 0], [2, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_127_13 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨127, by decide⟩
  m := 5
  T1 := T127_127
  T2 := Q2.T127_127_2
  h1 := (2,3,0,3,2)
  h2 := (2,3,0,3,2)
  D := [[2, 3, 4, 4], [2, 3, 4, 1], [2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_127_14 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨127, by decide⟩
  m := 5
  T1 := T127_127
  T2 := Q2.T127_127_2
  h1 := (2,4,2,3,1)
  h2 := (2,4,2,3,2)
  D := [[2, 4, 2, 2], [2, 4, 2, 3], [2, 4, 2, 4], [2, 4, 2, 0], [2, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_127_15 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨127, by decide⟩
  m := 5
  T1 := T127_127
  T2 := Q2.T127_127_2
  h1 := (3,0,1,2,4)
  h2 := (3,0,1,2,2)
  D := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_127_16 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨127, by decide⟩
  m := 5
  T1 := T127_127
  T2 := Q2.T127_127_2
  h1 := (3,1,3,2,4)
  h2 := (3,1,3,2,3)
  D := [[3, 1, 2, 3], [3, 1, 2, 2], [3, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_127_17 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨127, by decide⟩
  m := 5
  T1 := T127_127
  T2 := Q2.T127_127_2
  h1 := (3,2,0,2,1)
  h2 := (3,2,0,2,1)
  D := [[3, 2, 4, 1], [3, 2, 4, 4], [3, 2, 4, 2], [3, 2, 4, 0], [3, 2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_127_18 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨127, by decide⟩
  m := 5
  T1 := T127_127
  T2 := Q2.T127_127_2
  h1 := (3,3,2,2,0)
  h2 := (3,3,2,2,1)
  D := [[3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_127_19 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨127, by decide⟩
  m := 5
  T1 := T127_127
  T2 := Q2.T127_127_2
  h1 := (3,4,4,2,1)
  h2 := (3,4,4,2,3)
  D := [[3, 4, 3, 2], [3, 4, 3, 3], [3, 4, 3, 4], [3, 4, 3, 0], [3, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_127_20 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨127, by decide⟩
  m := 5
  T1 := T127_127
  T2 := Q2.T127_127_2
  h1 := (4,0,3,1,0)
  h2 := (4,0,3,1,4)
  D := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_127_21 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨127, by decide⟩
  m := 5
  T1 := T127_127
  T2 := Q2.T127_127_2
  h1 := (4,1,0,1,2)
  h2 := (4,1,0,1,2)
  D := [[4, 1, 1, 4], [4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_127_22 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨127, by decide⟩
  m := 5
  T1 := T127_127
  T2 := Q2.T127_127_2
  h1 := (4,2,2,1,1)
  h2 := (4,2,2,1,2)
  D := [[4, 2, 2, 3], [4, 2, 2, 1], [4, 2, 2, 4], [4, 2, 2, 2], [4, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_127_23 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨127, by decide⟩
  m := 5
  T1 := T127_127
  T2 := Q2.T127_127_2
  h1 := (4,3,4,1,2)
  h2 := (4,3,4,1,4)
  D := [[4, 3, 3, 2], [4, 3, 3, 4], [4, 3, 3, 1], [4, 3, 3, 3], [4, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_127_24 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨127, by decide⟩
  m := 5
  T1 := T127_127
  T2 := Q2.T127_127_2
  h1 := (4,4,1,1,0)
  h2 := (4,4,1,1,3)
  D := [[4, 4, 4, 1], [4, 4, 4, 2], [4, 4, 4, 3], [4, 4, 4, 4], [4, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_0_0 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨0, by decide⟩
  m := 5
  T1 := T128_0
  T2 := Q2.T128_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_3_0 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T128_3
  T2 := Q2.T128_3_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_10_0 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T128_10
  T2 := Q2.T128_10_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_10_1 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T128_10
  T2 := Q2.T128_10_2
  h1 := (0,0,0,1,4)
  h2 := (0,0,0,1,4)
  D := [[0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_10_2 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T128_10
  T2 := Q2.T128_10_2
  h1 := (0,0,0,2,3)
  h2 := (0,0,0,2,3)
  D := [[0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_10_3 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T128_10
  T2 := Q2.T128_10_2
  h1 := (0,0,0,3,2)
  h2 := (0,0,0,3,2)
  D := [[0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_10_4 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T128_10
  T2 := Q2.T128_10_2
  h1 := (0,0,0,4,1)
  h2 := (0,0,0,4,1)
  D := [[0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_12_0 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T128_12
  T2 := Q2.T128_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_12_1 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T128_12
  T2 := Q2.T128_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_12_2 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T128_12
  T2 := Q2.T128_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_12_3 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T128_12
  T2 := Q2.T128_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_12_4 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T128_12
  T2 := Q2.T128_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_21_0 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T128_21
  T2 := Q2.T128_21_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_21_1 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T128_21
  T2 := Q2.T128_21_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_21_2 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T128_21
  T2 := Q2.T128_21_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_21_3 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T128_21
  T2 := Q2.T128_21_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_21_4 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T128_21
  T2 := Q2.T128_21_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_28_0 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T128_28
  T2 := Q2.T128_28_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_28_1 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T128_28
  T2 := Q2.T128_28_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_28_2 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T128_28
  T2 := Q2.T128_28_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_28_3 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T128_28
  T2 := Q2.T128_28_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_28_4 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T128_28
  T2 := Q2.T128_28_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_28_5 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T128_28
  T2 := Q2.T128_28_2
  h1 := (0,1,4,4,2)
  h2 := (0,1,4,4,0)
  D := [[0, 1, 4, 4], [0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1], [0, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_28_10 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T128_28
  T2 := Q2.T128_28_2
  h1 := (0,2,3,3,3)
  h2 := (0,2,3,3,4)
  D := [[0, 2, 3, 3], [0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2], [0, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_28_15 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T128_28
  T2 := Q2.T128_28_2
  h1 := (0,3,2,2,3)
  h2 := (0,3,2,2,2)
  D := [[0, 3, 2, 2], [0, 3, 2, 4], [0, 3, 2, 1], [0, 3, 2, 3], [0, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_28_20 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T128_28
  T2 := Q2.T128_28_2
  h1 := (0,4,1,1,2)
  h2 := (0,4,1,1,4)
  D := [[0, 4, 1, 1], [0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4], [0, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_34_0 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T128_34
  T2 := Q2.T128_34_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_34_1 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T128_34
  T2 := Q2.T128_34_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_34_2 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T128_34
  T2 := Q2.T128_34_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_34_3 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T128_34
  T2 := Q2.T128_34_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_34_4 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T128_34
  T2 := Q2.T128_34_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_41_0 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T128_41
  T2 := Q2.T128_41_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_41_1 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T128_41
  T2 := Q2.T128_41_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_41_2 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T128_41
  T2 := Q2.T128_41_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_41_3 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T128_41
  T2 := Q2.T128_41_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_41_4 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T128_41
  T2 := Q2.T128_41_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_41_15 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T128_41
  T2 := Q2.T128_41_2
  h1 := (3,4,2,4,0)
  h2 := (3,4,2,4,4)
  D := [[3, 4, 3, 1], [3, 4, 3, 2], [3, 4, 3, 3], [3, 4, 3, 4], [3, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_47_0 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T128_47
  T2 := Q2.T128_47_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_47_1 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T128_47
  T2 := Q2.T128_47_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_47_2 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T128_47
  T2 := Q2.T128_47_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
