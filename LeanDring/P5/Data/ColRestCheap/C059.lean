/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C032

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 58: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_126_110_100 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T126_110
  T2 := Q2.T126_110_2
  h1 := (0,4,0,0,0)
  h2 := (0,4,0,0,0)
  D := [[0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_126_0 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨126, by decide⟩
  m := 5
  T1 := T126_126
  T2 := Q2.T126_126_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_126_1 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨126, by decide⟩
  m := 5
  T1 := T126_126
  T2 := Q2.T126_126_2
  h1 := (0,1,0,0,0)
  h2 := (0,1,0,0,0)
  D := [[0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_126_2 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨126, by decide⟩
  m := 5
  T1 := T126_126
  T2 := Q2.T126_126_2
  h1 := (0,2,0,0,0)
  h2 := (0,2,0,0,0)
  D := [[0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_126_3 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨126, by decide⟩
  m := 5
  T1 := T126_126
  T2 := Q2.T126_126_2
  h1 := (0,3,0,0,0)
  h2 := (0,3,0,0,0)
  D := [[0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_126_4 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨126, by decide⟩
  m := 5
  T1 := T126_126
  T2 := Q2.T126_126_2
  h1 := (0,4,0,0,0)
  h2 := (0,4,0,0,0)
  D := [[0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_126_5 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨126, by decide⟩
  m := 5
  T1 := T126_126
  T2 := Q2.T126_126_2
  h1 := (1,0,2,0,0)
  h2 := (1,0,2,0,0)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_126_6 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨126, by decide⟩
  m := 5
  T1 := T126_126
  T2 := Q2.T126_126_2
  h1 := (1,1,2,0,2)
  h2 := (1,1,2,0,2)
  D := [[1, 1, 4, 1], [1, 1, 4, 0], [1, 1, 4, 4], [1, 1, 4, 3], [1, 1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_126_7 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨126, by decide⟩
  m := 5
  T1 := T126_126
  T2 := Q2.T126_126_2
  h1 := (1,2,2,0,4)
  h2 := (1,2,2,0,4)
  D := [[1, 2, 3, 2], [1, 2, 3, 0], [1, 2, 3, 3], [1, 2, 3, 1], [1, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_126_8 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨126, by decide⟩
  m := 5
  T1 := T126_126
  T2 := Q2.T126_126_2
  h1 := (1,3,2,0,1)
  h2 := (1,3,2,0,1)
  D := [[1, 3, 2, 3], [1, 3, 2, 0], [1, 3, 2, 2], [1, 3, 2, 4], [1, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_126_9 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨126, by decide⟩
  m := 5
  T1 := T126_126
  T2 := Q2.T126_126_2
  h1 := (1,4,2,0,3)
  h2 := (1,4,2,0,3)
  D := [[1, 4, 1, 4], [1, 4, 1, 0], [1, 4, 1, 1], [1, 4, 1, 2], [1, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_126_10 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨126, by decide⟩
  m := 5
  T1 := T126_126
  T2 := Q2.T126_126_2
  h1 := (2,0,4,0,0)
  h2 := (2,0,4,0,0)
  D := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_126_11 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨126, by decide⟩
  m := 5
  T1 := T126_126
  T2 := Q2.T126_126_2
  h1 := (2,1,4,0,4)
  h2 := (2,1,4,0,4)
  D := [[2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3], [2, 1, 3, 2], [2, 1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_126_12 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨126, by decide⟩
  m := 5
  T1 := T126_126
  T2 := Q2.T126_126_2
  h1 := (2,2,4,0,3)
  h2 := (2,2,4,0,3)
  D := [[2, 2, 1, 0], [2, 2, 1, 3], [2, 2, 1, 1], [2, 2, 1, 4], [2, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_126_13 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨126, by decide⟩
  m := 5
  T1 := T126_126
  T2 := Q2.T126_126_2
  h1 := (2,3,4,0,2)
  h2 := (2,3,4,0,2)
  D := [[2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1], [2, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_126_14 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨126, by decide⟩
  m := 5
  T1 := T126_126
  T2 := Q2.T126_126_2
  h1 := (2,4,4,0,1)
  h2 := (2,4,4,0,1)
  D := [[2, 4, 2, 0], [2, 4, 2, 1], [2, 4, 2, 2], [2, 4, 2, 3], [2, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_126_15 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨126, by decide⟩
  m := 5
  T1 := T126_126
  T2 := Q2.T126_126_2
  h1 := (3,0,1,0,0)
  h2 := (3,0,1,0,0)
  D := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_126_16 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨126, by decide⟩
  m := 5
  T1 := T126_126
  T2 := Q2.T126_126_2
  h1 := (3,1,1,0,1)
  h2 := (3,1,1,0,1)
  D := [[3, 1, 2, 0], [3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2], [3, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_126_17 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨126, by decide⟩
  m := 5
  T1 := T126_126
  T2 := Q2.T126_126_2
  h1 := (3,2,1,0,2)
  h2 := (3,2,1,0,2)
  D := [[3, 2, 4, 0], [3, 2, 4, 3], [3, 2, 4, 1], [3, 2, 4, 4], [3, 2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_126_18 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨126, by decide⟩
  m := 5
  T1 := T126_126
  T2 := Q2.T126_126_2
  h1 := (3,3,1,0,3)
  h2 := (3,3,1,0,3)
  D := [[3, 3, 1, 0], [3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_126_19 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨126, by decide⟩
  m := 5
  T1 := T126_126
  T2 := Q2.T126_126_2
  h1 := (3,4,1,0,4)
  h2 := (3,4,1,0,4)
  D := [[3, 4, 3, 0], [3, 4, 3, 1], [3, 4, 3, 2], [3, 4, 3, 3], [3, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_126_20 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨126, by decide⟩
  m := 5
  T1 := T126_126
  T2 := Q2.T126_126_2
  h1 := (4,0,3,0,0)
  h2 := (4,0,3,0,0)
  D := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_126_21 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨126, by decide⟩
  m := 5
  T1 := T126_126
  T2 := Q2.T126_126_2
  h1 := (4,1,3,0,3)
  h2 := (4,1,3,0,3)
  D := [[4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4], [4, 1, 1, 3], [4, 1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_126_22 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨126, by decide⟩
  m := 5
  T1 := T126_126
  T2 := Q2.T126_126_2
  h1 := (4,2,3,0,1)
  h2 := (4,2,3,0,1)
  D := [[4, 2, 2, 2], [4, 2, 2, 0], [4, 2, 2, 3], [4, 2, 2, 1], [4, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_126_23 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨126, by decide⟩
  m := 5
  T1 := T126_126
  T2 := Q2.T126_126_2
  h1 := (4,3,3,0,4)
  h2 := (4,3,3,0,4)
  D := [[4, 3, 3, 3], [4, 3, 3, 0], [4, 3, 3, 2], [4, 3, 3, 4], [4, 3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_126_24 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨126, by decide⟩
  m := 5
  T1 := T126_126
  T2 := Q2.T126_126_2
  h1 := (4,4,3,0,2)
  h2 := (4,4,3,0,2)
  D := [[4, 4, 4, 4], [4, 4, 4, 0], [4, 4, 4, 1], [4, 4, 4, 2], [4, 4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_0_0 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨0, by decide⟩
  m := 5
  T1 := T127_0
  T2 := Q2.T127_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_3_0 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T127_3
  T2 := Q2.T127_3_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_10_0 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T127_10
  T2 := Q2.T127_10_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_10_1 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T127_10
  T2 := Q2.T127_10_2
  h1 := (0,0,0,1,4)
  h2 := (0,0,0,1,4)
  D := [[0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_10_2 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T127_10
  T2 := Q2.T127_10_2
  h1 := (0,0,0,2,3)
  h2 := (0,0,0,2,3)
  D := [[0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_10_3 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T127_10
  T2 := Q2.T127_10_2
  h1 := (0,0,0,3,2)
  h2 := (0,0,0,3,2)
  D := [[0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_10_4 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T127_10
  T2 := Q2.T127_10_2
  h1 := (0,0,0,4,1)
  h2 := (0,0,0,4,1)
  D := [[0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_12_0 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T127_12
  T2 := Q2.T127_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_12_1 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T127_12
  T2 := Q2.T127_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_12_2 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T127_12
  T2 := Q2.T127_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_12_3 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T127_12
  T2 := Q2.T127_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_12_4 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T127_12
  T2 := Q2.T127_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_21_0 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T127_21
  T2 := Q2.T127_21_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_21_1 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T127_21
  T2 := Q2.T127_21_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_21_2 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T127_21
  T2 := Q2.T127_21_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_21_3 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T127_21
  T2 := Q2.T127_21_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_21_4 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T127_21
  T2 := Q2.T127_21_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_32_0 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T127_32
  T2 := Q2.T127_32_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_32_1 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T127_32
  T2 := Q2.T127_32_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_32_2 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T127_32
  T2 := Q2.T127_32_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_32_3 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T127_32
  T2 := Q2.T127_32_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_32_4 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T127_32
  T2 := Q2.T127_32_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_33_0 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T127_33
  T2 := Q2.T127_33_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_33_1 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T127_33
  T2 := Q2.T127_33_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_33_2 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T127_33
  T2 := Q2.T127_33_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_33_3 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T127_33
  T2 := Q2.T127_33_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_33_4 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T127_33
  T2 := Q2.T127_33_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_40_0 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T127_40
  T2 := Q2.T127_40_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_40_1 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T127_40
  T2 := Q2.T127_40_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_40_2 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T127_40
  T2 := Q2.T127_40_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_40_3 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T127_40
  T2 := Q2.T127_40_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_40_4 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T127_40
  T2 := Q2.T127_40_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_46_0 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T127_46
  T2 := Q2.T127_46_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_46_1 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T127_46
  T2 := Q2.T127_46_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
