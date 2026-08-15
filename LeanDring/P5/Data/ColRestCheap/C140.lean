/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C014

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 139: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_55_43_1 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T55_43
  T2 := Q2.T55_43_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_43_2 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T55_43
  T2 := Q2.T55_43_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_43_3 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T55_43
  T2 := Q2.T55_43_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_43_4 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T55_43
  T2 := Q2.T55_43_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_43_5 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T55_43
  T2 := Q2.T55_43_2
  h1 := (0,1,1,4,4)
  h2 := (0,1,1,4,2)
  D := [[1, 1, 0], [1, 1, 0], [1, 1, 0], [1, 1, 0], [1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_43_10 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T55_43
  T2 := Q2.T55_43_2
  h1 := (0,2,2,3,4)
  h2 := (0,2,2,3,0)
  D := [[2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_43_15 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T55_43
  T2 := Q2.T55_43_2
  h1 := (0,3,3,2,0)
  h2 := (0,3,3,2,4)
  D := [[3, 3, 2], [3, 3, 2], [3, 3, 2], [3, 3, 2], [3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_43_20 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T55_43
  T2 := Q2.T55_43_2
  h1 := (0,4,4,1,2)
  h2 := (0,4,4,1,4)
  D := [[4, 4, 4], [4, 4, 4], [4, 4, 4], [4, 4, 4], [4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_48_0 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T55_48
  T2 := Q2.T55_48_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_48_1 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T55_48
  T2 := Q2.T55_48_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_48_2 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T55_48
  T2 := Q2.T55_48_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_48_3 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T55_48
  T2 := Q2.T55_48_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_48_4 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T55_48
  T2 := Q2.T55_48_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_48_5 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T55_48
  T2 := Q2.T55_48_2
  h1 := (0,1,0,4,3)
  h2 := (0,1,0,4,1)
  D := [[1, 0, 0], [1, 0, 0], [1, 0, 0], [1, 0, 0], [1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_48_10 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T55_48
  T2 := Q2.T55_48_2
  h1 := (0,2,0,3,1)
  h2 := (0,2,0,3,2)
  D := [[2, 0, 0], [2, 0, 0], [2, 0, 0], [2, 0, 0], [2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_48_15 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T55_48
  T2 := Q2.T55_48_2
  h1 := (0,3,0,2,4)
  h2 := (0,3,0,2,3)
  D := [[3, 0, 0], [3, 0, 0], [3, 0, 0], [3, 0, 0], [3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_48_20 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T55_48
  T2 := Q2.T55_48_2
  h1 := (0,4,0,1,2)
  h2 := (0,4,0,1,4)
  D := [[4, 0, 0], [4, 0, 0], [4, 0, 0], [4, 0, 0], [4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_55_0 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T55_55
  T2 := Q2.T55_55_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_55_1 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T55_55
  T2 := Q2.T55_55_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_55_2 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T55_55
  T2 := Q2.T55_55_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_55_3 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T55_55
  T2 := Q2.T55_55_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_55_4 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T55_55
  T2 := Q2.T55_55_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_55_5 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T55_55
  T2 := Q2.T55_55_2
  h1 := (0,1,0,4,3)
  h2 := (0,1,0,4,1)
  D := [[1, 0, 0], [1, 0, 0], [1, 0, 0], [1, 0, 0], [1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_55_6 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T55_55
  T2 := Q2.T55_55_2
  h1 := (0,1,1,4,3)
  h2 := (0,1,1,4,1)
  D := [[1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_55_7 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T55_55
  T2 := Q2.T55_55_2
  h1 := (0,1,2,4,3)
  h2 := (0,1,2,4,1)
  D := [[1, 2, 3], [1, 2, 3], [1, 2, 3], [1, 2, 3], [1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_55_8 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T55_55
  T2 := Q2.T55_55_2
  h1 := (0,1,3,4,3)
  h2 := (0,1,3,4,1)
  D := [[1, 3, 2], [1, 3, 2], [1, 3, 2], [1, 3, 2], [1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_55_9 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T55_55
  T2 := Q2.T55_55_2
  h1 := (0,1,4,4,3)
  h2 := (0,1,4,4,1)
  D := [[1, 4, 1], [1, 4, 1], [1, 4, 1], [1, 4, 1], [1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_55_10 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T55_55
  T2 := Q2.T55_55_2
  h1 := (0,2,0,3,1)
  h2 := (0,2,0,3,2)
  D := [[2, 0, 0], [2, 0, 0], [2, 0, 0], [2, 0, 0], [2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_55_11 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T55_55
  T2 := Q2.T55_55_2
  h1 := (0,2,1,3,1)
  h2 := (0,2,1,3,2)
  D := [[2, 1, 3], [2, 1, 3], [2, 1, 3], [2, 1, 3], [2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_55_12 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T55_55
  T2 := Q2.T55_55_2
  h1 := (0,2,2,3,1)
  h2 := (0,2,2,3,2)
  D := [[2, 2, 1], [2, 2, 1], [2, 2, 1], [2, 2, 1], [2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_55_13 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T55_55
  T2 := Q2.T55_55_2
  h1 := (0,2,3,3,1)
  h2 := (0,2,3,3,2)
  D := [[2, 3, 4], [2, 3, 4], [2, 3, 4], [2, 3, 4], [2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_55_14 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T55_55
  T2 := Q2.T55_55_2
  h1 := (0,2,4,3,1)
  h2 := (0,2,4,3,2)
  D := [[2, 4, 2], [2, 4, 2], [2, 4, 2], [2, 4, 2], [2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_55_15 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T55_55
  T2 := Q2.T55_55_2
  h1 := (0,3,0,2,4)
  h2 := (0,3,0,2,3)
  D := [[3, 0, 0], [3, 0, 0], [3, 0, 0], [3, 0, 0], [3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_55_16 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T55_55
  T2 := Q2.T55_55_2
  h1 := (0,3,1,2,4)
  h2 := (0,3,1,2,3)
  D := [[3, 1, 2], [3, 1, 2], [3, 1, 2], [3, 1, 2], [3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_55_17 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T55_55
  T2 := Q2.T55_55_2
  h1 := (0,3,2,2,4)
  h2 := (0,3,2,2,3)
  D := [[3, 2, 4], [3, 2, 4], [3, 2, 4], [3, 2, 4], [3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_55_18 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T55_55
  T2 := Q2.T55_55_2
  h1 := (0,3,3,2,4)
  h2 := (0,3,3,2,3)
  D := [[3, 3, 1], [3, 3, 1], [3, 3, 1], [3, 3, 1], [3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_55_19 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T55_55
  T2 := Q2.T55_55_2
  h1 := (0,3,4,2,4)
  h2 := (0,3,4,2,3)
  D := [[3, 4, 3], [3, 4, 3], [3, 4, 3], [3, 4, 3], [3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_55_20 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T55_55
  T2 := Q2.T55_55_2
  h1 := (0,4,0,1,2)
  h2 := (0,4,0,1,4)
  D := [[4, 0, 0], [4, 0, 0], [4, 0, 0], [4, 0, 0], [4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_55_21 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T55_55
  T2 := Q2.T55_55_2
  h1 := (0,4,1,1,2)
  h2 := (0,4,1,1,4)
  D := [[4, 1, 1], [4, 1, 1], [4, 1, 1], [4, 1, 1], [4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_55_22 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T55_55
  T2 := Q2.T55_55_2
  h1 := (0,4,2,1,2)
  h2 := (0,4,2,1,4)
  D := [[4, 2, 2], [4, 2, 2], [4, 2, 2], [4, 2, 2], [4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_55_23 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T55_55
  T2 := Q2.T55_55_2
  h1 := (0,4,3,1,2)
  h2 := (0,4,3,1,4)
  D := [[4, 3, 3], [4, 3, 3], [4, 3, 3], [4, 3, 3], [4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_55_55_24 : ColCert where
  rK := ⟨55, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T55_55
  T2 := Q2.T55_55_2
  h1 := (0,4,4,1,2)
  h2 := (0,4,4,1,4)
  D := [[4, 4, 4], [4, 4, 4], [4, 4, 4], [4, 4, 4], [4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_0_0 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨0, by decide⟩
  m := 25
  T1 := T56_0
  T2 := Q2.T56_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_1_0 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨1, by decide⟩
  m := 25
  T1 := T56_1
  T2 := Q2.T56_1_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_1_1 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨1, by decide⟩
  m := 25
  T1 := T56_1
  T2 := Q2.T56_1_2
  h1 := (0,0,1,4,4)
  h2 := (0,0,1,4,4)
  D := [[0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_1_2 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨1, by decide⟩
  m := 25
  T1 := T56_1
  T2 := Q2.T56_1_2
  h1 := (0,0,2,3,3)
  h2 := (0,0,2,3,3)
  D := [[0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_1_3 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨1, by decide⟩
  m := 25
  T1 := T56_1
  T2 := Q2.T56_1_2
  h1 := (0,0,3,2,2)
  h2 := (0,0,3,2,2)
  D := [[0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_1_4 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨1, by decide⟩
  m := 25
  T1 := T56_1
  T2 := Q2.T56_1_2
  h1 := (0,0,4,1,1)
  h2 := (0,0,4,1,1)
  D := [[0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_12_0 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T56_12
  T2 := Q2.T56_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_12_1 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T56_12
  T2 := Q2.T56_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_12_2 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T56_12
  T2 := Q2.T56_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_12_3 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T56_12
  T2 := Q2.T56_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_12_4 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T56_12
  T2 := Q2.T56_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_19_0 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T56_19
  T2 := Q2.T56_19_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_19_1 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T56_19
  T2 := Q2.T56_19_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_19_2 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T56_19
  T2 := Q2.T56_19_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_19_3 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T56_19
  T2 := Q2.T56_19_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_19_4 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T56_19
  T2 := Q2.T56_19_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_19_5 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T56_19
  T2 := Q2.T56_19_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_19_10 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T56_19
  T2 := Q2.T56_19_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
