/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C015

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 146: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_60_60_13 : ColCert where
  rK := ⟨60, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T60_60
  T2 := Q2.T60_60_2
  h1 := (2,3,3,0,2)
  h2 := (2,3,3,0,3)
  D := [[2, 3, 3], [2, 3, 1], [2, 3, 4], [2, 3, 2], [2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_60_60_14 : ColCert where
  rK := ⟨60, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T60_60
  T2 := Q2.T60_60_2
  h1 := (2,3,4,0,2)
  h2 := (2,3,4,0,3)
  D := [[2, 4, 0], [2, 4, 3], [2, 4, 1], [2, 4, 4], [2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_60_60_15 : ColCert where
  rK := ⟨60, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T60_60
  T2 := Q2.T60_60_2
  h1 := (3,2,0,1,2)
  h2 := (3,2,0,1,4)
  D := [[3, 0, 3], [3, 0, 0], [3, 0, 2], [3, 0, 4], [3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_60_60_16 : ColCert where
  rK := ⟨60, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T60_60
  T2 := Q2.T60_60_2
  h1 := (3,2,1,1,2)
  h2 := (3,2,1,1,4)
  D := [[3, 1, 1], [3, 1, 3], [3, 1, 0], [3, 1, 2], [3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_60_60_17 : ColCert where
  rK := ⟨60, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T60_60
  T2 := Q2.T60_60_2
  h1 := (3,2,2,1,2)
  h2 := (3,2,2,1,4)
  D := [[3, 2, 4], [3, 2, 1], [3, 2, 3], [3, 2, 0], [3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_60_60_18 : ColCert where
  rK := ⟨60, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T60_60
  T2 := Q2.T60_60_2
  h1 := (3,2,3,1,2)
  h2 := (3,2,3,1,4)
  D := [[3, 3, 2], [3, 3, 4], [3, 3, 1], [3, 3, 3], [3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_60_60_19 : ColCert where
  rK := ⟨60, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T60_60
  T2 := Q2.T60_60_2
  h1 := (3,2,4,1,2)
  h2 := (3,2,4,1,4)
  D := [[3, 4, 0], [3, 4, 2], [3, 4, 4], [3, 4, 1], [3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_60_60_20 : ColCert where
  rK := ⟨60, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T60_60
  T2 := Q2.T60_60_2
  h1 := (4,1,0,1,3)
  h2 := (4,1,0,1,1)
  D := [[4, 0, 4], [4, 0, 0], [4, 0, 1], [4, 0, 2], [4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_60_60_21 : ColCert where
  rK := ⟨60, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T60_60
  T2 := Q2.T60_60_2
  h1 := (4,1,1,1,3)
  h2 := (4,1,1,1,1)
  D := [[4, 1, 3], [4, 1, 4], [4, 1, 0], [4, 1, 1], [4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_60_60_22 : ColCert where
  rK := ⟨60, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T60_60
  T2 := Q2.T60_60_2
  h1 := (4,1,2,1,3)
  h2 := (4,1,2,1,1)
  D := [[4, 2, 2], [4, 2, 3], [4, 2, 4], [4, 2, 0], [4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_60_60_23 : ColCert where
  rK := ⟨60, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T60_60
  T2 := Q2.T60_60_2
  h1 := (4,1,3,1,3)
  h2 := (4,1,3,1,1)
  D := [[4, 3, 1], [4, 3, 2], [4, 3, 3], [4, 3, 4], [4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_60_60_24 : ColCert where
  rK := ⟨60, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T60_60
  T2 := Q2.T60_60_2
  h1 := (4,1,4,1,3)
  h2 := (4,1,4,1,1)
  D := [[4, 4, 0], [4, 4, 1], [4, 4, 2], [4, 4, 3], [4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_0_0 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨0, by decide⟩
  m := 25
  T1 := T61_0
  T2 := Q2.T61_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_1_0 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨1, by decide⟩
  m := 25
  T1 := T61_1
  T2 := Q2.T61_1_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_1_1 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨1, by decide⟩
  m := 25
  T1 := T61_1
  T2 := Q2.T61_1_2
  h1 := (0,0,1,4,4)
  h2 := (0,0,1,4,4)
  D := [[0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_1_2 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨1, by decide⟩
  m := 25
  T1 := T61_1
  T2 := Q2.T61_1_2
  h1 := (0,0,2,3,3)
  h2 := (0,0,2,3,3)
  D := [[0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_1_3 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨1, by decide⟩
  m := 25
  T1 := T61_1
  T2 := Q2.T61_1_2
  h1 := (0,0,3,2,2)
  h2 := (0,0,3,2,2)
  D := [[0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_1_4 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨1, by decide⟩
  m := 25
  T1 := T61_1
  T2 := Q2.T61_1_2
  h1 := (0,0,4,1,1)
  h2 := (0,0,4,1,1)
  D := [[0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_12_0 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T61_12
  T2 := Q2.T61_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_12_1 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T61_12
  T2 := Q2.T61_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_12_2 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T61_12
  T2 := Q2.T61_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_12_3 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T61_12
  T2 := Q2.T61_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_12_4 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T61_12
  T2 := Q2.T61_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_19_0 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T61_19
  T2 := Q2.T61_19_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_19_1 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T61_19
  T2 := Q2.T61_19_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_19_2 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T61_19
  T2 := Q2.T61_19_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_19_3 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T61_19
  T2 := Q2.T61_19_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_19_4 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T61_19
  T2 := Q2.T61_19_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_19_5 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T61_19
  T2 := Q2.T61_19_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_19_10 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T61_19
  T2 := Q2.T61_19_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_19_15 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T61_19
  T2 := Q2.T61_19_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_19_20 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T61_19
  T2 := Q2.T61_19_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_29_0 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T61_29
  T2 := Q2.T61_29_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_29_1 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T61_29
  T2 := Q2.T61_29_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_29_2 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T61_29
  T2 := Q2.T61_29_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_29_3 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T61_29
  T2 := Q2.T61_29_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_29_4 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T61_29
  T2 := Q2.T61_29_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_29_5 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T61_29
  T2 := Q2.T61_29_2
  h1 := (1,4,1,3,3)
  h2 := (1,4,1,3,3)
  D := [[1, 1, 1], [1, 1, 0], [1, 1, 4], [1, 1, 3], [1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_29_10 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T61_29
  T2 := Q2.T61_29_2
  h1 := (2,3,2,0,4)
  h2 := (2,3,2,0,0)
  D := [[2, 2, 4], [2, 2, 2], [2, 2, 0], [2, 2, 3], [2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_29_15 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T61_29
  T2 := Q2.T61_29_2
  h1 := (3,2,3,1,1)
  h2 := (3,2,3,1,3)
  D := [[3, 3, 4], [3, 3, 1], [3, 3, 3], [3, 3, 0], [3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_29_20 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T61_29
  T2 := Q2.T61_29_2
  h1 := (4,1,4,1,3)
  h2 := (4,1,4,1,1)
  D := [[4, 4, 1], [4, 4, 2], [4, 4, 3], [4, 4, 4], [4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_34_0 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T61_34
  T2 := Q2.T61_34_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_34_1 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T61_34
  T2 := Q2.T61_34_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_34_2 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T61_34
  T2 := Q2.T61_34_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_34_3 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T61_34
  T2 := Q2.T61_34_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_34_4 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T61_34
  T2 := Q2.T61_34_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_34_5 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T61_34
  T2 := Q2.T61_34_2
  h1 := (1,4,3,3,1)
  h2 := (1,4,3,3,1)
  D := [[1, 3, 4], [1, 3, 3], [1, 3, 2], [1, 3, 1], [1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_34_10 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T61_34
  T2 := Q2.T61_34_2
  h1 := (2,3,1,0,3)
  h2 := (2,3,1,0,4)
  D := [[2, 1, 4], [2, 1, 2], [2, 1, 0], [2, 1, 3], [2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_34_15 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T61_34
  T2 := Q2.T61_34_2
  h1 := (3,2,4,1,4)
  h2 := (3,2,4,1,1)
  D := [[3, 4, 0], [3, 4, 2], [3, 4, 4], [3, 4, 1], [3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_34_20 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T61_34
  T2 := Q2.T61_34_2
  h1 := (4,1,2,1,3)
  h2 := (4,1,2,1,1)
  D := [[4, 2, 2], [4, 2, 3], [4, 2, 4], [4, 2, 0], [4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_39_0 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T61_39
  T2 := Q2.T61_39_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_39_1 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T61_39
  T2 := Q2.T61_39_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_39_2 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T61_39
  T2 := Q2.T61_39_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_39_3 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T61_39
  T2 := Q2.T61_39_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_39_4 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T61_39
  T2 := Q2.T61_39_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_39_5 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T61_39
  T2 := Q2.T61_39_2
  h1 := (1,4,2,3,2)
  h2 := (1,4,2,3,2)
  D := [[1, 2, 4], [1, 2, 3], [1, 2, 2], [1, 2, 1], [1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_39_10 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T61_39
  T2 := Q2.T61_39_2
  h1 := (2,3,4,0,1)
  h2 := (2,3,4,0,2)
  D := [[2, 4, 2], [2, 4, 0], [2, 4, 3], [2, 4, 1], [2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_39_15 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T61_39
  T2 := Q2.T61_39_2
  h1 := (3,2,1,1,0)
  h2 := (3,2,1,1,2)
  D := [[3, 1, 4], [3, 1, 1], [3, 1, 3], [3, 1, 0], [3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_39_20 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T61_39
  T2 := Q2.T61_39_2
  h1 := (4,1,3,1,3)
  h2 := (4,1,3,1,1)
  D := [[4, 3, 0], [4, 3, 1], [4, 3, 2], [4, 3, 3], [4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_61_44_0 : ColCert where
  rK := ⟨61, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T61_44
  T2 := Q2.T61_44_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
