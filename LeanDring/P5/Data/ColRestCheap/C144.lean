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
rest tier, chunk 143: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_58_43_3 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T58_43
  T2 := Q2.T58_43_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_43_4 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T58_43
  T2 := Q2.T58_43_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_48_0 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T58_48
  T2 := Q2.T58_48_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_48_1 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T58_48
  T2 := Q2.T58_48_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_48_2 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T58_48
  T2 := Q2.T58_48_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_48_3 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T58_48
  T2 := Q2.T58_48_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_48_4 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T58_48
  T2 := Q2.T58_48_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_58_0 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T58_58
  T2 := Q2.T58_58_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_58_1 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T58_58
  T2 := Q2.T58_58_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_58_2 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T58_58
  T2 := Q2.T58_58_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_58_3 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T58_58
  T2 := Q2.T58_58_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_58_4 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T58_58
  T2 := Q2.T58_58_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_58_5 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T58_58
  T2 := Q2.T58_58_2
  h1 := (0,1,0,4,2)
  h2 := (0,1,0,4,3)
  D := [[1, 0, 0], [1, 0, 0], [1, 0, 0], [1, 0, 0], [1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_58_6 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T58_58
  T2 := Q2.T58_58_2
  h1 := (0,1,1,1,2)
  h2 := (0,1,1,1,3)
  D := [[1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_58_7 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T58_58
  T2 := Q2.T58_58_2
  h1 := (0,1,2,3,2)
  h2 := (0,1,2,3,3)
  D := [[1, 2, 3], [1, 2, 3], [1, 2, 3], [1, 2, 3], [1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_58_8 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T58_58
  T2 := Q2.T58_58_2
  h1 := (0,1,3,0,2)
  h2 := (0,1,3,0,3)
  D := [[1, 3, 2], [1, 3, 2], [1, 3, 2], [1, 3, 2], [1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_58_9 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T58_58
  T2 := Q2.T58_58_2
  h1 := (0,1,4,2,2)
  h2 := (0,1,4,2,3)
  D := [[1, 4, 1], [1, 4, 1], [1, 4, 1], [1, 4, 1], [1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_58_10 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T58_58
  T2 := Q2.T58_58_2
  h1 := (0,2,0,3,4)
  h2 := (0,2,0,3,1)
  D := [[2, 0, 0], [2, 0, 0], [2, 0, 0], [2, 0, 0], [2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_58_11 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T58_58
  T2 := Q2.T58_58_2
  h1 := (0,2,1,0,4)
  h2 := (0,2,1,0,1)
  D := [[2, 1, 3], [2, 1, 3], [2, 1, 3], [2, 1, 3], [2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_58_12 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T58_58
  T2 := Q2.T58_58_2
  h1 := (0,2,2,2,4)
  h2 := (0,2,2,2,1)
  D := [[2, 2, 1], [2, 2, 1], [2, 2, 1], [2, 2, 1], [2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_58_13 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T58_58
  T2 := Q2.T58_58_2
  h1 := (0,2,3,4,4)
  h2 := (0,2,3,4,1)
  D := [[2, 3, 4], [2, 3, 4], [2, 3, 4], [2, 3, 4], [2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_58_14 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T58_58
  T2 := Q2.T58_58_2
  h1 := (0,2,4,1,4)
  h2 := (0,2,4,1,1)
  D := [[2, 4, 2], [2, 4, 2], [2, 4, 2], [2, 4, 2], [2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_58_15 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T58_58
  T2 := Q2.T58_58_2
  h1 := (0,3,0,2,1)
  h2 := (0,3,0,2,4)
  D := [[3, 0, 0], [3, 0, 0], [3, 0, 0], [3, 0, 0], [3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_58_16 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T58_58
  T2 := Q2.T58_58_2
  h1 := (0,3,1,4,1)
  h2 := (0,3,1,4,4)
  D := [[3, 1, 2], [3, 1, 2], [3, 1, 2], [3, 1, 2], [3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_58_17 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T58_58
  T2 := Q2.T58_58_2
  h1 := (0,3,2,1,1)
  h2 := (0,3,2,1,4)
  D := [[3, 2, 4], [3, 2, 4], [3, 2, 4], [3, 2, 4], [3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_58_18 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T58_58
  T2 := Q2.T58_58_2
  h1 := (0,3,3,3,1)
  h2 := (0,3,3,3,4)
  D := [[3, 3, 1], [3, 3, 1], [3, 3, 1], [3, 3, 1], [3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_58_19 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T58_58
  T2 := Q2.T58_58_2
  h1 := (0,3,4,0,1)
  h2 := (0,3,4,0,4)
  D := [[3, 4, 3], [3, 4, 3], [3, 4, 3], [3, 4, 3], [3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_58_20 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T58_58
  T2 := Q2.T58_58_2
  h1 := (0,4,0,1,3)
  h2 := (0,4,0,1,2)
  D := [[4, 0, 0], [4, 0, 0], [4, 0, 0], [4, 0, 0], [4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_58_21 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T58_58
  T2 := Q2.T58_58_2
  h1 := (0,4,1,3,3)
  h2 := (0,4,1,3,2)
  D := [[4, 1, 1], [4, 1, 1], [4, 1, 1], [4, 1, 1], [4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_58_22 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T58_58
  T2 := Q2.T58_58_2
  h1 := (0,4,2,0,3)
  h2 := (0,4,2,0,2)
  D := [[4, 2, 2], [4, 2, 2], [4, 2, 2], [4, 2, 2], [4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_58_23 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T58_58
  T2 := Q2.T58_58_2
  h1 := (0,4,3,2,3)
  h2 := (0,4,3,2,2)
  D := [[4, 3, 3], [4, 3, 3], [4, 3, 3], [4, 3, 3], [4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_58_58_24 : ColCert where
  rK := ⟨58, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T58_58
  T2 := Q2.T58_58_2
  h1 := (0,4,4,4,3)
  h2 := (0,4,4,4,2)
  D := [[4, 4, 4], [4, 4, 4], [4, 4, 4], [4, 4, 4], [4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_59_0_0 : ColCert where
  rK := ⟨59, by decide⟩
  rH := ⟨0, by decide⟩
  m := 25
  T1 := T59_0
  T2 := Q2.T59_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_59_8_0 : ColCert where
  rK := ⟨59, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T59_8
  T2 := Q2.T59_8_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_59_8_1 : ColCert where
  rK := ⟨59, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T59_8
  T2 := Q2.T59_8_2
  h1 := (0,0,1,1,4)
  h2 := (0,0,1,1,4)
  D := [[0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_59_8_2 : ColCert where
  rK := ⟨59, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T59_8
  T2 := Q2.T59_8_2
  h1 := (0,0,2,2,3)
  h2 := (0,0,2,2,3)
  D := [[0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_59_8_3 : ColCert where
  rK := ⟨59, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T59_8
  T2 := Q2.T59_8_2
  h1 := (0,0,3,3,2)
  h2 := (0,0,3,3,2)
  D := [[0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_59_8_4 : ColCert where
  rK := ⟨59, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T59_8
  T2 := Q2.T59_8_2
  h1 := (0,0,4,4,1)
  h2 := (0,0,4,4,1)
  D := [[0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_59_12_0 : ColCert where
  rK := ⟨59, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T59_12
  T2 := Q2.T59_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_59_12_1 : ColCert where
  rK := ⟨59, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T59_12
  T2 := Q2.T59_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_59_12_2 : ColCert where
  rK := ⟨59, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T59_12
  T2 := Q2.T59_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_59_12_3 : ColCert where
  rK := ⟨59, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T59_12
  T2 := Q2.T59_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_59_12_4 : ColCert where
  rK := ⟨59, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T59_12
  T2 := Q2.T59_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_59_26_0 : ColCert where
  rK := ⟨59, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T59_26
  T2 := Q2.T59_26_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_59_26_1 : ColCert where
  rK := ⟨59, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T59_26
  T2 := Q2.T59_26_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_59_26_2 : ColCert where
  rK := ⟨59, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T59_26
  T2 := Q2.T59_26_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_59_26_3 : ColCert where
  rK := ⟨59, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T59_26
  T2 := Q2.T59_26_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_59_26_4 : ColCert where
  rK := ⟨59, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T59_26
  T2 := Q2.T59_26_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_59_26_5 : ColCert where
  rK := ⟨59, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T59_26
  T2 := Q2.T59_26_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_59_26_10 : ColCert where
  rK := ⟨59, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T59_26
  T2 := Q2.T59_26_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_59_26_15 : ColCert where
  rK := ⟨59, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T59_26
  T2 := Q2.T59_26_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_59_26_20 : ColCert where
  rK := ⟨59, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T59_26
  T2 := Q2.T59_26_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_59_28_0 : ColCert where
  rK := ⟨59, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T59_28
  T2 := Q2.T59_28_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_59_28_1 : ColCert where
  rK := ⟨59, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T59_28
  T2 := Q2.T59_28_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_59_28_2 : ColCert where
  rK := ⟨59, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T59_28
  T2 := Q2.T59_28_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_59_28_3 : ColCert where
  rK := ⟨59, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T59_28
  T2 := Q2.T59_28_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_59_28_4 : ColCert where
  rK := ⟨59, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T59_28
  T2 := Q2.T59_28_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_59_33_0 : ColCert where
  rK := ⟨59, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T59_33
  T2 := Q2.T59_33_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_59_33_1 : ColCert where
  rK := ⟨59, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T59_33
  T2 := Q2.T59_33_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_59_33_2 : ColCert where
  rK := ⟨59, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T59_33
  T2 := Q2.T59_33_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
