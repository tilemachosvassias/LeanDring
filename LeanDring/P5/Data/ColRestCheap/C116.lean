/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C044

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 115: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_147_57_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨57, by decide⟩
  m := 1
  T1 := T147_57
  T2 := Q2.T147_57_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 0, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_57_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨57, by decide⟩
  m := 1
  T1 := T147_57
  T2 := Q2.T147_57_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 0, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_57_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨57, by decide⟩
  m := 1
  T1 := T147_57
  T2 := Q2.T147_57_2
  h1 := (0,0,4,2,0)
  h2 := (0,0,4,2,0)
  D := [[0, 0, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_58_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨58, by decide⟩
  m := 1
  T1 := T147_58
  T2 := Q2.T147_58_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_58_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨58, by decide⟩
  m := 1
  T1 := T147_58
  T2 := Q2.T147_58_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 0, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_58_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨58, by decide⟩
  m := 1
  T1 := T147_58
  T2 := Q2.T147_58_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 0, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_58_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨58, by decide⟩
  m := 1
  T1 := T147_58
  T2 := Q2.T147_58_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 0, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_58_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨58, by decide⟩
  m := 1
  T1 := T147_58
  T2 := Q2.T147_58_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 0, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_59_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨59, by decide⟩
  m := 1
  T1 := T147_59
  T2 := Q2.T147_59_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_59_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨59, by decide⟩
  m := 1
  T1 := T147_59
  T2 := Q2.T147_59_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 0, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_59_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨59, by decide⟩
  m := 1
  T1 := T147_59
  T2 := Q2.T147_59_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 0, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_59_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨59, by decide⟩
  m := 1
  T1 := T147_59
  T2 := Q2.T147_59_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 0, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_59_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨59, by decide⟩
  m := 1
  T1 := T147_59
  T2 := Q2.T147_59_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 0, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_59_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨59, by decide⟩
  m := 1
  T1 := T147_59
  T2 := Q2.T147_59_2
  h1 := (0,1,0,4,0)
  h2 := (0,1,0,4,0)
  D := [[0, 1, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_59_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨59, by decide⟩
  m := 1
  T1 := T147_59
  T2 := Q2.T147_59_2
  h1 := (0,1,1,0,0)
  h2 := (0,1,1,0,0)
  D := [[0, 1, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_59_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨59, by decide⟩
  m := 1
  T1 := T147_59
  T2 := Q2.T147_59_2
  h1 := (0,1,2,1,0)
  h2 := (0,1,2,1,0)
  D := [[0, 1, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_59_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨59, by decide⟩
  m := 1
  T1 := T147_59
  T2 := Q2.T147_59_2
  h1 := (0,1,3,2,0)
  h2 := (0,1,3,2,0)
  D := [[0, 1, 3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_59_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨59, by decide⟩
  m := 1
  T1 := T147_59
  T2 := Q2.T147_59_2
  h1 := (0,1,4,3,0)
  h2 := (0,1,4,3,0)
  D := [[0, 1, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_59_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨59, by decide⟩
  m := 1
  T1 := T147_59
  T2 := Q2.T147_59_2
  h1 := (0,2,0,3,0)
  h2 := (0,2,0,3,0)
  D := [[0, 2, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_59_11 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨59, by decide⟩
  m := 1
  T1 := T147_59
  T2 := Q2.T147_59_2
  h1 := (0,2,1,4,0)
  h2 := (0,2,1,4,0)
  D := [[0, 2, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_59_12 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨59, by decide⟩
  m := 1
  T1 := T147_59
  T2 := Q2.T147_59_2
  h1 := (0,2,2,0,0)
  h2 := (0,2,2,0,0)
  D := [[0, 2, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_59_13 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨59, by decide⟩
  m := 1
  T1 := T147_59
  T2 := Q2.T147_59_2
  h1 := (0,2,3,1,0)
  h2 := (0,2,3,1,0)
  D := [[0, 2, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_59_14 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨59, by decide⟩
  m := 1
  T1 := T147_59
  T2 := Q2.T147_59_2
  h1 := (0,2,4,2,0)
  h2 := (0,2,4,2,0)
  D := [[0, 2, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_59_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨59, by decide⟩
  m := 1
  T1 := T147_59
  T2 := Q2.T147_59_2
  h1 := (0,3,0,2,0)
  h2 := (0,3,0,2,0)
  D := [[0, 3, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_59_16 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨59, by decide⟩
  m := 1
  T1 := T147_59
  T2 := Q2.T147_59_2
  h1 := (0,3,1,3,0)
  h2 := (0,3,1,3,0)
  D := [[0, 3, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_59_17 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨59, by decide⟩
  m := 1
  T1 := T147_59
  T2 := Q2.T147_59_2
  h1 := (0,3,2,4,0)
  h2 := (0,3,2,4,0)
  D := [[0, 3, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_59_18 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨59, by decide⟩
  m := 1
  T1 := T147_59
  T2 := Q2.T147_59_2
  h1 := (0,3,3,0,0)
  h2 := (0,3,3,0,0)
  D := [[0, 3, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_59_19 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨59, by decide⟩
  m := 1
  T1 := T147_59
  T2 := Q2.T147_59_2
  h1 := (0,3,4,1,0)
  h2 := (0,3,4,1,0)
  D := [[0, 3, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_59_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨59, by decide⟩
  m := 1
  T1 := T147_59
  T2 := Q2.T147_59_2
  h1 := (0,4,0,1,0)
  h2 := (0,4,0,1,0)
  D := [[0, 4, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_59_21 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨59, by decide⟩
  m := 1
  T1 := T147_59
  T2 := Q2.T147_59_2
  h1 := (0,4,1,2,0)
  h2 := (0,4,1,2,0)
  D := [[0, 4, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_59_22 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨59, by decide⟩
  m := 1
  T1 := T147_59
  T2 := Q2.T147_59_2
  h1 := (0,4,2,3,0)
  h2 := (0,4,2,3,0)
  D := [[0, 4, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_59_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨59, by decide⟩
  m := 1
  T1 := T147_59
  T2 := Q2.T147_59_2
  h1 := (0,4,3,4,0)
  h2 := (0,4,3,4,0)
  D := [[0, 4, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_59_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨59, by decide⟩
  m := 1
  T1 := T147_59
  T2 := Q2.T147_59_2
  h1 := (0,4,4,0,0)
  h2 := (0,4,4,0,0)
  D := [[0, 4, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_60_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨60, by decide⟩
  m := 1
  T1 := T147_60
  T2 := Q2.T147_60_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_60_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨60, by decide⟩
  m := 1
  T1 := T147_60
  T2 := Q2.T147_60_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_60_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨60, by decide⟩
  m := 1
  T1 := T147_60
  T2 := Q2.T147_60_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_60_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨60, by decide⟩
  m := 1
  T1 := T147_60
  T2 := Q2.T147_60_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_60_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨60, by decide⟩
  m := 1
  T1 := T147_60
  T2 := Q2.T147_60_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_60_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨60, by decide⟩
  m := 1
  T1 := T147_60
  T2 := Q2.T147_60_2
  h1 := (1,4,0,3,4)
  h2 := (1,4,0,3,4)
  D := [[1, 4, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_60_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨60, by decide⟩
  m := 1
  T1 := T147_60
  T2 := Q2.T147_60_2
  h1 := (1,4,1,3,4)
  h2 := (1,4,1,3,4)
  D := [[1, 4, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_60_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨60, by decide⟩
  m := 1
  T1 := T147_60
  T2 := Q2.T147_60_2
  h1 := (1,4,2,3,4)
  h2 := (1,4,2,3,4)
  D := [[1, 4, 2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_60_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨60, by decide⟩
  m := 1
  T1 := T147_60
  T2 := Q2.T147_60_2
  h1 := (1,4,3,3,4)
  h2 := (1,4,3,3,4)
  D := [[1, 4, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_60_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨60, by decide⟩
  m := 1
  T1 := T147_60
  T2 := Q2.T147_60_2
  h1 := (1,4,4,3,4)
  h2 := (1,4,4,3,4)
  D := [[1, 4, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_61_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨61, by decide⟩
  m := 1
  T1 := T147_61
  T2 := Q2.T147_61_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_61_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨61, by decide⟩
  m := 1
  T1 := T147_61
  T2 := Q2.T147_61_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 0, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_61_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨61, by decide⟩
  m := 1
  T1 := T147_61
  T2 := Q2.T147_61_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 0, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_61_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨61, by decide⟩
  m := 1
  T1 := T147_61
  T2 := Q2.T147_61_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 0, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_61_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨61, by decide⟩
  m := 1
  T1 := T147_61
  T2 := Q2.T147_61_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 0, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_61_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨61, by decide⟩
  m := 1
  T1 := T147_61
  T2 := Q2.T147_61_2
  h1 := (1,4,0,3,1)
  h2 := (1,4,0,3,1)
  D := [[1, 4, 0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_61_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨61, by decide⟩
  m := 1
  T1 := T147_61
  T2 := Q2.T147_61_2
  h1 := (1,4,1,2,1)
  h2 := (1,4,1,2,1)
  D := [[1, 4, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_61_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨61, by decide⟩
  m := 1
  T1 := T147_61
  T2 := Q2.T147_61_2
  h1 := (1,4,2,1,1)
  h2 := (1,4,2,1,1)
  D := [[1, 4, 2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_61_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨61, by decide⟩
  m := 1
  T1 := T147_61
  T2 := Q2.T147_61_2
  h1 := (1,4,3,0,1)
  h2 := (1,4,3,0,1)
  D := [[1, 4, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_61_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨61, by decide⟩
  m := 1
  T1 := T147_61
  T2 := Q2.T147_61_2
  h1 := (1,4,4,4,1)
  h2 := (1,4,4,4,1)
  D := [[1, 4, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_62_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨62, by decide⟩
  m := 1
  T1 := T147_62
  T2 := Q2.T147_62_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_62_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨62, by decide⟩
  m := 1
  T1 := T147_62
  T2 := Q2.T147_62_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 0, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_62_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨62, by decide⟩
  m := 1
  T1 := T147_62
  T2 := Q2.T147_62_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 0, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_62_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨62, by decide⟩
  m := 1
  T1 := T147_62
  T2 := Q2.T147_62_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 0, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_62_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨62, by decide⟩
  m := 1
  T1 := T147_62
  T2 := Q2.T147_62_2
  h1 := (0,0,4,2,0)
  h2 := (0,0,4,2,0)
  D := [[0, 0, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_62_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨62, by decide⟩
  m := 1
  T1 := T147_62
  T2 := Q2.T147_62_2
  h1 := (1,4,0,3,0)
  h2 := (1,4,0,3,0)
  D := [[1, 4, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_62_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨62, by decide⟩
  m := 1
  T1 := T147_62
  T2 := Q2.T147_62_2
  h1 := (1,4,1,1,0)
  h2 := (1,4,1,1,0)
  D := [[1, 4, 1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
