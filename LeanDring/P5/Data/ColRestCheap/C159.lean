/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C016

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 158: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_68_68_13 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T68_68
  T2 := Q2.T68_68_2
  h1 := (2,4,3,2,2)
  h2 := (2,4,3,2,1)
  D := [[2, 3, 2], [2, 3, 0], [2, 3, 3], [2, 3, 1], [2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_68_14 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T68_68
  T2 := Q2.T68_68_2
  h1 := (2,4,4,4,2)
  h2 := (2,4,4,4,1)
  D := [[2, 4, 4], [2, 4, 2], [2, 4, 0], [2, 4, 3], [2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_68_15 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T68_68
  T2 := Q2.T68_68_2
  h1 := (3,1,0,2,4)
  h2 := (3,1,0,2,1)
  D := [[3, 0, 4], [3, 0, 1], [3, 0, 3], [3, 0, 0], [3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_68_16 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T68_68
  T2 := Q2.T68_68_2
  h1 := (3,1,1,4,4)
  h2 := (3,1,1,4,1)
  D := [[3, 1, 2], [3, 1, 4], [3, 1, 1], [3, 1, 3], [3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_68_17 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T68_68
  T2 := Q2.T68_68_2
  h1 := (3,1,2,1,4)
  h2 := (3,1,2,1,1)
  D := [[3, 2, 0], [3, 2, 2], [3, 2, 4], [3, 2, 1], [3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_68_18 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T68_68
  T2 := Q2.T68_68_2
  h1 := (3,1,3,3,4)
  h2 := (3,1,3,3,1)
  D := [[3, 3, 3], [3, 3, 0], [3, 3, 2], [3, 3, 4], [3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_68_23 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T68_68
  T2 := Q2.T68_68_2
  h1 := (4,3,3,1,1)
  h2 := (4,3,3,1,0)
  D := [[4, 3, 4], [4, 3, 0], [4, 3, 1], [4, 3, 2], [4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_68_68_24 : ColCert where
  rK := ⟨68, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T68_68
  T2 := Q2.T68_68_2
  h1 := (4,3,4,3,1)
  h2 := (4,3,4,3,0)
  D := [[4, 4, 3], [4, 4, 4], [4, 4, 0], [4, 4, 1], [4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_0_0 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨0, by decide⟩
  m := 25
  T1 := T69_0
  T2 := Q2.T69_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_8_0 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T69_8
  T2 := Q2.T69_8_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_8_1 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T69_8
  T2 := Q2.T69_8_2
  h1 := (0,0,1,1,4)
  h2 := (0,0,1,1,4)
  D := [[0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_8_2 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T69_8
  T2 := Q2.T69_8_2
  h1 := (0,0,2,2,3)
  h2 := (0,0,2,2,3)
  D := [[0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_8_3 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T69_8
  T2 := Q2.T69_8_2
  h1 := (0,0,3,3,2)
  h2 := (0,0,3,3,2)
  D := [[0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_8_4 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T69_8
  T2 := Q2.T69_8_2
  h1 := (0,0,4,4,1)
  h2 := (0,0,4,4,1)
  D := [[0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_12_0 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T69_12
  T2 := Q2.T69_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_12_1 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T69_12
  T2 := Q2.T69_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_12_2 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T69_12
  T2 := Q2.T69_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_12_3 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T69_12
  T2 := Q2.T69_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_12_4 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T69_12
  T2 := Q2.T69_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_26_0 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T69_26
  T2 := Q2.T69_26_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_26_1 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T69_26
  T2 := Q2.T69_26_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_26_2 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T69_26
  T2 := Q2.T69_26_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_26_3 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T69_26
  T2 := Q2.T69_26_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_26_4 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T69_26
  T2 := Q2.T69_26_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_26_5 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T69_26
  T2 := Q2.T69_26_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_26_10 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T69_26
  T2 := Q2.T69_26_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_26_15 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T69_26
  T2 := Q2.T69_26_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_26_20 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T69_26
  T2 := Q2.T69_26_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_30_0 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T69_30
  T2 := Q2.T69_30_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_30_1 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T69_30
  T2 := Q2.T69_30_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_30_2 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T69_30
  T2 := Q2.T69_30_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_30_3 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T69_30
  T2 := Q2.T69_30_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_30_4 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T69_30
  T2 := Q2.T69_30_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_35_0 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T69_35
  T2 := Q2.T69_35_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_35_1 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T69_35
  T2 := Q2.T69_35_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_35_2 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T69_35
  T2 := Q2.T69_35_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_35_3 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T69_35
  T2 := Q2.T69_35_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_35_4 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T69_35
  T2 := Q2.T69_35_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_40_0 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T69_40
  T2 := Q2.T69_40_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_40_1 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T69_40
  T2 := Q2.T69_40_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_40_2 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T69_40
  T2 := Q2.T69_40_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_40_3 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T69_40
  T2 := Q2.T69_40_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_40_4 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T69_40
  T2 := Q2.T69_40_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_45_0 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T69_45
  T2 := Q2.T69_45_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_45_1 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T69_45
  T2 := Q2.T69_45_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_45_2 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T69_45
  T2 := Q2.T69_45_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_45_3 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T69_45
  T2 := Q2.T69_45_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_45_4 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T69_45
  T2 := Q2.T69_45_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_50_0 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T69_50
  T2 := Q2.T69_50_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_50_1 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T69_50
  T2 := Q2.T69_50_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_50_2 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T69_50
  T2 := Q2.T69_50_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_50_3 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T69_50
  T2 := Q2.T69_50_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_50_4 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T69_50
  T2 := Q2.T69_50_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_69_0 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨69, by decide⟩
  m := 5
  T1 := T69_69
  T2 := Q2.T69_69_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_69_1 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨69, by decide⟩
  m := 5
  T1 := T69_69
  T2 := Q2.T69_69_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_69_2 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨69, by decide⟩
  m := 5
  T1 := T69_69
  T2 := Q2.T69_69_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_69_3 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨69, by decide⟩
  m := 5
  T1 := T69_69
  T2 := Q2.T69_69_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_69_4 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨69, by decide⟩
  m := 5
  T1 := T69_69
  T2 := Q2.T69_69_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_69_5 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨69, by decide⟩
  m := 5
  T1 := T69_69
  T2 := Q2.T69_69_2
  h1 := (1,2,0,2,0)
  h2 := (1,2,0,2,0)
  D := [[1, 0, 4], [1, 0, 3], [1, 0, 2], [1, 0, 1], [1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_69_69_6 : ColCert where
  rK := ⟨69, by decide⟩
  rH := ⟨69, by decide⟩
  m := 5
  T1 := T69_69
  T2 := Q2.T69_69_2
  h1 := (1,2,1,3,0)
  h2 := (1,2,1,3,0)
  D := [[1, 1, 1], [1, 1, 0], [1, 1, 4], [1, 1, 3], [1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
