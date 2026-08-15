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
rest tier, chunk 141: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_56_56_13 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T56_56
  T2 := Q2.T56_56_2
  h1 := (0,2,3,0,4)
  h2 := (0,2,3,0,0)
  D := [[2, 3, 4], [2, 3, 4], [2, 3, 4], [2, 3, 4], [2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_56_14 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T56_56
  T2 := Q2.T56_56_2
  h1 := (0,2,4,4,4)
  h2 := (0,2,4,4,0)
  D := [[2, 4, 2], [2, 4, 2], [2, 4, 2], [2, 4, 2], [2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_56_15 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T56_56
  T2 := Q2.T56_56_2
  h1 := (0,3,0,2,1)
  h2 := (0,3,0,2,0)
  D := [[3, 0, 0], [3, 0, 0], [3, 0, 0], [3, 0, 0], [3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_56_16 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T56_56
  T2 := Q2.T56_56_2
  h1 := (0,3,1,1,1)
  h2 := (0,3,1,1,0)
  D := [[3, 1, 2], [3, 1, 2], [3, 1, 2], [3, 1, 2], [3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_56_17 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T56_56
  T2 := Q2.T56_56_2
  h1 := (0,3,2,0,1)
  h2 := (0,3,2,0,0)
  D := [[3, 2, 4], [3, 2, 4], [3, 2, 4], [3, 2, 4], [3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_56_18 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T56_56
  T2 := Q2.T56_56_2
  h1 := (0,3,3,4,1)
  h2 := (0,3,3,4,0)
  D := [[3, 3, 1], [3, 3, 1], [3, 3, 1], [3, 3, 1], [3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_56_19 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T56_56
  T2 := Q2.T56_56_2
  h1 := (0,3,4,3,1)
  h2 := (0,3,4,3,0)
  D := [[3, 4, 3], [3, 4, 3], [3, 4, 3], [3, 4, 3], [3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_56_20 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T56_56
  T2 := Q2.T56_56_2
  h1 := (0,4,0,1,3)
  h2 := (0,4,0,1,0)
  D := [[4, 0, 0], [4, 0, 0], [4, 0, 0], [4, 0, 0], [4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_56_21 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T56_56
  T2 := Q2.T56_56_2
  h1 := (0,4,1,0,3)
  h2 := (0,4,1,0,0)
  D := [[4, 1, 1], [4, 1, 1], [4, 1, 1], [4, 1, 1], [4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_56_22 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T56_56
  T2 := Q2.T56_56_2
  h1 := (0,4,2,4,3)
  h2 := (0,4,2,4,0)
  D := [[4, 2, 2], [4, 2, 2], [4, 2, 2], [4, 2, 2], [4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_56_23 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T56_56
  T2 := Q2.T56_56_2
  h1 := (0,4,3,3,3)
  h2 := (0,4,3,3,0)
  D := [[4, 3, 3], [4, 3, 3], [4, 3, 3], [4, 3, 3], [4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_56_56_24 : ColCert where
  rK := ⟨56, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T56_56
  T2 := Q2.T56_56_2
  h1 := (0,4,4,2,3)
  h2 := (0,4,4,2,0)
  D := [[4, 4, 4], [4, 4, 4], [4, 4, 4], [4, 4, 4], [4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_0_0 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨0, by decide⟩
  m := 25
  T1 := T57_0
  T2 := Q2.T57_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_7_0 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨7, by decide⟩
  m := 25
  T1 := T57_7
  T2 := Q2.T57_7_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_7_1 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨7, by decide⟩
  m := 25
  T1 := T57_7
  T2 := Q2.T57_7_2
  h1 := (0,0,1,3,4)
  h2 := (0,0,1,3,4)
  D := [[0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_7_2 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨7, by decide⟩
  m := 25
  T1 := T57_7
  T2 := Q2.T57_7_2
  h1 := (0,0,2,1,3)
  h2 := (0,0,2,1,3)
  D := [[0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_7_3 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨7, by decide⟩
  m := 25
  T1 := T57_7
  T2 := Q2.T57_7_2
  h1 := (0,0,3,4,2)
  h2 := (0,0,3,4,2)
  D := [[0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_7_4 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨7, by decide⟩
  m := 25
  T1 := T57_7
  T2 := Q2.T57_7_2
  h1 := (0,0,4,2,1)
  h2 := (0,0,4,2,1)
  D := [[0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_12_0 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T57_12
  T2 := Q2.T57_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_12_1 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T57_12
  T2 := Q2.T57_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_12_2 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T57_12
  T2 := Q2.T57_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_12_3 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T57_12
  T2 := Q2.T57_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_12_4 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T57_12
  T2 := Q2.T57_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_25_0 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨25, by decide⟩
  m := 25
  T1 := T57_25
  T2 := Q2.T57_25_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_25_1 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨25, by decide⟩
  m := 25
  T1 := T57_25
  T2 := Q2.T57_25_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_25_2 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨25, by decide⟩
  m := 25
  T1 := T57_25
  T2 := Q2.T57_25_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_25_3 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨25, by decide⟩
  m := 25
  T1 := T57_25
  T2 := Q2.T57_25_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_25_4 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨25, by decide⟩
  m := 25
  T1 := T57_25
  T2 := Q2.T57_25_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_25_5 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨25, by decide⟩
  m := 25
  T1 := T57_25
  T2 := Q2.T57_25_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_25_10 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨25, by decide⟩
  m := 25
  T1 := T57_25
  T2 := Q2.T57_25_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_25_15 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨25, by decide⟩
  m := 25
  T1 := T57_25
  T2 := Q2.T57_25_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_25_20 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨25, by decide⟩
  m := 25
  T1 := T57_25
  T2 := Q2.T57_25_2
  h1 := (0,0,4,2,0)
  h2 := (0,0,4,2,0)
  D := [[0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_28_0 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T57_28
  T2 := Q2.T57_28_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_28_1 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T57_28
  T2 := Q2.T57_28_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_28_2 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T57_28
  T2 := Q2.T57_28_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_28_3 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T57_28
  T2 := Q2.T57_28_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_28_4 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T57_28
  T2 := Q2.T57_28_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_33_0 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T57_33
  T2 := Q2.T57_33_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_33_1 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T57_33
  T2 := Q2.T57_33_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_33_2 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T57_33
  T2 := Q2.T57_33_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_33_3 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T57_33
  T2 := Q2.T57_33_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_33_4 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T57_33
  T2 := Q2.T57_33_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_38_0 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T57_38
  T2 := Q2.T57_38_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_38_1 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T57_38
  T2 := Q2.T57_38_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_38_2 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T57_38
  T2 := Q2.T57_38_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_38_3 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T57_38
  T2 := Q2.T57_38_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_38_4 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T57_38
  T2 := Q2.T57_38_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_43_0 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T57_43
  T2 := Q2.T57_43_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_43_1 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T57_43
  T2 := Q2.T57_43_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_43_2 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T57_43
  T2 := Q2.T57_43_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_43_3 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T57_43
  T2 := Q2.T57_43_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_43_4 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T57_43
  T2 := Q2.T57_43_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_48_0 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T57_48
  T2 := Q2.T57_48_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_48_1 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T57_48
  T2 := Q2.T57_48_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_48_2 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T57_48
  T2 := Q2.T57_48_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_48_3 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T57_48
  T2 := Q2.T57_48_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_48_4 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T57_48
  T2 := Q2.T57_48_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_57_0 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨57, by decide⟩
  m := 5
  T1 := T57_57
  T2 := Q2.T57_57_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_57_1 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨57, by decide⟩
  m := 5
  T1 := T57_57
  T2 := Q2.T57_57_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_57_57_2 : ColCert where
  rK := ⟨57, by decide⟩
  rH := ⟨57, by decide⟩
  m := 5
  T1 := T57_57
  T2 := Q2.T57_57_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
