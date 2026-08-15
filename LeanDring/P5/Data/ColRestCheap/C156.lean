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
rest tier, chunk 155: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_66_66_13 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T66_66
  T2 := Q2.T66_66_2
  h1 := (2,4,3,3,4)
  h2 := (2,4,3,3,3)
  D := [[2, 3, 1], [2, 3, 4], [2, 3, 2], [2, 3, 0], [2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_66_14 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T66_66
  T2 := Q2.T66_66_2
  h1 := (2,4,4,2,4)
  h2 := (2,4,4,2,3)
  D := [[2, 4, 4], [2, 4, 2], [2, 4, 0], [2, 4, 3], [2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_66_15 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T66_66
  T2 := Q2.T66_66_2
  h1 := (3,1,0,2,2)
  h2 := (3,1,0,2,4)
  D := [[3, 0, 3], [3, 0, 0], [3, 0, 2], [3, 0, 4], [3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_66_16 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T66_66
  T2 := Q2.T66_66_2
  h1 := (3,1,1,1,2)
  h2 := (3,1,1,1,4)
  D := [[3, 1, 0], [3, 1, 2], [3, 1, 4], [3, 1, 1], [3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_66_17 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T66_66
  T2 := Q2.T66_66_2
  h1 := (3,1,2,0,2)
  h2 := (3,1,2,0,4)
  D := [[3, 2, 2], [3, 2, 4], [3, 2, 1], [3, 2, 3], [3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_66_18 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T66_66
  T2 := Q2.T66_66_2
  h1 := (3,1,3,4,2)
  h2 := (3,1,3,4,4)
  D := [[3, 3, 4], [3, 3, 1], [3, 3, 3], [3, 3, 0], [3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_66_19 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T66_66
  T2 := Q2.T66_66_2
  h1 := (3,1,4,3,2)
  h2 := (3,1,4,3,4)
  D := [[3, 4, 1], [3, 4, 3], [3, 4, 0], [3, 4, 2], [3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_66_20 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T66_66
  T2 := Q2.T66_66_2
  h1 := (4,3,0,0,0)
  h2 := (4,3,0,0,4)
  D := [[4, 0, 4], [4, 0, 0], [4, 0, 1], [4, 0, 2], [4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_66_21 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T66_66
  T2 := Q2.T66_66_2
  h1 := (4,3,1,4,0)
  h2 := (4,3,1,4,4)
  D := [[4, 1, 0], [4, 1, 1], [4, 1, 2], [4, 1, 3], [4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_66_22 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T66_66
  T2 := Q2.T66_66_2
  h1 := (4,3,2,3,0)
  h2 := (4,3,2,3,4)
  D := [[4, 2, 1], [4, 2, 2], [4, 2, 3], [4, 2, 4], [4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_66_23 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T66_66
  T2 := Q2.T66_66_2
  h1 := (4,3,3,2,0)
  h2 := (4,3,3,2,4)
  D := [[4, 3, 2], [4, 3, 3], [4, 3, 4], [4, 3, 0], [4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_66_66_24 : ColCert where
  rK := ⟨66, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T66_66
  T2 := Q2.T66_66_2
  h1 := (4,3,4,1,0)
  h2 := (4,3,4,1,4)
  D := [[4, 4, 3], [4, 4, 4], [4, 4, 0], [4, 4, 1], [4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_0_0 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨0, by decide⟩
  m := 25
  T1 := T67_0
  T2 := Q2.T67_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_7_0 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨7, by decide⟩
  m := 25
  T1 := T67_7
  T2 := Q2.T67_7_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_7_1 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨7, by decide⟩
  m := 25
  T1 := T67_7
  T2 := Q2.T67_7_2
  h1 := (0,0,1,3,4)
  h2 := (0,0,1,3,4)
  D := [[0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_7_2 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨7, by decide⟩
  m := 25
  T1 := T67_7
  T2 := Q2.T67_7_2
  h1 := (0,0,2,1,3)
  h2 := (0,0,2,1,3)
  D := [[0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_7_3 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨7, by decide⟩
  m := 25
  T1 := T67_7
  T2 := Q2.T67_7_2
  h1 := (0,0,3,4,2)
  h2 := (0,0,3,4,2)
  D := [[0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_7_4 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨7, by decide⟩
  m := 25
  T1 := T67_7
  T2 := Q2.T67_7_2
  h1 := (0,0,4,2,1)
  h2 := (0,0,4,2,1)
  D := [[0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_12_0 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T67_12
  T2 := Q2.T67_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_12_1 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T67_12
  T2 := Q2.T67_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_12_2 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T67_12
  T2 := Q2.T67_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_12_3 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T67_12
  T2 := Q2.T67_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_12_4 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T67_12
  T2 := Q2.T67_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_25_0 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨25, by decide⟩
  m := 25
  T1 := T67_25
  T2 := Q2.T67_25_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_25_1 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨25, by decide⟩
  m := 25
  T1 := T67_25
  T2 := Q2.T67_25_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_25_2 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨25, by decide⟩
  m := 25
  T1 := T67_25
  T2 := Q2.T67_25_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_25_3 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨25, by decide⟩
  m := 25
  T1 := T67_25
  T2 := Q2.T67_25_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_25_4 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨25, by decide⟩
  m := 25
  T1 := T67_25
  T2 := Q2.T67_25_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_25_5 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨25, by decide⟩
  m := 25
  T1 := T67_25
  T2 := Q2.T67_25_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_25_10 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨25, by decide⟩
  m := 25
  T1 := T67_25
  T2 := Q2.T67_25_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_25_15 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨25, by decide⟩
  m := 25
  T1 := T67_25
  T2 := Q2.T67_25_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_25_20 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨25, by decide⟩
  m := 25
  T1 := T67_25
  T2 := Q2.T67_25_2
  h1 := (0,0,4,2,0)
  h2 := (0,0,4,2,0)
  D := [[0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_30_0 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T67_30
  T2 := Q2.T67_30_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_30_1 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T67_30
  T2 := Q2.T67_30_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_30_2 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T67_30
  T2 := Q2.T67_30_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_30_3 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T67_30
  T2 := Q2.T67_30_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_30_4 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T67_30
  T2 := Q2.T67_30_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_35_0 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T67_35
  T2 := Q2.T67_35_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_35_1 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T67_35
  T2 := Q2.T67_35_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_35_2 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T67_35
  T2 := Q2.T67_35_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_35_3 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T67_35
  T2 := Q2.T67_35_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_35_4 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T67_35
  T2 := Q2.T67_35_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_40_0 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T67_40
  T2 := Q2.T67_40_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_40_1 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T67_40
  T2 := Q2.T67_40_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_40_2 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T67_40
  T2 := Q2.T67_40_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_40_3 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T67_40
  T2 := Q2.T67_40_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_40_4 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T67_40
  T2 := Q2.T67_40_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_45_0 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T67_45
  T2 := Q2.T67_45_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_45_1 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T67_45
  T2 := Q2.T67_45_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_45_2 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T67_45
  T2 := Q2.T67_45_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_45_3 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T67_45
  T2 := Q2.T67_45_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_45_4 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T67_45
  T2 := Q2.T67_45_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_50_0 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T67_50
  T2 := Q2.T67_50_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_50_1 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T67_50
  T2 := Q2.T67_50_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_50_2 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T67_50
  T2 := Q2.T67_50_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_50_3 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T67_50
  T2 := Q2.T67_50_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_50_4 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T67_50
  T2 := Q2.T67_50_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_67_0 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨67, by decide⟩
  m := 5
  T1 := T67_67
  T2 := Q2.T67_67_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_67_1 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨67, by decide⟩
  m := 5
  T1 := T67_67
  T2 := Q2.T67_67_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_67_67_2 : ColCert where
  rK := ⟨67, by decide⟩
  rH := ⟨67, by decide⟩
  m := 5
  T1 := T67_67
  T2 := Q2.T67_67_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
