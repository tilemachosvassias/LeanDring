/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C025

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 18: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_116_13_18 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T116_13
  T2 := Q2.T116_13_2
  h1 := (0,0,3,3,2)
  h2 := (0,0,3,3,2)
  D := [[0, 3, 3, 2], [0, 3, 3, 0], [0, 3, 3, 3], [0, 3, 3, 1], [0, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_13_19 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T116_13
  T2 := Q2.T116_13_2
  h1 := (0,0,3,4,2)
  h2 := (0,0,3,4,2)
  D := [[0, 3, 4, 2], [0, 3, 4, 1], [0, 3, 4, 0], [0, 3, 4, 4], [0, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_13_20 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T116_13
  T2 := Q2.T116_13_2
  h1 := (0,0,4,0,1)
  h2 := (0,0,4,0,1)
  D := [[0, 4, 0, 1], [0, 4, 0, 1], [0, 4, 0, 1], [0, 4, 0, 1], [0, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_13_21 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T116_13
  T2 := Q2.T116_13_2
  h1 := (0,0,4,1,1)
  h2 := (0,0,4,1,1)
  D := [[0, 4, 1, 1], [0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4], [0, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_13_22 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T116_13
  T2 := Q2.T116_13_2
  h1 := (0,0,4,2,1)
  h2 := (0,0,4,2,1)
  D := [[0, 4, 2, 1], [0, 4, 2, 3], [0, 4, 2, 0], [0, 4, 2, 2], [0, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_13_23 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T116_13
  T2 := Q2.T116_13_2
  h1 := (0,0,4,3,1)
  h2 := (0,0,4,3,1)
  D := [[0, 4, 3, 1], [0, 4, 3, 4], [0, 4, 3, 2], [0, 4, 3, 0], [0, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_13_24 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T116_13
  T2 := Q2.T116_13_2
  h1 := (0,0,4,4,1)
  h2 := (0,0,4,4,1)
  D := [[0, 4, 4, 1], [0, 4, 4, 0], [0, 4, 4, 4], [0, 4, 4, 3], [0, 4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_19_0 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨19, by decide⟩
  m := 5
  T1 := T116_19
  T2 := Q2.T116_19_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_19_1 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨19, by decide⟩
  m := 5
  T1 := T116_19
  T2 := Q2.T116_19_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_19_2 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨19, by decide⟩
  m := 5
  T1 := T116_19
  T2 := Q2.T116_19_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_19_3 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨19, by decide⟩
  m := 5
  T1 := T116_19
  T2 := Q2.T116_19_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_19_4 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨19, by decide⟩
  m := 5
  T1 := T116_19
  T2 := Q2.T116_19_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_19_5 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨19, by decide⟩
  m := 5
  T1 := T116_19
  T2 := Q2.T116_19_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 1, 4, 0], [0, 1, 4, 4], [0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_19_10 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨19, by decide⟩
  m := 5
  T1 := T116_19
  T2 := Q2.T116_19_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 2, 3, 0], [0, 2, 3, 3], [0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_19_15 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨19, by decide⟩
  m := 5
  T1 := T116_19
  T2 := Q2.T116_19_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 3, 2, 0], [0, 3, 2, 2], [0, 3, 2, 4], [0, 3, 2, 1], [0, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_19_20 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨19, by decide⟩
  m := 5
  T1 := T116_19
  T2 := Q2.T116_19_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 4, 1, 0], [0, 4, 1, 1], [0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_24_0 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨24, by decide⟩
  m := 5
  T1 := T116_24
  T2 := Q2.T116_24_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_24_1 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨24, by decide⟩
  m := 5
  T1 := T116_24
  T2 := Q2.T116_24_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_24_2 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨24, by decide⟩
  m := 5
  T1 := T116_24
  T2 := Q2.T116_24_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_24_3 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨24, by decide⟩
  m := 5
  T1 := T116_24
  T2 := Q2.T116_24_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_24_4 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨24, by decide⟩
  m := 5
  T1 := T116_24
  T2 := Q2.T116_24_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_24_5 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨24, by decide⟩
  m := 5
  T1 := T116_24
  T2 := Q2.T116_24_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 1, 2, 0], [0, 1, 2, 2], [0, 1, 2, 4], [0, 1, 2, 1], [0, 1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_24_10 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨24, by decide⟩
  m := 5
  T1 := T116_24
  T2 := Q2.T116_24_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 2, 4, 0], [0, 2, 4, 4], [0, 2, 4, 3], [0, 2, 4, 2], [0, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_24_15 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨24, by decide⟩
  m := 5
  T1 := T116_24
  T2 := Q2.T116_24_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 3, 1, 0], [0, 3, 1, 1], [0, 3, 1, 2], [0, 3, 1, 3], [0, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_24_20 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨24, by decide⟩
  m := 5
  T1 := T116_24
  T2 := Q2.T116_24_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 4, 3, 0], [0, 4, 3, 3], [0, 4, 3, 1], [0, 4, 3, 4], [0, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_25_0 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨25, by decide⟩
  m := 5
  T1 := T116_25
  T2 := Q2.T116_25_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_25_1 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨25, by decide⟩
  m := 5
  T1 := T116_25
  T2 := Q2.T116_25_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_25_2 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨25, by decide⟩
  m := 5
  T1 := T116_25
  T2 := Q2.T116_25_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_25_3 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨25, by decide⟩
  m := 5
  T1 := T116_25
  T2 := Q2.T116_25_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_25_4 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨25, by decide⟩
  m := 5
  T1 := T116_25
  T2 := Q2.T116_25_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_25_5 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨25, by decide⟩
  m := 5
  T1 := T116_25
  T2 := Q2.T116_25_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 1, 3, 0], [0, 1, 3, 3], [0, 1, 3, 1], [0, 1, 3, 4], [0, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_25_10 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨25, by decide⟩
  m := 5
  T1 := T116_25
  T2 := Q2.T116_25_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 2, 1, 0], [0, 2, 1, 1], [0, 2, 1, 2], [0, 2, 1, 3], [0, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_25_15 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨25, by decide⟩
  m := 5
  T1 := T116_25
  T2 := Q2.T116_25_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 3, 4, 0], [0, 3, 4, 4], [0, 3, 4, 3], [0, 3, 4, 2], [0, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_25_20 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨25, by decide⟩
  m := 5
  T1 := T116_25
  T2 := Q2.T116_25_2
  h1 := (0,0,4,2,0)
  h2 := (0,0,4,2,0)
  D := [[0, 4, 2, 0], [0, 4, 2, 2], [0, 4, 2, 4], [0, 4, 2, 1], [0, 4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_26_0 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T116_26
  T2 := Q2.T116_26_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_26_1 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T116_26
  T2 := Q2.T116_26_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_26_2 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T116_26
  T2 := Q2.T116_26_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_26_3 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T116_26
  T2 := Q2.T116_26_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_26_4 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T116_26
  T2 := Q2.T116_26_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_26_5 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T116_26
  T2 := Q2.T116_26_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 1, 1, 0], [0, 1, 1, 1], [0, 1, 1, 2], [0, 1, 1, 3], [0, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_26_10 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T116_26
  T2 := Q2.T116_26_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 2, 2, 0], [0, 2, 2, 2], [0, 2, 2, 4], [0, 2, 2, 1], [0, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_26_15 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T116_26
  T2 := Q2.T116_26_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 3, 3, 0], [0, 3, 3, 3], [0, 3, 3, 1], [0, 3, 3, 4], [0, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_26_20 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T116_26
  T2 := Q2.T116_26_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 4, 4, 0], [0, 4, 4, 4], [0, 4, 4, 3], [0, 4, 4, 2], [0, 4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_27_0 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T116_27
  T2 := Q2.T116_27_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_27_1 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T116_27
  T2 := Q2.T116_27_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_27_2 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T116_27
  T2 := Q2.T116_27_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_27_3 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T116_27
  T2 := Q2.T116_27_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_27_4 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T116_27
  T2 := Q2.T116_27_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_27_5 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T116_27
  T2 := Q2.T116_27_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 1, 0, 0], [0, 1, 0, 0], [0, 1, 0, 0], [0, 1, 0, 0], [0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_27_10 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T116_27
  T2 := Q2.T116_27_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 2, 0, 0], [0, 2, 0, 0], [0, 2, 0, 0], [0, 2, 0, 0], [0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_27_15 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T116_27
  T2 := Q2.T116_27_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 3, 0, 0], [0, 3, 0, 0], [0, 3, 0, 0], [0, 3, 0, 0], [0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_27_20 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T116_27
  T2 := Q2.T116_27_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 4, 0, 0], [0, 4, 0, 0], [0, 4, 0, 0], [0, 4, 0, 0], [0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_28_0 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T116_28
  T2 := Q2.T116_28_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_28_1 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T116_28
  T2 := Q2.T116_28_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_28_2 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T116_28
  T2 := Q2.T116_28_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_28_3 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T116_28
  T2 := Q2.T116_28_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_28_4 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T116_28
  T2 := Q2.T116_28_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_33_0 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T116_33
  T2 := Q2.T116_33_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_33_1 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T116_33
  T2 := Q2.T116_33_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_33_2 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T116_33
  T2 := Q2.T116_33_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
