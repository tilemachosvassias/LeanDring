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
rest tier, chunk 149: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_62_62_13 : ColCert where
  rK := ⟨62, by decide⟩
  rH := ⟨62, by decide⟩
  m := 5
  T1 := T62_62
  T2 := Q2.T62_62_2
  h1 := (2,3,3,4,4)
  h2 := (2,3,3,4,0)
  D := [[2, 3, 4], [2, 3, 2], [2, 3, 0], [2, 3, 3], [2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_62_62_14 : ColCert where
  rK := ⟨62, by decide⟩
  rH := ⟨62, by decide⟩
  m := 5
  T1 := T62_62
  T2 := Q2.T62_62_2
  h1 := (2,3,4,2,4)
  h2 := (2,3,4,2,0)
  D := [[2, 4, 0], [2, 4, 3], [2, 4, 1], [2, 4, 4], [2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_62_62_15 : ColCert where
  rK := ⟨62, by decide⟩
  rH := ⟨62, by decide⟩
  m := 5
  T1 := T62_62
  T2 := Q2.T62_62_2
  h1 := (3,2,0,1,0)
  h2 := (3,2,0,1,2)
  D := [[3, 0, 4], [3, 0, 1], [3, 0, 3], [3, 0, 0], [3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_62_62_16 : ColCert where
  rK := ⟨62, by decide⟩
  rH := ⟨62, by decide⟩
  m := 5
  T1 := T62_62
  T2 := Q2.T62_62_2
  h1 := (3,2,1,4,0)
  h2 := (3,2,1,4,2)
  D := [[3, 1, 3], [3, 1, 0], [3, 1, 2], [3, 1, 4], [3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_62_62_17 : ColCert where
  rK := ⟨62, by decide⟩
  rH := ⟨62, by decide⟩
  m := 5
  T1 := T62_62
  T2 := Q2.T62_62_2
  h1 := (3,2,2,2,0)
  h2 := (3,2,2,2,2)
  D := [[3, 2, 2], [3, 2, 4], [3, 2, 1], [3, 2, 3], [3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_62_62_18 : ColCert where
  rK := ⟨62, by decide⟩
  rH := ⟨62, by decide⟩
  m := 5
  T1 := T62_62
  T2 := Q2.T62_62_2
  h1 := (3,2,3,0,0)
  h2 := (3,2,3,0,2)
  D := [[3, 3, 1], [3, 3, 3], [3, 3, 0], [3, 3, 2], [3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_62_62_19 : ColCert where
  rK := ⟨62, by decide⟩
  rH := ⟨62, by decide⟩
  m := 5
  T1 := T62_62
  T2 := Q2.T62_62_2
  h1 := (3,2,4,3,0)
  h2 := (3,2,4,3,2)
  D := [[3, 4, 0], [3, 4, 2], [3, 4, 4], [3, 4, 1], [3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_62_62_20 : ColCert where
  rK := ⟨62, by decide⟩
  rH := ⟨62, by decide⟩
  m := 5
  T1 := T62_62
  T2 := Q2.T62_62_2
  h1 := (4,1,0,1,2)
  h2 := (4,1,0,1,0)
  D := [[4, 0, 2], [4, 0, 3], [4, 0, 4], [4, 0, 0], [4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_62_62_21 : ColCert where
  rK := ⟨62, by decide⟩
  rH := ⟨62, by decide⟩
  m := 5
  T1 := T62_62
  T2 := Q2.T62_62_2
  h1 := (4,1,1,4,2)
  h2 := (4,1,1,4,0)
  D := [[4, 1, 4], [4, 1, 0], [4, 1, 1], [4, 1, 2], [4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_62_62_22 : ColCert where
  rK := ⟨62, by decide⟩
  rH := ⟨62, by decide⟩
  m := 5
  T1 := T62_62
  T2 := Q2.T62_62_2
  h1 := (4,1,2,2,2)
  h2 := (4,1,2,2,0)
  D := [[4, 2, 1], [4, 2, 2], [4, 2, 3], [4, 2, 4], [4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_62_62_23 : ColCert where
  rK := ⟨62, by decide⟩
  rH := ⟨62, by decide⟩
  m := 5
  T1 := T62_62
  T2 := Q2.T62_62_2
  h1 := (4,1,3,0,2)
  h2 := (4,1,3,0,0)
  D := [[4, 3, 3], [4, 3, 4], [4, 3, 0], [4, 3, 1], [4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_62_62_24 : ColCert where
  rK := ⟨62, by decide⟩
  rH := ⟨62, by decide⟩
  m := 5
  T1 := T62_62
  T2 := Q2.T62_62_2
  h1 := (4,1,4,3,2)
  h2 := (4,1,4,3,0)
  D := [[4, 4, 0], [4, 4, 1], [4, 4, 2], [4, 4, 3], [4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_0_0 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨0, by decide⟩
  m := 25
  T1 := T63_0
  T2 := Q2.T63_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_6_0 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨6, by decide⟩
  m := 25
  T1 := T63_6
  T2 := Q2.T63_6_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_6_1 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨6, by decide⟩
  m := 25
  T1 := T63_6
  T2 := Q2.T63_6_2
  h1 := (0,0,1,2,4)
  h2 := (0,0,1,2,4)
  D := [[0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_6_2 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨6, by decide⟩
  m := 25
  T1 := T63_6
  T2 := Q2.T63_6_2
  h1 := (0,0,2,4,3)
  h2 := (0,0,2,4,3)
  D := [[0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_6_3 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨6, by decide⟩
  m := 25
  T1 := T63_6
  T2 := Q2.T63_6_2
  h1 := (0,0,3,1,2)
  h2 := (0,0,3,1,2)
  D := [[0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_6_4 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨6, by decide⟩
  m := 25
  T1 := T63_6
  T2 := Q2.T63_6_2
  h1 := (0,0,4,3,1)
  h2 := (0,0,4,3,1)
  D := [[0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_12_0 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T63_12
  T2 := Q2.T63_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_12_1 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T63_12
  T2 := Q2.T63_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_12_2 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T63_12
  T2 := Q2.T63_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_12_3 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T63_12
  T2 := Q2.T63_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_12_4 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T63_12
  T2 := Q2.T63_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_24_0 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨24, by decide⟩
  m := 25
  T1 := T63_24
  T2 := Q2.T63_24_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_24_1 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨24, by decide⟩
  m := 25
  T1 := T63_24
  T2 := Q2.T63_24_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_24_2 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨24, by decide⟩
  m := 25
  T1 := T63_24
  T2 := Q2.T63_24_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_24_3 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨24, by decide⟩
  m := 25
  T1 := T63_24
  T2 := Q2.T63_24_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_24_4 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨24, by decide⟩
  m := 25
  T1 := T63_24
  T2 := Q2.T63_24_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_24_5 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨24, by decide⟩
  m := 25
  T1 := T63_24
  T2 := Q2.T63_24_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_24_10 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨24, by decide⟩
  m := 25
  T1 := T63_24
  T2 := Q2.T63_24_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_24_15 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨24, by decide⟩
  m := 25
  T1 := T63_24
  T2 := Q2.T63_24_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_24_20 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨24, by decide⟩
  m := 25
  T1 := T63_24
  T2 := Q2.T63_24_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_29_0 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T63_29
  T2 := Q2.T63_29_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_29_1 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T63_29
  T2 := Q2.T63_29_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_29_2 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T63_29
  T2 := Q2.T63_29_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_29_3 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T63_29
  T2 := Q2.T63_29_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_29_4 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T63_29
  T2 := Q2.T63_29_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_34_0 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T63_34
  T2 := Q2.T63_34_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_34_1 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T63_34
  T2 := Q2.T63_34_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_34_2 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T63_34
  T2 := Q2.T63_34_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_34_3 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T63_34
  T2 := Q2.T63_34_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_34_4 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T63_34
  T2 := Q2.T63_34_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_39_0 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T63_39
  T2 := Q2.T63_39_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_39_1 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T63_39
  T2 := Q2.T63_39_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_39_2 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T63_39
  T2 := Q2.T63_39_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_39_3 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T63_39
  T2 := Q2.T63_39_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_39_4 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T63_39
  T2 := Q2.T63_39_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_44_0 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T63_44
  T2 := Q2.T63_44_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_44_1 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T63_44
  T2 := Q2.T63_44_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_44_2 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T63_44
  T2 := Q2.T63_44_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_44_3 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T63_44
  T2 := Q2.T63_44_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_44_4 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T63_44
  T2 := Q2.T63_44_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_49_0 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T63_49
  T2 := Q2.T63_49_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_49_1 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T63_49
  T2 := Q2.T63_49_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_49_2 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T63_49
  T2 := Q2.T63_49_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_49_3 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T63_49
  T2 := Q2.T63_49_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_49_4 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T63_49
  T2 := Q2.T63_49_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_63_0 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨63, by decide⟩
  m := 5
  T1 := T63_63
  T2 := Q2.T63_63_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_63_1 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨63, by decide⟩
  m := 5
  T1 := T63_63
  T2 := Q2.T63_63_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_63_2 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨63, by decide⟩
  m := 5
  T1 := T63_63
  T2 := Q2.T63_63_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
