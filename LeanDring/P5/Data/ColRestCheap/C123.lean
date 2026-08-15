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
rest tier, chunk 122: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_147_87_17 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨87, by decide⟩
  m := 1
  T1 := T147_87
  T2 := Q2.T147_87_2
  h1 := (3,0,2,3,2)
  h2 := (3,0,2,3,2)
  D := [[3, 0, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_87_18 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨87, by decide⟩
  m := 1
  T1 := T147_87
  T2 := Q2.T147_87_2
  h1 := (3,0,3,1,2)
  h2 := (3,0,3,1,2)
  D := [[3, 0, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_87_19 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨87, by decide⟩
  m := 1
  T1 := T147_87
  T2 := Q2.T147_87_2
  h1 := (3,0,4,4,2)
  h2 := (3,0,4,4,2)
  D := [[3, 0, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_87_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨87, by decide⟩
  m := 1
  T1 := T147_87
  T2 := Q2.T147_87_2
  h1 := (4,0,0,1,4)
  h2 := (4,0,0,1,4)
  D := [[4, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_87_21 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨87, by decide⟩
  m := 1
  T1 := T147_87
  T2 := Q2.T147_87_2
  h1 := (4,0,1,4,4)
  h2 := (4,0,1,4,4)
  D := [[4, 0, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_87_22 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨87, by decide⟩
  m := 1
  T1 := T147_87
  T2 := Q2.T147_87_2
  h1 := (4,0,2,2,4)
  h2 := (4,0,2,2,4)
  D := [[4, 0, 2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_87_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨87, by decide⟩
  m := 1
  T1 := T147_87
  T2 := Q2.T147_87_2
  h1 := (4,0,3,0,4)
  h2 := (4,0,3,0,4)
  D := [[4, 0, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_87_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨87, by decide⟩
  m := 1
  T1 := T147_87
  T2 := Q2.T147_87_2
  h1 := (4,0,4,3,4)
  h2 := (4,0,4,3,4)
  D := [[4, 0, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_88_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨88, by decide⟩
  m := 1
  T1 := T147_88
  T2 := Q2.T147_88_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_88_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨88, by decide⟩
  m := 1
  T1 := T147_88
  T2 := Q2.T147_88_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 0, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_88_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨88, by decide⟩
  m := 1
  T1 := T147_88
  T2 := Q2.T147_88_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 0, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_88_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨88, by decide⟩
  m := 1
  T1 := T147_88
  T2 := Q2.T147_88_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 0, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_88_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨88, by decide⟩
  m := 1
  T1 := T147_88
  T2 := Q2.T147_88_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 0, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_88_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨88, by decide⟩
  m := 1
  T1 := T147_88
  T2 := Q2.T147_88_2
  h1 := (1,0,0,4,0)
  h2 := (1,0,0,4,0)
  D := [[1, 0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_88_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨88, by decide⟩
  m := 1
  T1 := T147_88
  T2 := Q2.T147_88_2
  h1 := (1,0,1,1,0)
  h2 := (1,0,1,1,0)
  D := [[1, 0, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_88_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨88, by decide⟩
  m := 1
  T1 := T147_88
  T2 := Q2.T147_88_2
  h1 := (1,0,2,3,0)
  h2 := (1,0,2,3,0)
  D := [[1, 0, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_88_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨88, by decide⟩
  m := 1
  T1 := T147_88
  T2 := Q2.T147_88_2
  h1 := (1,0,3,0,0)
  h2 := (1,0,3,0,0)
  D := [[1, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_88_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨88, by decide⟩
  m := 1
  T1 := T147_88
  T2 := Q2.T147_88_2
  h1 := (1,0,4,2,0)
  h2 := (1,0,4,2,0)
  D := [[1, 0, 4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_88_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨88, by decide⟩
  m := 1
  T1 := T147_88
  T2 := Q2.T147_88_2
  h1 := (2,0,0,3,4)
  h2 := (2,0,0,3,4)
  D := [[2, 0, 0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_88_11 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨88, by decide⟩
  m := 1
  T1 := T147_88
  T2 := Q2.T147_88_2
  h1 := (2,0,1,0,4)
  h2 := (2,0,1,0,4)
  D := [[2, 0, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_88_12 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨88, by decide⟩
  m := 1
  T1 := T147_88
  T2 := Q2.T147_88_2
  h1 := (2,0,2,2,4)
  h2 := (2,0,2,2,4)
  D := [[2, 0, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_88_13 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨88, by decide⟩
  m := 1
  T1 := T147_88
  T2 := Q2.T147_88_2
  h1 := (2,0,3,4,4)
  h2 := (2,0,3,4,4)
  D := [[2, 0, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_88_14 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨88, by decide⟩
  m := 1
  T1 := T147_88
  T2 := Q2.T147_88_2
  h1 := (2,0,4,1,4)
  h2 := (2,0,4,1,4)
  D := [[2, 0, 4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_88_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨88, by decide⟩
  m := 1
  T1 := T147_88
  T2 := Q2.T147_88_2
  h1 := (3,0,0,2,2)
  h2 := (3,0,0,2,2)
  D := [[3, 0, 0, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_88_16 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨88, by decide⟩
  m := 1
  T1 := T147_88
  T2 := Q2.T147_88_2
  h1 := (3,0,1,4,2)
  h2 := (3,0,1,4,2)
  D := [[3, 0, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_88_17 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨88, by decide⟩
  m := 1
  T1 := T147_88
  T2 := Q2.T147_88_2
  h1 := (3,0,2,1,2)
  h2 := (3,0,2,1,2)
  D := [[3, 0, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_88_18 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨88, by decide⟩
  m := 1
  T1 := T147_88
  T2 := Q2.T147_88_2
  h1 := (3,0,3,3,2)
  h2 := (3,0,3,3,2)
  D := [[3, 0, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_88_19 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨88, by decide⟩
  m := 1
  T1 := T147_88
  T2 := Q2.T147_88_2
  h1 := (3,0,4,0,2)
  h2 := (3,0,4,0,2)
  D := [[3, 0, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_88_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨88, by decide⟩
  m := 1
  T1 := T147_88
  T2 := Q2.T147_88_2
  h1 := (4,0,0,1,4)
  h2 := (4,0,0,1,4)
  D := [[4, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_88_21 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨88, by decide⟩
  m := 1
  T1 := T147_88
  T2 := Q2.T147_88_2
  h1 := (4,0,1,3,4)
  h2 := (4,0,1,3,4)
  D := [[4, 0, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_88_22 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨88, by decide⟩
  m := 1
  T1 := T147_88
  T2 := Q2.T147_88_2
  h1 := (4,0,2,0,4)
  h2 := (4,0,2,0,4)
  D := [[4, 0, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_88_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨88, by decide⟩
  m := 1
  T1 := T147_88
  T2 := Q2.T147_88_2
  h1 := (4,0,3,2,4)
  h2 := (4,0,3,2,4)
  D := [[4, 0, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_88_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨88, by decide⟩
  m := 1
  T1 := T147_88
  T2 := Q2.T147_88_2
  h1 := (4,0,4,4,4)
  h2 := (4,0,4,4,4)
  D := [[4, 0, 4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_89_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨89, by decide⟩
  m := 1
  T1 := T147_89
  T2 := Q2.T147_89_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_89_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨89, by decide⟩
  m := 1
  T1 := T147_89
  T2 := Q2.T147_89_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 0, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_89_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨89, by decide⟩
  m := 1
  T1 := T147_89
  T2 := Q2.T147_89_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 0, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_89_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨89, by decide⟩
  m := 1
  T1 := T147_89
  T2 := Q2.T147_89_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 0, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_89_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨89, by decide⟩
  m := 1
  T1 := T147_89
  T2 := Q2.T147_89_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 0, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_89_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨89, by decide⟩
  m := 1
  T1 := T147_89
  T2 := Q2.T147_89_2
  h1 := (1,0,0,4,0)
  h2 := (1,0,0,4,0)
  D := [[1, 0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_89_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨89, by decide⟩
  m := 1
  T1 := T147_89
  T2 := Q2.T147_89_2
  h1 := (1,0,1,0,0)
  h2 := (1,0,1,0,0)
  D := [[1, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_89_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨89, by decide⟩
  m := 1
  T1 := T147_89
  T2 := Q2.T147_89_2
  h1 := (1,0,2,1,0)
  h2 := (1,0,2,1,0)
  D := [[1, 0, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_89_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨89, by decide⟩
  m := 1
  T1 := T147_89
  T2 := Q2.T147_89_2
  h1 := (1,0,3,2,0)
  h2 := (1,0,3,2,0)
  D := [[1, 0, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_89_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨89, by decide⟩
  m := 1
  T1 := T147_89
  T2 := Q2.T147_89_2
  h1 := (1,0,4,3,0)
  h2 := (1,0,4,3,0)
  D := [[1, 0, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_89_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨89, by decide⟩
  m := 1
  T1 := T147_89
  T2 := Q2.T147_89_2
  h1 := (2,0,0,3,4)
  h2 := (2,0,0,3,4)
  D := [[2, 0, 0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_89_11 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨89, by decide⟩
  m := 1
  T1 := T147_89
  T2 := Q2.T147_89_2
  h1 := (2,0,1,4,4)
  h2 := (2,0,1,4,4)
  D := [[2, 0, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_89_12 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨89, by decide⟩
  m := 1
  T1 := T147_89
  T2 := Q2.T147_89_2
  h1 := (2,0,2,0,4)
  h2 := (2,0,2,0,4)
  D := [[2, 0, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_89_13 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨89, by decide⟩
  m := 1
  T1 := T147_89
  T2 := Q2.T147_89_2
  h1 := (2,0,3,1,4)
  h2 := (2,0,3,1,4)
  D := [[2, 0, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_89_14 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨89, by decide⟩
  m := 1
  T1 := T147_89
  T2 := Q2.T147_89_2
  h1 := (2,0,4,2,4)
  h2 := (2,0,4,2,4)
  D := [[2, 0, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_89_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨89, by decide⟩
  m := 1
  T1 := T147_89
  T2 := Q2.T147_89_2
  h1 := (3,0,0,2,2)
  h2 := (3,0,0,2,2)
  D := [[3, 0, 0, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_89_16 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨89, by decide⟩
  m := 1
  T1 := T147_89
  T2 := Q2.T147_89_2
  h1 := (3,0,1,3,2)
  h2 := (3,0,1,3,2)
  D := [[3, 0, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_89_17 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨89, by decide⟩
  m := 1
  T1 := T147_89
  T2 := Q2.T147_89_2
  h1 := (3,0,2,4,2)
  h2 := (3,0,2,4,2)
  D := [[3, 0, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_89_18 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨89, by decide⟩
  m := 1
  T1 := T147_89
  T2 := Q2.T147_89_2
  h1 := (3,0,3,0,2)
  h2 := (3,0,3,0,2)
  D := [[3, 0, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_89_19 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨89, by decide⟩
  m := 1
  T1 := T147_89
  T2 := Q2.T147_89_2
  h1 := (3,0,4,1,2)
  h2 := (3,0,4,1,2)
  D := [[3, 0, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_89_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨89, by decide⟩
  m := 1
  T1 := T147_89
  T2 := Q2.T147_89_2
  h1 := (4,0,0,1,4)
  h2 := (4,0,0,1,4)
  D := [[4, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_89_21 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨89, by decide⟩
  m := 1
  T1 := T147_89
  T2 := Q2.T147_89_2
  h1 := (4,0,1,2,4)
  h2 := (4,0,1,2,4)
  D := [[4, 0, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_89_22 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨89, by decide⟩
  m := 1
  T1 := T147_89
  T2 := Q2.T147_89_2
  h1 := (4,0,2,3,4)
  h2 := (4,0,2,3,4)
  D := [[4, 0, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_89_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨89, by decide⟩
  m := 1
  T1 := T147_89
  T2 := Q2.T147_89_2
  h1 := (4,0,3,4,4)
  h2 := (4,0,3,4,4)
  D := [[4, 0, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_89_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨89, by decide⟩
  m := 1
  T1 := T147_89
  T2 := Q2.T147_89_2
  h1 := (4,0,4,0,4)
  h2 := (4,0,4,0,4)
  D := [[4, 0, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_90_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨90, by decide⟩
  m := 1
  T1 := T147_90
  T2 := Q2.T147_90_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_90_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨90, by decide⟩
  m := 1
  T1 := T147_90
  T2 := Q2.T147_90_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
