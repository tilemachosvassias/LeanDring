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
rest tier, chunk 126: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_147_111_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨111, by decide⟩
  m := 1
  T1 := T147_111
  T2 := Q2.T147_111_2
  h1 := (1,4,0,4,0)
  h2 := (1,4,0,4,0)
  D := [[1, 4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_112_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨112, by decide⟩
  m := 1
  T1 := T147_112
  T2 := Q2.T147_112_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_112_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨112, by decide⟩
  m := 1
  T1 := T147_112
  T2 := Q2.T147_112_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_112_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨112, by decide⟩
  m := 1
  T1 := T147_112
  T2 := Q2.T147_112_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_112_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨112, by decide⟩
  m := 1
  T1 := T147_112
  T2 := Q2.T147_112_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_112_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨112, by decide⟩
  m := 1
  T1 := T147_112
  T2 := Q2.T147_112_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_112_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨112, by decide⟩
  m := 1
  T1 := T147_112
  T2 := Q2.T147_112_2
  h1 := (1,2,0,3,3)
  h2 := (1,2,0,3,3)
  D := [[1, 2, 0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_112_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨112, by decide⟩
  m := 1
  T1 := T147_112
  T2 := Q2.T147_112_2
  h1 := (2,4,0,3,4)
  h2 := (2,4,0,3,4)
  D := [[2, 4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_113_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨113, by decide⟩
  m := 1
  T1 := T147_113
  T2 := Q2.T147_113_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_113_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨113, by decide⟩
  m := 1
  T1 := T147_113
  T2 := Q2.T147_113_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_113_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨113, by decide⟩
  m := 1
  T1 := T147_113
  T2 := Q2.T147_113_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_113_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨113, by decide⟩
  m := 1
  T1 := T147_113
  T2 := Q2.T147_113_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_113_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨113, by decide⟩
  m := 1
  T1 := T147_113
  T2 := Q2.T147_113_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_113_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨113, by decide⟩
  m := 1
  T1 := T147_113
  T2 := Q2.T147_113_2
  h1 := (1,3,0,1,2)
  h2 := (1,3,0,1,2)
  D := [[1, 3, 0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_114_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨114, by decide⟩
  m := 1
  T1 := T147_114
  T2 := Q2.T147_114_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_114_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨114, by decide⟩
  m := 1
  T1 := T147_114
  T2 := Q2.T147_114_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_114_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨114, by decide⟩
  m := 1
  T1 := T147_114
  T2 := Q2.T147_114_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_114_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨114, by decide⟩
  m := 1
  T1 := T147_114
  T2 := Q2.T147_114_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_114_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨114, by decide⟩
  m := 1
  T1 := T147_114
  T2 := Q2.T147_114_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_114_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨114, by decide⟩
  m := 1
  T1 := T147_114
  T2 := Q2.T147_114_2
  h1 := (1,1,0,0,0)
  h2 := (1,1,0,0,0)
  D := [[1, 1, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_114_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨114, by decide⟩
  m := 1
  T1 := T147_114
  T2 := Q2.T147_114_2
  h1 := (2,2,0,1,0)
  h2 := (2,2,0,1,0)
  D := [[2, 2, 0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_114_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨114, by decide⟩
  m := 1
  T1 := T147_114
  T2 := Q2.T147_114_2
  h1 := (3,3,0,3,1)
  h2 := (3,3,0,3,1)
  D := [[3, 3, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_114_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨114, by decide⟩
  m := 1
  T1 := T147_114
  T2 := Q2.T147_114_2
  h1 := (4,4,0,1,4)
  h2 := (4,4,0,1,4)
  D := [[4, 4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_115_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨115, by decide⟩
  m := 1
  T1 := T147_115
  T2 := Q2.T147_115_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_115_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨115, by decide⟩
  m := 1
  T1 := T147_115
  T2 := Q2.T147_115_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_115_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨115, by decide⟩
  m := 1
  T1 := T147_115
  T2 := Q2.T147_115_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_115_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨115, by decide⟩
  m := 1
  T1 := T147_115
  T2 := Q2.T147_115_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_115_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨115, by decide⟩
  m := 1
  T1 := T147_115
  T2 := Q2.T147_115_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_115_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨115, by decide⟩
  m := 1
  T1 := T147_115
  T2 := Q2.T147_115_2
  h1 := (1,0,0,0,0)
  h2 := (1,0,0,0,0)
  D := [[1, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_115_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨115, by decide⟩
  m := 1
  T1 := T147_115
  T2 := Q2.T147_115_2
  h1 := (2,0,0,0,0)
  h2 := (2,0,0,0,0)
  D := [[2, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_115_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨115, by decide⟩
  m := 1
  T1 := T147_115
  T2 := Q2.T147_115_2
  h1 := (3,0,0,0,0)
  h2 := (3,0,0,0,0)
  D := [[3, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_115_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨115, by decide⟩
  m := 1
  T1 := T147_115
  T2 := Q2.T147_115_2
  h1 := (4,0,0,0,0)
  h2 := (4,0,0,0,0)
  D := [[4, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 0, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 0, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 0, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 0, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_11 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 0, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_12 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 0, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_13 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 0, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_14 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 0, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_16 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 0, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_17 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 0, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_18 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 0, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_19 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 0, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_21 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 0, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_22 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,0,4,2,0)
  h2 := (0,0,4,2,0)
  D := [[0, 0, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 0, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 0, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_25 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,1,0,0,0)
  h2 := (0,1,0,0,0)
  D := [[0, 1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_30 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,1,1,0,0)
  h2 := (0,1,1,0,0)
  D := [[0, 1, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_116_35 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨116, by decide⟩
  m := 1
  T1 := T147_116
  T2 := Q2.T147_116_2
  h1 := (0,1,2,0,0)
  h2 := (0,1,2,0,0)
  D := [[0, 1, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
