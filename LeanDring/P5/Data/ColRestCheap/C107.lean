/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C043

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 106: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_146_53_1 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T146_53
  T2 := Q2.T146_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_53_2 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T146_53
  T2 := Q2.T146_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_53_3 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T146_53
  T2 := Q2.T146_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_53_4 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T146_53
  T2 := Q2.T146_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_53_5 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T146_53
  T2 := Q2.T146_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_53_10 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T146_53
  T2 := Q2.T146_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_53_15 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T146_53
  T2 := Q2.T146_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_53_20 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T146_53
  T2 := Q2.T146_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_54_0 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T146_54
  T2 := Q2.T146_54_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_54_1 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T146_54
  T2 := Q2.T146_54_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_54_2 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T146_54
  T2 := Q2.T146_54_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_54_3 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T146_54
  T2 := Q2.T146_54_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_54_4 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T146_54
  T2 := Q2.T146_54_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_54_5 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T146_54
  T2 := Q2.T146_54_2
  h1 := (1,0,0,4,4)
  h2 := (1,0,0,4,4)
  D := [[1, 0, 4, 0], [1, 0, 4, 0], [1, 0, 4, 0], [1, 0, 4, 0], [1, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_54_10 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T146_54
  T2 := Q2.T146_54_2
  h1 := (2,0,0,3,2)
  h2 := (2,0,0,3,2)
  D := [[2, 0, 3, 1], [2, 0, 3, 1], [2, 0, 3, 1], [2, 0, 3, 1], [2, 0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_54_15 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T146_54
  T2 := Q2.T146_54_2
  h1 := (3,0,0,2,4)
  h2 := (3,0,0,2,4)
  D := [[3, 0, 2, 3], [3, 0, 2, 3], [3, 0, 2, 3], [3, 0, 2, 3], [3, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_54_20 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T146_54
  T2 := Q2.T146_54_2
  h1 := (4,0,0,1,0)
  h2 := (4,0,0,1,0)
  D := [[4, 0, 1, 1], [4, 0, 1, 1], [4, 0, 1, 1], [4, 0, 1, 1], [4, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_110_0 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T146_110
  T2 := Q2.T146_110_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_110_1 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T146_110
  T2 := Q2.T146_110_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_110_2 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T146_110
  T2 := Q2.T146_110_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_110_3 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T146_110
  T2 := Q2.T146_110_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_110_4 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T146_110
  T2 := Q2.T146_110_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_110_5 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T146_110
  T2 := Q2.T146_110_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_110_10 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T146_110
  T2 := Q2.T146_110_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_110_15 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T146_110
  T2 := Q2.T146_110_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_110_20 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T146_110
  T2 := Q2.T146_110_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_110_25 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T146_110
  T2 := Q2.T146_110_2
  h1 := (0,1,0,0,0)
  h2 := (0,1,0,0,0)
  D := [[0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_110_50 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T146_110
  T2 := Q2.T146_110_2
  h1 := (0,2,0,0,0)
  h2 := (0,2,0,0,0)
  D := [[0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_110_75 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T146_110
  T2 := Q2.T146_110_2
  h1 := (0,3,0,0,0)
  h2 := (0,3,0,0,0)
  D := [[0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_110_100 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T146_110
  T2 := Q2.T146_110_2
  h1 := (0,4,0,0,0)
  h2 := (0,4,0,0,0)
  D := [[0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_111_0 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T146_111
  T2 := Q2.T146_111_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_111_1 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T146_111
  T2 := Q2.T146_111_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_111_2 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T146_111
  T2 := Q2.T146_111_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_111_3 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T146_111
  T2 := Q2.T146_111_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_111_4 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T146_111
  T2 := Q2.T146_111_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_111_5 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T146_111
  T2 := Q2.T146_111_2
  h1 := (1,4,0,4,0)
  h2 := (1,4,0,4,0)
  D := [[1, 4, 0, 0], [1, 4, 0, 1], [1, 4, 0, 2], [1, 4, 0, 3], [1, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_112_0 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T146_112
  T2 := Q2.T146_112_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_112_1 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T146_112
  T2 := Q2.T146_112_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_112_2 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T146_112
  T2 := Q2.T146_112_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_112_3 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T146_112
  T2 := Q2.T146_112_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_112_4 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T146_112
  T2 := Q2.T146_112_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_112_5 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T146_112
  T2 := Q2.T146_112_2
  h1 := (1,2,0,3,3)
  h2 := (1,2,0,3,3)
  D := [[1, 2, 1, 2], [1, 2, 1, 0], [1, 2, 1, 3], [1, 2, 1, 1], [1, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_112_10 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T146_112
  T2 := Q2.T146_112_2
  h1 := (2,4,0,3,4)
  h2 := (2,4,0,3,4)
  D := [[2, 4, 0, 0], [2, 4, 0, 1], [2, 4, 0, 2], [2, 4, 0, 3], [2, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_113_0 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T146_113
  T2 := Q2.T146_113_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_113_1 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T146_113
  T2 := Q2.T146_113_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_113_2 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T146_113
  T2 := Q2.T146_113_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_113_3 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T146_113
  T2 := Q2.T146_113_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_113_4 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T146_113
  T2 := Q2.T146_113_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_113_5 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T146_113
  T2 := Q2.T146_113_2
  h1 := (1,3,0,1,2)
  h2 := (1,3,0,1,2)
  D := [[1, 3, 3, 4], [1, 3, 3, 1], [1, 3, 3, 3], [1, 3, 3, 0], [1, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_114_0 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T146_114
  T2 := Q2.T146_114_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_114_1 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T146_114
  T2 := Q2.T146_114_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_114_2 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T146_114
  T2 := Q2.T146_114_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_114_3 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T146_114
  T2 := Q2.T146_114_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_114_4 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T146_114
  T2 := Q2.T146_114_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_114_5 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T146_114
  T2 := Q2.T146_114_2
  h1 := (1,1,0,0,0)
  h2 := (1,1,0,0,0)
  D := [[1, 1, 4, 1], [1, 1, 4, 0], [1, 1, 4, 4], [1, 1, 4, 3], [1, 1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_114_10 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T146_114
  T2 := Q2.T146_114_2
  h1 := (2,2,0,1,0)
  h2 := (2,2,0,1,0)
  D := [[2, 2, 2, 4], [2, 2, 2, 2], [2, 2, 2, 0], [2, 2, 2, 3], [2, 2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_114_15 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T146_114
  T2 := Q2.T146_114_2
  h1 := (3,3,0,3,1)
  h2 := (3,3,0,3,1)
  D := [[3, 3, 4, 0], [3, 3, 4, 2], [3, 3, 4, 4], [3, 3, 4, 1], [3, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_114_20 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T146_114
  T2 := Q2.T146_114_2
  h1 := (4,4,0,1,4)
  h2 := (4,4,0,1,4)
  D := [[4, 4, 0, 0], [4, 4, 0, 1], [4, 4, 0, 2], [4, 4, 0, 3], [4, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_115_0 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T146_115
  T2 := Q2.T146_115_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_146_115_1 : ColCert where
  rK := ⟨146, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T146_115
  T2 := Q2.T146_115_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
