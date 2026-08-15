/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C026

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 25: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_117_53_3 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T117_53
  T2 := Q2.T117_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_53_4 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T117_53
  T2 := Q2.T117_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_53_5 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T117_53
  T2 := Q2.T117_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_53_10 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T117_53
  T2 := Q2.T117_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_53_15 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T117_53
  T2 := Q2.T117_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_53_20 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T117_53
  T2 := Q2.T117_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_60_0 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T117_60
  T2 := Q2.T117_60_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_60_1 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T117_60
  T2 := Q2.T117_60_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 1, 0, 4], [0, 1, 0, 0], [0, 1, 0, 1], [0, 1, 0, 2], [0, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_60_2 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T117_60
  T2 := Q2.T117_60_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 2, 0, 3], [0, 2, 0, 0], [0, 2, 0, 2], [0, 2, 0, 4], [0, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_60_3 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T117_60
  T2 := Q2.T117_60_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 3, 0, 2], [0, 3, 0, 0], [0, 3, 0, 3], [0, 3, 0, 1], [0, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_60_4 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T117_60
  T2 := Q2.T117_60_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 4, 0, 1], [0, 4, 0, 0], [0, 4, 0, 4], [0, 4, 0, 3], [0, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_60_5 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T117_60
  T2 := Q2.T117_60_2
  h1 := (1,4,0,3,4)
  h2 := (1,4,0,3,4)
  D := [[1, 0, 0, 4], [1, 0, 4, 0], [1, 0, 3, 1], [1, 0, 2, 2], [1, 0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_60_6 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T117_60
  T2 := Q2.T117_60_2
  h1 := (1,4,1,3,4)
  h2 := (1,4,1,3,4)
  D := [[1, 1, 0, 4], [1, 1, 4, 1], [1, 1, 3, 3], [1, 1, 2, 0], [1, 1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_60_7 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T117_60
  T2 := Q2.T117_60_2
  h1 := (1,4,2,3,4)
  h2 := (1,4,2,3,4)
  D := [[1, 2, 0, 4], [1, 2, 4, 2], [1, 2, 3, 0], [1, 2, 2, 3], [1, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_60_8 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T117_60
  T2 := Q2.T117_60_2
  h1 := (1,4,3,3,4)
  h2 := (1,4,3,3,4)
  D := [[1, 3, 0, 4], [1, 3, 4, 3], [1, 3, 3, 2], [1, 3, 2, 1], [1, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_60_9 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T117_60
  T2 := Q2.T117_60_2
  h1 := (1,4,4,3,4)
  h2 := (1,4,4,3,4)
  D := [[1, 4, 0, 4], [1, 4, 4, 4], [1, 4, 3, 4], [1, 4, 2, 4], [1, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_60_10 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T117_60
  T2 := Q2.T117_60_2
  h1 := (2,3,0,0,2)
  h2 := (2,3,0,0,3)
  D := [[2, 0, 0, 3], [2, 0, 3, 1], [2, 0, 1, 4], [2, 0, 4, 2], [2, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_60_11 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T117_60
  T2 := Q2.T117_60_2
  h1 := (2,3,1,0,2)
  h2 := (2,3,1,0,3)
  D := [[2, 1, 0, 4], [2, 1, 3, 3], [2, 1, 1, 2], [2, 1, 4, 1], [2, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_60_12 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T117_60
  T2 := Q2.T117_60_2
  h1 := (2,3,2,0,2)
  h2 := (2,3,2,0,3)
  D := [[2, 2, 0, 0], [2, 2, 3, 0], [2, 2, 1, 0], [2, 2, 4, 0], [2, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_60_13 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T117_60
  T2 := Q2.T117_60_2
  h1 := (2,3,3,0,2)
  h2 := (2,3,3,0,3)
  D := [[2, 3, 0, 1], [2, 3, 3, 2], [2, 3, 1, 3], [2, 3, 4, 4], [2, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_60_14 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T117_60
  T2 := Q2.T117_60_2
  h1 := (2,3,4,0,2)
  h2 := (2,3,4,0,3)
  D := [[2, 4, 0, 2], [2, 4, 3, 4], [2, 4, 1, 1], [2, 4, 4, 3], [2, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_60_15 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T117_60
  T2 := Q2.T117_60_2
  h1 := (3,2,0,1,2)
  h2 := (3,2,0,1,4)
  D := [[3, 0, 0, 2], [3, 0, 2, 3], [3, 0, 4, 4], [3, 0, 1, 0], [3, 0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_60_16 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T117_60
  T2 := Q2.T117_60_2
  h1 := (3,2,1,1,2)
  h2 := (3,2,1,1,4)
  D := [[3, 1, 0, 4], [3, 1, 2, 1], [3, 1, 4, 3], [3, 1, 1, 0], [3, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_60_17 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T117_60
  T2 := Q2.T117_60_2
  h1 := (3,2,2,1,2)
  h2 := (3,2,2,1,4)
  D := [[3, 2, 0, 1], [3, 2, 2, 4], [3, 2, 4, 2], [3, 2, 1, 0], [3, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_60_18 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T117_60
  T2 := Q2.T117_60_2
  h1 := (3,2,3,1,2)
  h2 := (3,2,3,1,4)
  D := [[3, 3, 0, 3], [3, 3, 2, 2], [3, 3, 4, 1], [3, 3, 1, 0], [3, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_60_19 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T117_60
  T2 := Q2.T117_60_2
  h1 := (3,2,4,1,2)
  h2 := (3,2,4,1,4)
  D := [[3, 4, 0, 0], [3, 4, 2, 0], [3, 4, 4, 0], [3, 4, 1, 0], [3, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_60_20 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T117_60
  T2 := Q2.T117_60_2
  h1 := (4,1,0,1,3)
  h2 := (4,1,0,1,1)
  D := [[4, 0, 0, 1], [4, 0, 1, 1], [4, 0, 2, 1], [4, 0, 3, 1], [4, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_60_21 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T117_60
  T2 := Q2.T117_60_2
  h1 := (4,1,1,1,3)
  h2 := (4,1,1,1,1)
  D := [[4, 1, 0, 4], [4, 1, 1, 0], [4, 1, 2, 1], [4, 1, 3, 2], [4, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_60_22 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T117_60
  T2 := Q2.T117_60_2
  h1 := (4,1,2,1,3)
  h2 := (4,1,2,1,1)
  D := [[4, 2, 0, 2], [4, 2, 1, 4], [4, 2, 2, 1], [4, 2, 3, 3], [4, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_60_23 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T117_60
  T2 := Q2.T117_60_2
  h1 := (4,1,3,1,3)
  h2 := (4,1,3,1,1)
  D := [[4, 3, 0, 0], [4, 3, 1, 3], [4, 3, 2, 1], [4, 3, 3, 4], [4, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_60_24 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨60, by decide⟩
  m := 5
  T1 := T117_60
  T2 := Q2.T117_60_2
  h1 := (4,1,4,1,3)
  h2 := (4,1,4,1,1)
  D := [[4, 4, 0, 3], [4, 4, 1, 2], [4, 4, 2, 1], [4, 4, 3, 0], [4, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_61_0 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨61, by decide⟩
  m := 5
  T1 := T117_61
  T2 := Q2.T117_61_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_61_1 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨61, by decide⟩
  m := 5
  T1 := T117_61
  T2 := Q2.T117_61_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 1, 4, 4], [0, 1, 4, 0], [0, 1, 4, 1], [0, 1, 4, 2], [0, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_61_2 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨61, by decide⟩
  m := 5
  T1 := T117_61
  T2 := Q2.T117_61_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 2, 3, 3], [0, 2, 3, 0], [0, 2, 3, 2], [0, 2, 3, 4], [0, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_61_3 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨61, by decide⟩
  m := 5
  T1 := T117_61
  T2 := Q2.T117_61_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 3, 2, 2], [0, 3, 2, 0], [0, 3, 2, 3], [0, 3, 2, 1], [0, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_61_4 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨61, by decide⟩
  m := 5
  T1 := T117_61
  T2 := Q2.T117_61_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 4, 1, 1], [0, 4, 1, 0], [0, 4, 1, 4], [0, 4, 1, 3], [0, 4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_61_5 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨61, by decide⟩
  m := 5
  T1 := T117_61
  T2 := Q2.T117_61_2
  h1 := (1,4,0,3,1)
  h2 := (1,4,0,3,1)
  D := [[1, 0, 0, 1], [1, 0, 4, 2], [1, 0, 3, 3], [1, 0, 2, 4], [1, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_61_6 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨61, by decide⟩
  m := 5
  T1 := T117_61
  T2 := Q2.T117_61_2
  h1 := (1,4,1,2,1)
  h2 := (1,4,1,2,1)
  D := [[1, 1, 4, 2], [1, 1, 3, 4], [1, 1, 2, 1], [1, 1, 1, 3], [1, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_61_7 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨61, by decide⟩
  m := 5
  T1 := T117_61
  T2 := Q2.T117_61_2
  h1 := (1,4,2,1,1)
  h2 := (1,4,2,1,1)
  D := [[1, 2, 3, 3], [1, 2, 2, 1], [1, 2, 1, 4], [1, 2, 0, 2], [1, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_61_8 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨61, by decide⟩
  m := 5
  T1 := T117_61
  T2 := Q2.T117_61_2
  h1 := (1,4,3,0,1)
  h2 := (1,4,3,0,1)
  D := [[1, 3, 2, 4], [1, 3, 1, 3], [1, 3, 0, 2], [1, 3, 4, 1], [1, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_61_9 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨61, by decide⟩
  m := 5
  T1 := T117_61
  T2 := Q2.T117_61_2
  h1 := (1,4,4,4,1)
  h2 := (1,4,4,4,1)
  D := [[1, 4, 1, 0], [1, 4, 0, 0], [1, 4, 4, 0], [1, 4, 3, 0], [1, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_61_10 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨61, by decide⟩
  m := 5
  T1 := T117_61
  T2 := Q2.T117_61_2
  h1 := (2,3,0,0,1)
  h2 := (2,3,0,0,2)
  D := [[2, 0, 0, 2], [2, 0, 3, 0], [2, 0, 1, 3], [2, 0, 4, 1], [2, 0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_61_11 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨61, by decide⟩
  m := 5
  T1 := T117_61
  T2 := Q2.T117_61_2
  h1 := (2,3,1,4,1)
  h2 := (2,3,1,4,2)
  D := [[2, 1, 4, 0], [2, 1, 2, 4], [2, 1, 0, 3], [2, 1, 3, 2], [2, 1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_61_12 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨61, by decide⟩
  m := 5
  T1 := T117_61
  T2 := Q2.T117_61_2
  h1 := (2,3,2,3,1)
  h2 := (2,3,2,3,2)
  D := [[2, 2, 3, 3], [2, 2, 1, 3], [2, 2, 4, 3], [2, 2, 2, 3], [2, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_61_13 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨61, by decide⟩
  m := 5
  T1 := T117_61
  T2 := Q2.T117_61_2
  h1 := (2,3,3,2,1)
  h2 := (2,3,3,2,2)
  D := [[2, 3, 2, 1], [2, 3, 0, 2], [2, 3, 3, 3], [2, 3, 1, 4], [2, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_61_14 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨61, by decide⟩
  m := 5
  T1 := T117_61
  T2 := Q2.T117_61_2
  h1 := (2,3,4,1,1)
  h2 := (2,3,4,1,2)
  D := [[2, 4, 1, 4], [2, 4, 4, 1], [2, 4, 2, 3], [2, 4, 0, 0], [2, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_61_15 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨61, by decide⟩
  m := 5
  T1 := T117_61
  T2 := Q2.T117_61_2
  h1 := (3,2,0,1,3)
  h2 := (3,2,0,1,0)
  D := [[3, 0, 0, 3], [3, 0, 2, 4], [3, 0, 4, 0], [3, 0, 1, 1], [3, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_61_16 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨61, by decide⟩
  m := 5
  T1 := T117_61
  T2 := Q2.T117_61_2
  h1 := (3,2,1,0,3)
  h2 := (3,2,1,0,0)
  D := [[3, 1, 4, 3], [3, 1, 1, 0], [3, 1, 3, 2], [3, 1, 0, 4], [3, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_61_17 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨61, by decide⟩
  m := 5
  T1 := T117_61
  T2 := Q2.T117_61_2
  h1 := (3,2,2,4,3)
  h2 := (3,2,2,4,0)
  D := [[3, 2, 3, 3], [3, 2, 0, 1], [3, 2, 2, 4], [3, 2, 4, 2], [3, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_61_18 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨61, by decide⟩
  m := 5
  T1 := T117_61
  T2 := Q2.T117_61_2
  h1 := (3,2,3,3,3)
  h2 := (3,2,3,3,0)
  D := [[3, 3, 2, 3], [3, 3, 4, 2], [3, 3, 1, 1], [3, 3, 3, 0], [3, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_61_19 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨61, by decide⟩
  m := 5
  T1 := T117_61
  T2 := Q2.T117_61_2
  h1 := (3,2,4,2,3)
  h2 := (3,2,4,2,0)
  D := [[3, 4, 1, 3], [3, 4, 3, 3], [3, 4, 0, 3], [3, 4, 2, 3], [3, 4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_61_20 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨61, by decide⟩
  m := 5
  T1 := T117_61
  T2 := Q2.T117_61_2
  h1 := (4,1,0,1,1)
  h2 := (4,1,0,1,4)
  D := [[4, 0, 0, 4], [4, 0, 1, 4], [4, 0, 2, 4], [4, 0, 3, 4], [4, 0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_61_21 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨61, by decide⟩
  m := 5
  T1 := T117_61
  T2 := Q2.T117_61_2
  h1 := (4,1,1,0,1)
  h2 := (4,1,1,0,4)
  D := [[4, 1, 4, 1], [4, 1, 0, 2], [4, 1, 1, 3], [4, 1, 2, 4], [4, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_61_22 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨61, by decide⟩
  m := 5
  T1 := T117_61
  T2 := Q2.T117_61_2
  h1 := (4,1,2,4,1)
  h2 := (4,1,2,4,4)
  D := [[4, 2, 3, 3], [4, 2, 4, 0], [4, 2, 0, 2], [4, 2, 1, 4], [4, 2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_61_23 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨61, by decide⟩
  m := 5
  T1 := T117_61
  T2 := Q2.T117_61_2
  h1 := (4,1,3,3,1)
  h2 := (4,1,3,3,4)
  D := [[4, 3, 2, 0], [4, 3, 3, 3], [4, 3, 4, 1], [4, 3, 0, 4], [4, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_61_24 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨61, by decide⟩
  m := 5
  T1 := T117_61
  T2 := Q2.T117_61_2
  h1 := (4,1,4,2,1)
  h2 := (4,1,4,2,4)
  D := [[4, 4, 1, 2], [4, 4, 2, 1], [4, 4, 3, 0], [4, 4, 4, 4], [4, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_62_0 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨62, by decide⟩
  m := 5
  T1 := T117_62
  T2 := Q2.T117_62_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_62_1 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨62, by decide⟩
  m := 5
  T1 := T117_62
  T2 := Q2.T117_62_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 1, 3, 4], [0, 1, 3, 0], [0, 1, 3, 1], [0, 1, 3, 2], [0, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_62_2 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨62, by decide⟩
  m := 5
  T1 := T117_62
  T2 := Q2.T117_62_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 2, 1, 3], [0, 2, 1, 0], [0, 2, 1, 2], [0, 2, 1, 4], [0, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_62_3 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨62, by decide⟩
  m := 5
  T1 := T117_62
  T2 := Q2.T117_62_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 3, 4, 2], [0, 3, 4, 0], [0, 3, 4, 3], [0, 3, 4, 1], [0, 3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
