/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C038
import LeanDring.P5.Data.EntryK.C039

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 85: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_139_139_9 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨139, by decide⟩
  m := 5
  T1 := T139_139
  T2 := Q2.T139_139_2
  h1 := (1,4,3,1,4)
  h2 := (1,4,3,1,0)
  D := [[1, 4, 1, 2], [1, 4, 1, 3], [1, 4, 1, 4], [1, 4, 1, 0], [1, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_139_10 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨139, by decide⟩
  m := 5
  T1 := T139_139
  T2 := Q2.T139_139_2
  h1 := (2,0,2,2,4)
  h2 := (2,0,2,2,3)
  D := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_139_11 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨139, by decide⟩
  m := 5
  T1 := T139_139
  T2 := Q2.T139_139_2
  h1 := (2,1,0,2,3)
  h2 := (2,1,0,2,3)
  D := [[2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3], [2, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_139_12 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨139, by decide⟩
  m := 5
  T1 := T139_139
  T2 := Q2.T139_139_2
  h1 := (2,2,3,2,0)
  h2 := (2,2,3,2,1)
  D := [[2, 2, 1, 2], [2, 2, 1, 0], [2, 2, 1, 3], [2, 2, 1, 1], [2, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_139_13 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨139, by decide⟩
  m := 5
  T1 := T139_139
  T2 := Q2.T139_139_2
  h1 := (2,3,1,2,0)
  h2 := (2,3,1,2,2)
  D := [[2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_139_14 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨139, by decide⟩
  m := 5
  T1 := T139_139
  T2 := Q2.T139_139_2
  h1 := (2,4,4,2,3)
  h2 := (2,4,4,2,1)
  D := [[2, 4, 2, 4], [2, 4, 2, 0], [2, 4, 2, 1], [2, 4, 2, 2], [2, 4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_139_15 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨139, by decide⟩
  m := 5
  T1 := T139_139
  T2 := Q2.T139_139_2
  h1 := (3,0,3,3,0)
  h2 := (3,0,3,3,1)
  D := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_139_16 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨139, by decide⟩
  m := 5
  T1 := T139_139
  T2 := Q2.T139_139_2
  h1 := (3,1,1,3,0)
  h2 := (3,1,1,3,2)
  D := [[3, 1, 2, 0], [3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2], [3, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_139_17 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨139, by decide⟩
  m := 5
  T1 := T139_139
  T2 := Q2.T139_139_2
  h1 := (3,2,4,3,3)
  h2 := (3,2,4,3,1)
  D := [[3, 2, 4, 0], [3, 2, 4, 3], [3, 2, 4, 1], [3, 2, 4, 4], [3, 2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_139_18 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨139, by decide⟩
  m := 5
  T1 := T139_139
  T2 := Q2.T139_139_2
  h1 := (3,3,2,3,4)
  h2 := (3,3,2,3,3)
  D := [[3, 3, 1, 0], [3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_139_19 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨139, by decide⟩
  m := 5
  T1 := T139_139
  T2 := Q2.T139_139_2
  h1 := (3,4,0,3,3)
  h2 := (3,4,0,3,3)
  D := [[3, 4, 3, 0], [3, 4, 3, 1], [3, 4, 3, 2], [3, 4, 3, 3], [3, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_139_20 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨139, by decide⟩
  m := 5
  T1 := T139_139
  T2 := Q2.T139_139_2
  h1 := (4,0,4,4,2)
  h2 := (4,0,4,4,0)
  D := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_139_21 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨139, by decide⟩
  m := 5
  T1 := T139_139
  T2 := Q2.T139_139_2
  h1 := (4,1,2,4,3)
  h2 := (4,1,2,4,2)
  D := [[4, 1, 1, 0], [4, 1, 1, 4], [4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_139_22 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨139, by decide⟩
  m := 5
  T1 := T139_139
  T2 := Q2.T139_139_2
  h1 := (4,2,0,4,2)
  h2 := (4,2,0,4,2)
  D := [[4, 2, 2, 0], [4, 2, 2, 3], [4, 2, 2, 1], [4, 2, 2, 4], [4, 2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_139_23 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨139, by decide⟩
  m := 5
  T1 := T139_139
  T2 := Q2.T139_139_2
  h1 := (4,3,3,4,4)
  h2 := (4,3,3,4,0)
  D := [[4, 3, 3, 0], [4, 3, 3, 2], [4, 3, 3, 4], [4, 3, 3, 1], [4, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_139_24 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨139, by decide⟩
  m := 5
  T1 := T139_139
  T2 := Q2.T139_139_2
  h1 := (4,4,1,4,4)
  h2 := (4,4,1,4,1)
  D := [[4, 4, 4, 0], [4, 4, 4, 1], [4, 4, 4, 2], [4, 4, 4, 3], [4, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_0_0 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨0, by decide⟩
  m := 5
  T1 := T140_0
  T2 := Q2.T140_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_5_0 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T140_5
  T2 := Q2.T140_5_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_10_0 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T140_10
  T2 := Q2.T140_10_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_10_1 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T140_10
  T2 := Q2.T140_10_2
  h1 := (0,0,0,1,4)
  h2 := (0,0,0,1,4)
  D := [[0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_10_2 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T140_10
  T2 := Q2.T140_10_2
  h1 := (0,0,0,2,3)
  h2 := (0,0,0,2,3)
  D := [[0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_10_3 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T140_10
  T2 := Q2.T140_10_2
  h1 := (0,0,0,3,2)
  h2 := (0,0,0,3,2)
  D := [[0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_10_4 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T140_10
  T2 := Q2.T140_10_2
  h1 := (0,0,0,4,1)
  h2 := (0,0,0,4,1)
  D := [[0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_12_0 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T140_12
  T2 := Q2.T140_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_12_1 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T140_12
  T2 := Q2.T140_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_12_2 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T140_12
  T2 := Q2.T140_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_12_3 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T140_12
  T2 := Q2.T140_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_12_4 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T140_12
  T2 := Q2.T140_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_23_0 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T140_23
  T2 := Q2.T140_23_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_23_1 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T140_23
  T2 := Q2.T140_23_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_23_2 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T140_23
  T2 := Q2.T140_23_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_23_3 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T140_23
  T2 := Q2.T140_23_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_23_4 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T140_23
  T2 := Q2.T140_23_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_28_0 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T140_28
  T2 := Q2.T140_28_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_28_1 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T140_28
  T2 := Q2.T140_28_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_28_2 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T140_28
  T2 := Q2.T140_28_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_28_3 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T140_28
  T2 := Q2.T140_28_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_28_4 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T140_28
  T2 := Q2.T140_28_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_28_5 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T140_28
  T2 := Q2.T140_28_2
  h1 := (0,1,4,4,2)
  h2 := (0,1,4,4,0)
  D := [[0, 1, 4, 0], [0, 1, 4, 4], [0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_28_10 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T140_28
  T2 := Q2.T140_28_2
  h1 := (0,2,3,3,3)
  h2 := (0,2,3,3,4)
  D := [[0, 2, 3, 0], [0, 2, 3, 3], [0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_28_15 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T140_28
  T2 := Q2.T140_28_2
  h1 := (0,3,2,2,3)
  h2 := (0,3,2,2,2)
  D := [[0, 3, 2, 0], [0, 3, 2, 2], [0, 3, 2, 4], [0, 3, 2, 1], [0, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_28_20 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T140_28
  T2 := Q2.T140_28_2
  h1 := (0,4,1,1,2)
  h2 := (0,4,1,1,4)
  D := [[0, 4, 1, 0], [0, 4, 1, 1], [0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_35_0 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T140_35
  T2 := Q2.T140_35_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_35_1 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T140_35
  T2 := Q2.T140_35_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_35_2 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T140_35
  T2 := Q2.T140_35_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_35_3 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T140_35
  T2 := Q2.T140_35_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_35_4 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T140_35
  T2 := Q2.T140_35_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_39_0 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T140_39
  T2 := Q2.T140_39_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_39_1 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T140_39
  T2 := Q2.T140_39_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_39_2 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T140_39
  T2 := Q2.T140_39_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_39_3 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T140_39
  T2 := Q2.T140_39_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_39_4 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T140_39
  T2 := Q2.T140_39_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_39_15 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T140_39
  T2 := Q2.T140_39_2
  h1 := (3,2,1,1,0)
  h2 := (3,2,1,1,2)
  D := [[3, 2, 0, 0], [3, 2, 0, 3], [3, 2, 0, 1], [3, 2, 0, 4], [3, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_46_0 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T140_46
  T2 := Q2.T140_46_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_46_1 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T140_46
  T2 := Q2.T140_46_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_46_2 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T140_46
  T2 := Q2.T140_46_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_46_3 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T140_46
  T2 := Q2.T140_46_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_46_4 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T140_46
  T2 := Q2.T140_46_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_46_5 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T140_46
  T2 := Q2.T140_46_2
  h1 := (1,3,3,0,2)
  h2 := (1,3,3,0,3)
  D := [[1, 3, 2, 0], [1, 3, 2, 2], [1, 3, 2, 4], [1, 3, 2, 1], [1, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_52_0 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T140_52
  T2 := Q2.T140_52_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
