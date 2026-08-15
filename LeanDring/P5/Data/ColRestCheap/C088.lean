/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C039
import LeanDring.P5.Data.EntryK.C040

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 87: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_140_140_8 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨140, by decide⟩
  m := 5
  T1 := T140_140
  T2 := Q2.T140_140_2
  h1 := (1,3,3,0,3)
  h2 := (1,3,3,0,4)
  D := [[1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0], [1, 3, 2, 2], [1, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_140_9 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨140, by decide⟩
  m := 5
  T1 := T140_140
  T2 := Q2.T140_140_2
  h1 := (1,4,2,0,3)
  h2 := (1,4,2,0,2)
  D := [[1, 4, 1, 3], [1, 4, 1, 4], [1, 4, 1, 0], [1, 4, 1, 1], [1, 4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_140_10 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨140, by decide⟩
  m := 5
  T1 := T140_140
  T2 := Q2.T140_140_2
  h1 := (2,0,2,0,4)
  h2 := (2,0,2,0,3)
  D := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_140_11 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨140, by decide⟩
  m := 5
  T1 := T140_140
  T2 := Q2.T140_140_2
  h1 := (2,1,1,0,3)
  h2 := (2,1,1,0,0)
  D := [[2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3], [2, 1, 3, 2], [2, 1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_140_12 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨140, by decide⟩
  m := 5
  T1 := T140_140
  T2 := Q2.T140_140_2
  h1 := (2,2,0,0,1)
  h2 := (2,2,0,0,1)
  D := [[2, 2, 1, 0], [2, 2, 1, 3], [2, 2, 1, 1], [2, 2, 1, 4], [2, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_140_13 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨140, by decide⟩
  m := 5
  T1 := T140_140
  T2 := Q2.T140_140_2
  h1 := (2,3,4,0,3)
  h2 := (2,3,4,0,1)
  D := [[2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1], [2, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_140_14 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨140, by decide⟩
  m := 5
  T1 := T140_140
  T2 := Q2.T140_140_2
  h1 := (2,4,3,0,4)
  h2 := (2,4,3,0,0)
  D := [[2, 4, 2, 0], [2, 4, 2, 1], [2, 4, 2, 2], [2, 4, 2, 3], [2, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_140_15 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨140, by decide⟩
  m := 5
  T1 := T140_140
  T2 := Q2.T140_140_2
  h1 := (3,0,3,0,1)
  h2 := (3,0,3,0,2)
  D := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_140_16 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨140, by decide⟩
  m := 5
  T1 := T140_140
  T2 := Q2.T140_140_2
  h1 := (3,1,2,0,1)
  h2 := (3,1,2,0,0)
  D := [[3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2], [3, 1, 2, 1], [3, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_140_17 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨140, by decide⟩
  m := 5
  T1 := T140_140
  T2 := Q2.T140_140_2
  h1 := (3,2,1,0,0)
  h2 := (3,2,1,0,2)
  D := [[3, 2, 4, 3], [3, 2, 4, 1], [3, 2, 4, 4], [3, 2, 4, 2], [3, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_140_18 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨140, by decide⟩
  m := 5
  T1 := T140_140
  T2 := Q2.T140_140_2
  h1 := (3,3,0,0,3)
  h2 := (3,3,0,0,3)
  D := [[3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_140_19 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨140, by decide⟩
  m := 5
  T1 := T140_140
  T2 := Q2.T140_140_2
  h1 := (3,4,4,0,0)
  h2 := (3,4,4,0,3)
  D := [[3, 4, 3, 1], [3, 4, 3, 2], [3, 4, 3, 3], [3, 4, 3, 4], [3, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_140_20 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨140, by decide⟩
  m := 5
  T1 := T140_140
  T2 := Q2.T140_140_2
  h1 := (4,0,4,0,3)
  h2 := (4,0,4,0,1)
  D := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_140_21 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨140, by decide⟩
  m := 5
  T1 := T140_140
  T2 := Q2.T140_140_2
  h1 := (4,1,3,0,4)
  h2 := (4,1,3,0,0)
  D := [[4, 1, 1, 4], [4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_140_22 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨140, by decide⟩
  m := 5
  T1 := T140_140
  T2 := Q2.T140_140_2
  h1 := (4,2,2,0,4)
  h2 := (4,2,2,0,3)
  D := [[4, 2, 2, 3], [4, 2, 2, 1], [4, 2, 2, 4], [4, 2, 2, 2], [4, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_140_23 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨140, by decide⟩
  m := 5
  T1 := T140_140
  T2 := Q2.T140_140_2
  h1 := (4,3,1,0,3)
  h2 := (4,3,1,0,0)
  D := [[4, 3, 3, 2], [4, 3, 3, 4], [4, 3, 3, 1], [4, 3, 3, 3], [4, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_140_24 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨140, by decide⟩
  m := 5
  T1 := T140_140
  T2 := Q2.T140_140_2
  h1 := (4,4,0,0,1)
  h2 := (4,4,0,0,1)
  D := [[4, 4, 4, 1], [4, 4, 4, 2], [4, 4, 4, 3], [4, 4, 4, 4], [4, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_0_0 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨0, by decide⟩
  m := 5
  T1 := T141_0
  T2 := Q2.T141_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_1_0 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨1, by decide⟩
  m := 5
  T1 := T141_1
  T2 := Q2.T141_1_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_1_1 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨1, by decide⟩
  m := 5
  T1 := T141_1
  T2 := Q2.T141_1_2
  h1 := (0,0,1,4,4)
  h2 := (0,0,1,4,4)
  D := [[0, 1, 4, 4], [0, 1, 4, 0], [0, 1, 4, 1], [0, 1, 4, 2], [0, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_1_2 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨1, by decide⟩
  m := 5
  T1 := T141_1
  T2 := Q2.T141_1_2
  h1 := (0,0,2,3,3)
  h2 := (0,0,2,3,3)
  D := [[0, 2, 3, 3], [0, 2, 3, 0], [0, 2, 3, 2], [0, 2, 3, 4], [0, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_1_3 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨1, by decide⟩
  m := 5
  T1 := T141_1
  T2 := Q2.T141_1_2
  h1 := (0,0,3,2,2)
  h2 := (0,0,3,2,2)
  D := [[0, 3, 2, 2], [0, 3, 2, 0], [0, 3, 2, 3], [0, 3, 2, 1], [0, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_1_4 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨1, by decide⟩
  m := 5
  T1 := T141_1
  T2 := Q2.T141_1_2
  h1 := (0,0,4,1,1)
  h2 := (0,0,4,1,1)
  D := [[0, 4, 1, 1], [0, 4, 1, 0], [0, 4, 1, 4], [0, 4, 1, 3], [0, 4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_2_0 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T141_2
  T2 := Q2.T141_2_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_2_1 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T141_2
  T2 := Q2.T141_2_2
  h1 := (1,0,4,1,0)
  h2 := (1,0,4,1,0)
  D := [[1, 4, 1, 4], [1, 4, 0, 4], [1, 4, 4, 4], [1, 4, 3, 4], [1, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_2_2 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T141_2
  T2 := Q2.T141_2_2
  h1 := (2,0,3,2,1)
  h2 := (2,0,3,2,1)
  D := [[2, 3, 2, 2], [2, 3, 0, 3], [2, 3, 3, 4], [2, 3, 1, 0], [2, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_2_3 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T141_2
  T2 := Q2.T141_2_2
  h1 := (3,0,2,3,3)
  h2 := (3,0,2,3,3)
  D := [[3, 2, 3, 4], [3, 2, 0, 2], [3, 2, 2, 0], [3, 2, 4, 3], [3, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_2_4 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T141_2
  T2 := Q2.T141_2_2
  h1 := (4,0,1,4,1)
  h2 := (4,0,1,4,1)
  D := [[4, 1, 4, 0], [4, 1, 0, 1], [4, 1, 1, 2], [4, 1, 2, 3], [4, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_3_0 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T141_3
  T2 := Q2.T141_3_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_3_1 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T141_3
  T2 := Q2.T141_3_2
  h1 := (1,0,2,3,1)
  h2 := (1,0,2,3,1)
  D := [[1, 2, 3, 3], [1, 2, 2, 1], [1, 2, 1, 4], [1, 2, 0, 2], [1, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_3_2 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T141_3
  T2 := Q2.T141_3_2
  h1 := (2,0,4,1,0)
  h2 := (2,0,4,1,0)
  D := [[2, 4, 1, 3], [2, 4, 4, 0], [2, 4, 2, 2], [2, 4, 0, 4], [2, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_3_3 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T141_3
  T2 := Q2.T141_3_2
  h1 := (3,0,1,4,2)
  h2 := (3,0,1,4,2)
  D := [[3, 1, 4, 0], [3, 1, 1, 2], [3, 1, 3, 4], [3, 1, 0, 1], [3, 1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_3_4 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T141_3
  T2 := Q2.T141_3_2
  h1 := (4,0,3,2,2)
  h2 := (4,0,3,2,2)
  D := [[4, 3, 2, 4], [4, 3, 3, 2], [4, 3, 4, 0], [4, 3, 0, 3], [4, 3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_4_0 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T141_4
  T2 := Q2.T141_4_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_4_1 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T141_4
  T2 := Q2.T141_4_2
  h1 := (1,0,3,2,3)
  h2 := (1,0,3,2,3)
  D := [[1, 3, 2, 1], [1, 3, 1, 0], [1, 3, 0, 4], [1, 3, 4, 3], [1, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_4_2 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T141_4
  T2 := Q2.T141_4_2
  h1 := (2,0,1,4,3)
  h2 := (2,0,1,4,3)
  D := [[2, 1, 4, 0], [2, 1, 2, 4], [2, 1, 0, 3], [2, 1, 3, 2], [2, 1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_4_3 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T141_4
  T2 := Q2.T141_4_2
  h1 := (3,0,4,1,0)
  h2 := (3,0,4,1,0)
  D := [[3, 4, 1, 2], [3, 4, 3, 2], [3, 4, 0, 2], [3, 4, 2, 2], [3, 4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_4_4 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T141_4
  T2 := Q2.T141_4_2
  h1 := (4,0,2,3,4)
  h2 := (4,0,2,3,4)
  D := [[4, 2, 3, 2], [4, 2, 4, 4], [4, 2, 0, 1], [4, 2, 1, 3], [4, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_5_0 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T141_5
  T2 := Q2.T141_5_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_5_1 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T141_5
  T2 := Q2.T141_5_2
  h1 := (1,0,1,4,4)
  h2 := (1,0,1,4,4)
  D := [[1, 1, 4, 0], [1, 1, 3, 2], [1, 1, 2, 4], [1, 1, 1, 1], [1, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_5_2 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T141_5
  T2 := Q2.T141_5_2
  h1 := (2,0,2,3,2)
  h2 := (2,0,2,3,2)
  D := [[2, 2, 3, 1], [2, 2, 1, 1], [2, 2, 4, 1], [2, 2, 2, 1], [2, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_5_3 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T141_5
  T2 := Q2.T141_5_2
  h1 := (3,0,3,2,4)
  h2 := (3,0,3,2,4)
  D := [[3, 3, 2, 3], [3, 3, 4, 2], [3, 3, 1, 1], [3, 3, 3, 0], [3, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_5_4 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T141_5
  T2 := Q2.T141_5_2
  h1 := (4,0,4,1,0)
  h2 := (4,0,4,1,0)
  D := [[4, 4, 1, 1], [4, 4, 2, 0], [4, 4, 3, 4], [4, 4, 4, 3], [4, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_6_0 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨6, by decide⟩
  m := 5
  T1 := T141_6
  T2 := Q2.T141_6_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_6_1 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨6, by decide⟩
  m := 5
  T1 := T141_6
  T2 := Q2.T141_6_2
  h1 := (0,0,1,2,4)
  h2 := (0,0,1,2,4)
  D := [[0, 1, 2, 4], [0, 1, 2, 0], [0, 1, 2, 1], [0, 1, 2, 2], [0, 1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_6_2 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨6, by decide⟩
  m := 5
  T1 := T141_6
  T2 := Q2.T141_6_2
  h1 := (0,0,2,4,3)
  h2 := (0,0,2,4,3)
  D := [[0, 2, 4, 3], [0, 2, 4, 0], [0, 2, 4, 2], [0, 2, 4, 4], [0, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_6_3 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨6, by decide⟩
  m := 5
  T1 := T141_6
  T2 := Q2.T141_6_2
  h1 := (0,0,3,1,2)
  h2 := (0,0,3,1,2)
  D := [[0, 3, 1, 2], [0, 3, 1, 0], [0, 3, 1, 3], [0, 3, 1, 1], [0, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_6_4 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨6, by decide⟩
  m := 5
  T1 := T141_6
  T2 := Q2.T141_6_2
  h1 := (0,0,4,3,1)
  h2 := (0,0,4,3,1)
  D := [[0, 4, 3, 1], [0, 4, 3, 0], [0, 4, 3, 4], [0, 4, 3, 3], [0, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_7_0 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨7, by decide⟩
  m := 5
  T1 := T141_7
  T2 := Q2.T141_7_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_7_1 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨7, by decide⟩
  m := 5
  T1 := T141_7
  T2 := Q2.T141_7_2
  h1 := (0,0,1,3,4)
  h2 := (0,0,1,3,4)
  D := [[0, 1, 3, 4], [0, 1, 3, 0], [0, 1, 3, 1], [0, 1, 3, 2], [0, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_7_2 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨7, by decide⟩
  m := 5
  T1 := T141_7
  T2 := Q2.T141_7_2
  h1 := (0,0,2,1,3)
  h2 := (0,0,2,1,3)
  D := [[0, 2, 1, 3], [0, 2, 1, 0], [0, 2, 1, 2], [0, 2, 1, 4], [0, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_7_3 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨7, by decide⟩
  m := 5
  T1 := T141_7
  T2 := Q2.T141_7_2
  h1 := (0,0,3,4,2)
  h2 := (0,0,3,4,2)
  D := [[0, 3, 4, 2], [0, 3, 4, 0], [0, 3, 4, 3], [0, 3, 4, 1], [0, 3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_7_4 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨7, by decide⟩
  m := 5
  T1 := T141_7
  T2 := Q2.T141_7_2
  h1 := (0,0,4,2,1)
  h2 := (0,0,4,2,1)
  D := [[0, 4, 2, 1], [0, 4, 2, 0], [0, 4, 2, 4], [0, 4, 2, 3], [0, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_8_0 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨8, by decide⟩
  m := 5
  T1 := T141_8
  T2 := Q2.T141_8_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_8_1 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨8, by decide⟩
  m := 5
  T1 := T141_8
  T2 := Q2.T141_8_2
  h1 := (0,0,1,1,4)
  h2 := (0,0,1,1,4)
  D := [[0, 1, 1, 4], [0, 1, 1, 0], [0, 1, 1, 1], [0, 1, 1, 2], [0, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_8_2 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨8, by decide⟩
  m := 5
  T1 := T141_8
  T2 := Q2.T141_8_2
  h1 := (0,0,2,2,3)
  h2 := (0,0,2,2,3)
  D := [[0, 2, 2, 3], [0, 2, 2, 0], [0, 2, 2, 2], [0, 2, 2, 4], [0, 2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_8_3 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨8, by decide⟩
  m := 5
  T1 := T141_8
  T2 := Q2.T141_8_2
  h1 := (0,0,3,3,2)
  h2 := (0,0,3,3,2)
  D := [[0, 3, 3, 2], [0, 3, 3, 0], [0, 3, 3, 3], [0, 3, 3, 1], [0, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_8_4 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨8, by decide⟩
  m := 5
  T1 := T141_8
  T2 := Q2.T141_8_2
  h1 := (0,0,4,4,1)
  h2 := (0,0,4,4,1)
  D := [[0, 4, 4, 1], [0, 4, 4, 0], [0, 4, 4, 4], [0, 4, 4, 3], [0, 4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_9_0 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨9, by decide⟩
  m := 5
  T1 := T141_9
  T2 := Q2.T141_9_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_9_1 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨9, by decide⟩
  m := 5
  T1 := T141_9
  T2 := Q2.T141_9_2
  h1 := (0,0,1,0,4)
  h2 := (0,0,1,0,4)
  D := [[0, 1, 0, 4], [0, 1, 0, 0], [0, 1, 0, 1], [0, 1, 0, 2], [0, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
