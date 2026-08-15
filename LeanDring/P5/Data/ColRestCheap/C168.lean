/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C018

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 167: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_75_37_3 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T75_37
  T2 := Q2.T75_37_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_37_4 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T75_37
  T2 := Q2.T75_37_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_37_5 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T75_37
  T2 := Q2.T75_37_2
  h1 := (1,1,2,4,3)
  h2 := (1,1,2,4,1)
  D := [[1, 2, 2], [1, 2, 1], [1, 2, 0], [1, 2, 4], [1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_37_10 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T75_37
  T2 := Q2.T75_37_2
  h1 := (2,2,4,4,2)
  h2 := (2,2,4,4,3)
  D := [[2, 4, 2], [2, 4, 0], [2, 4, 3], [2, 4, 1], [2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_37_15 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T75_37
  T2 := Q2.T75_37_2
  h1 := (3,3,1,0,3)
  h2 := (3,3,1,0,2)
  D := [[3, 1, 0], [3, 1, 2], [3, 1, 4], [3, 1, 1], [3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_37_20 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T75_37
  T2 := Q2.T75_37_2
  h1 := (4,4,3,2,2)
  h2 := (4,4,3,2,4)
  D := [[4, 3, 1], [4, 3, 2], [4, 3, 3], [4, 3, 4], [4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_42_0 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T75_42
  T2 := Q2.T75_42_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_42_1 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T75_42
  T2 := Q2.T75_42_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_42_2 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T75_42
  T2 := Q2.T75_42_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_42_3 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T75_42
  T2 := Q2.T75_42_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_42_4 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T75_42
  T2 := Q2.T75_42_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_42_5 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T75_42
  T2 := Q2.T75_42_2
  h1 := (1,1,3,4,4)
  h2 := (1,1,3,4,2)
  D := [[1, 3, 2], [1, 3, 1], [1, 3, 0], [1, 3, 4], [1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_42_10 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T75_42
  T2 := Q2.T75_42_2
  h1 := (2,2,1,4,0)
  h2 := (2,2,1,4,1)
  D := [[2, 1, 1], [2, 1, 4], [2, 1, 2], [2, 1, 0], [2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_42_15 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T75_42
  T2 := Q2.T75_42_2
  h1 := (3,3,4,0,4)
  h2 := (3,3,4,0,3)
  D := [[3, 4, 2], [3, 4, 4], [3, 4, 1], [3, 4, 3], [3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_42_20 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T75_42
  T2 := Q2.T75_42_2
  h1 := (4,4,2,2,2)
  h2 := (4,4,2,2,4)
  D := [[4, 2, 0], [4, 2, 1], [4, 2, 2], [4, 2, 3], [4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_47_0 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T75_47
  T2 := Q2.T75_47_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_47_1 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T75_47
  T2 := Q2.T75_47_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_47_2 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T75_47
  T2 := Q2.T75_47_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_47_3 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T75_47
  T2 := Q2.T75_47_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_47_4 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T75_47
  T2 := Q2.T75_47_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_47_5 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T75_47
  T2 := Q2.T75_47_2
  h1 := (1,1,1,4,2)
  h2 := (1,1,1,4,0)
  D := [[1, 1, 2], [1, 1, 1], [1, 1, 0], [1, 1, 4], [1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_47_10 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T75_47
  T2 := Q2.T75_47_2
  h1 := (2,2,2,4,4)
  h2 := (2,2,2,4,0)
  D := [[2, 2, 3], [2, 2, 1], [2, 2, 4], [2, 2, 2], [2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_47_15 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T75_47
  T2 := Q2.T75_47_2
  h1 := (3,3,3,0,2)
  h2 := (3,3,3,0,1)
  D := [[3, 3, 3], [3, 3, 0], [3, 3, 2], [3, 3, 4], [3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_47_20 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T75_47
  T2 := Q2.T75_47_2
  h1 := (4,4,4,2,2)
  h2 := (4,4,4,2,4)
  D := [[4, 4, 2], [4, 4, 3], [4, 4, 4], [4, 4, 0], [4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_52_0 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T75_52
  T2 := Q2.T75_52_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_52_1 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T75_52
  T2 := Q2.T75_52_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_52_2 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T75_52
  T2 := Q2.T75_52_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_52_3 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T75_52
  T2 := Q2.T75_52_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_52_4 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T75_52
  T2 := Q2.T75_52_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_52_5 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T75_52
  T2 := Q2.T75_52_2
  h1 := (1,1,0,4,1)
  h2 := (1,1,0,4,4)
  D := [[1, 0, 2], [1, 0, 1], [1, 0, 0], [1, 0, 4], [1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_52_10 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T75_52
  T2 := Q2.T75_52_2
  h1 := (2,2,0,4,1)
  h2 := (2,2,0,4,2)
  D := [[2, 0, 4], [2, 0, 2], [2, 0, 0], [2, 0, 3], [2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_52_15 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T75_52
  T2 := Q2.T75_52_2
  h1 := (3,3,0,0,1)
  h2 := (3,3,0,0,0)
  D := [[3, 0, 1], [3, 0, 3], [3, 0, 0], [3, 0, 2], [3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_52_20 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T75_52
  T2 := Q2.T75_52_2
  h1 := (4,4,0,2,2)
  h2 := (4,4,0,2,4)
  D := [[4, 0, 3], [4, 0, 4], [4, 0, 0], [4, 0, 1], [4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_75_0 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T75_75
  T2 := Q2.T75_75_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_75_1 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T75_75
  T2 := Q2.T75_75_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_75_2 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T75_75
  T2 := Q2.T75_75_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_75_3 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T75_75
  T2 := Q2.T75_75_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_75_4 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T75_75
  T2 := Q2.T75_75_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_75_5 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T75_75
  T2 := Q2.T75_75_2
  h1 := (1,1,0,4,1)
  h2 := (1,1,0,4,4)
  D := [[1, 0, 2], [1, 0, 1], [1, 0, 0], [1, 0, 4], [1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_75_6 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T75_75
  T2 := Q2.T75_75_2
  h1 := (1,1,1,4,1)
  h2 := (1,1,1,4,4)
  D := [[1, 1, 1], [1, 1, 0], [1, 1, 4], [1, 1, 3], [1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_75_7 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T75_75
  T2 := Q2.T75_75_2
  h1 := (1,1,2,4,1)
  h2 := (1,1,2,4,4)
  D := [[1, 2, 0], [1, 2, 4], [1, 2, 3], [1, 2, 2], [1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_75_8 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T75_75
  T2 := Q2.T75_75_2
  h1 := (1,1,3,4,1)
  h2 := (1,1,3,4,4)
  D := [[1, 3, 4], [1, 3, 3], [1, 3, 2], [1, 3, 1], [1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_75_9 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T75_75
  T2 := Q2.T75_75_2
  h1 := (1,1,4,4,1)
  h2 := (1,1,4,4,4)
  D := [[1, 4, 3], [1, 4, 2], [1, 4, 1], [1, 4, 0], [1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_75_10 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T75_75
  T2 := Q2.T75_75_2
  h1 := (2,2,0,4,1)
  h2 := (2,2,0,4,2)
  D := [[2, 0, 4], [2, 0, 2], [2, 0, 0], [2, 0, 3], [2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_75_11 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T75_75
  T2 := Q2.T75_75_2
  h1 := (2,2,1,4,1)
  h2 := (2,2,1,4,2)
  D := [[2, 1, 2], [2, 1, 0], [2, 1, 3], [2, 1, 1], [2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_75_12 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T75_75
  T2 := Q2.T75_75_2
  h1 := (2,2,2,4,1)
  h2 := (2,2,2,4,2)
  D := [[2, 2, 0], [2, 2, 3], [2, 2, 1], [2, 2, 4], [2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_75_13 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T75_75
  T2 := Q2.T75_75_2
  h1 := (2,2,3,4,1)
  h2 := (2,2,3,4,2)
  D := [[2, 3, 3], [2, 3, 1], [2, 3, 4], [2, 3, 2], [2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_75_14 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T75_75
  T2 := Q2.T75_75_2
  h1 := (2,2,4,4,1)
  h2 := (2,2,4,4,2)
  D := [[2, 4, 1], [2, 4, 4], [2, 4, 2], [2, 4, 0], [2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_75_15 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T75_75
  T2 := Q2.T75_75_2
  h1 := (3,3,0,0,1)
  h2 := (3,3,0,0,0)
  D := [[3, 0, 1], [3, 0, 3], [3, 0, 0], [3, 0, 2], [3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_75_16 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T75_75
  T2 := Q2.T75_75_2
  h1 := (3,3,1,0,1)
  h2 := (3,3,1,0,0)
  D := [[3, 1, 3], [3, 1, 0], [3, 1, 2], [3, 1, 4], [3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_75_17 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T75_75
  T2 := Q2.T75_75_2
  h1 := (3,3,2,0,1)
  h2 := (3,3,2,0,0)
  D := [[3, 2, 0], [3, 2, 2], [3, 2, 4], [3, 2, 1], [3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_75_18 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T75_75
  T2 := Q2.T75_75_2
  h1 := (3,3,3,0,1)
  h2 := (3,3,3,0,0)
  D := [[3, 3, 2], [3, 3, 4], [3, 3, 1], [3, 3, 3], [3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_75_19 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T75_75
  T2 := Q2.T75_75_2
  h1 := (3,3,4,0,1)
  h2 := (3,3,4,0,0)
  D := [[3, 4, 4], [3, 4, 1], [3, 4, 3], [3, 4, 0], [3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_75_20 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T75_75
  T2 := Q2.T75_75_2
  h1 := (4,4,0,2,2)
  h2 := (4,4,0,2,4)
  D := [[4, 0, 3], [4, 0, 4], [4, 0, 0], [4, 0, 1], [4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_75_21 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T75_75
  T2 := Q2.T75_75_2
  h1 := (4,4,1,2,2)
  h2 := (4,4,1,2,4)
  D := [[4, 1, 4], [4, 1, 0], [4, 1, 1], [4, 1, 2], [4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_75_22 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T75_75
  T2 := Q2.T75_75_2
  h1 := (4,4,2,2,2)
  h2 := (4,4,2,2,4)
  D := [[4, 2, 0], [4, 2, 1], [4, 2, 2], [4, 2, 3], [4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_75_23 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T75_75
  T2 := Q2.T75_75_2
  h1 := (4,4,3,2,2)
  h2 := (4,4,3,2,4)
  D := [[4, 3, 1], [4, 3, 2], [4, 3, 3], [4, 3, 4], [4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_75_75_24 : ColCert where
  rK := ⟨75, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T75_75
  T2 := Q2.T75_75_2
  h1 := (4,4,4,2,2)
  h2 := (4,4,4,2,4)
  D := [[4, 4, 2], [4, 4, 3], [4, 4, 4], [4, 4, 0], [4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_0_0 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨0, by decide⟩
  m := 25
  T1 := T76_0
  T2 := Q2.T76_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_1_0 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨1, by decide⟩
  m := 25
  T1 := T76_1
  T2 := Q2.T76_1_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
