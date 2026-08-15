/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C040

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 93: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_141_81_20 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T141_81
  T2 := Q2.T141_81_2
  h1 := (4,0,1,0,0)
  h2 := (4,0,1,0,0)
  D := [[4, 1, 0, 0], [4, 1, 1, 1], [4, 1, 2, 2], [4, 1, 3, 3], [4, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_82_0 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T141_82
  T2 := Q2.T141_82_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_82_1 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T141_82
  T2 := Q2.T141_82_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_82_2 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T141_82
  T2 := Q2.T141_82_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_82_3 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T141_82
  T2 := Q2.T141_82_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_82_4 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T141_82
  T2 := Q2.T141_82_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_82_5 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T141_82
  T2 := Q2.T141_82_2
  h1 := (1,0,2,0,0)
  h2 := (1,0,2,0,0)
  D := [[1, 2, 0, 0], [1, 2, 4, 3], [1, 2, 3, 1], [1, 2, 2, 4], [1, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_82_10 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T141_82
  T2 := Q2.T141_82_2
  h1 := (2,0,4,0,0)
  h2 := (2,0,4,0,0)
  D := [[2, 4, 0, 0], [2, 4, 3, 2], [2, 4, 1, 4], [2, 4, 4, 1], [2, 4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_82_15 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T141_82
  T2 := Q2.T141_82_2
  h1 := (3,0,1,0,0)
  h2 := (3,0,1,0,0)
  D := [[3, 1, 0, 0], [3, 1, 2, 2], [3, 1, 4, 4], [3, 1, 1, 1], [3, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_82_20 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T141_82
  T2 := Q2.T141_82_2
  h1 := (4,0,3,0,0)
  h2 := (4,0,3,0,0)
  D := [[4, 3, 0, 0], [4, 3, 1, 3], [4, 3, 2, 1], [4, 3, 3, 4], [4, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_83_0 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T141_83
  T2 := Q2.T141_83_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_83_1 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T141_83
  T2 := Q2.T141_83_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_83_2 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T141_83
  T2 := Q2.T141_83_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_83_3 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T141_83
  T2 := Q2.T141_83_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_83_4 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T141_83
  T2 := Q2.T141_83_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_83_5 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T141_83
  T2 := Q2.T141_83_2
  h1 := (1,0,3,0,0)
  h2 := (1,0,3,0,0)
  D := [[1, 3, 0, 0], [1, 3, 4, 4], [1, 3, 3, 3], [1, 3, 2, 2], [1, 3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_83_10 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T141_83
  T2 := Q2.T141_83_2
  h1 := (2,0,1,0,0)
  h2 := (2,0,1,0,0)
  D := [[2, 1, 0, 0], [2, 1, 3, 4], [2, 1, 1, 3], [2, 1, 4, 2], [2, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_83_15 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T141_83
  T2 := Q2.T141_83_2
  h1 := (3,0,4,0,0)
  h2 := (3,0,4,0,0)
  D := [[3, 4, 0, 0], [3, 4, 2, 0], [3, 4, 4, 0], [3, 4, 1, 0], [3, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_83_20 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T141_83
  T2 := Q2.T141_83_2
  h1 := (4,0,2,0,0)
  h2 := (4,0,2,0,0)
  D := [[4, 2, 0, 0], [4, 2, 1, 2], [4, 2, 2, 4], [4, 2, 3, 1], [4, 2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_84_0 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T141_84
  T2 := Q2.T141_84_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_84_1 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T141_84
  T2 := Q2.T141_84_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_84_2 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T141_84
  T2 := Q2.T141_84_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_84_3 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T141_84
  T2 := Q2.T141_84_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_84_4 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T141_84
  T2 := Q2.T141_84_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_84_5 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T141_84
  T2 := Q2.T141_84_2
  h1 := (1,0,1,0,0)
  h2 := (1,0,1,0,0)
  D := [[1, 1, 0, 0], [1, 1, 4, 2], [1, 1, 3, 4], [1, 1, 2, 1], [1, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_84_10 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T141_84
  T2 := Q2.T141_84_2
  h1 := (2,0,2,0,0)
  h2 := (2,0,2,0,0)
  D := [[2, 2, 0, 0], [2, 2, 3, 0], [2, 2, 1, 0], [2, 2, 4, 0], [2, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_84_15 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T141_84
  T2 := Q2.T141_84_2
  h1 := (3,0,3,0,0)
  h2 := (3,0,3,0,0)
  D := [[3, 3, 0, 0], [3, 3, 2, 4], [3, 3, 4, 3], [3, 3, 1, 2], [3, 3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_84_20 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T141_84
  T2 := Q2.T141_84_2
  h1 := (4,0,4,0,0)
  h2 := (4,0,4,0,0)
  D := [[4, 4, 0, 0], [4, 4, 1, 4], [4, 4, 2, 3], [4, 4, 3, 2], [4, 4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_0 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_1 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_2 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_3 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_4 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_5 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 1, 0, 0], [0, 1, 0, 1], [0, 1, 0, 2], [0, 1, 0, 3], [0, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_6 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (0,0,1,0,1)
  h2 := (0,0,1,0,1)
  D := [[0, 1, 0, 1], [0, 1, 0, 2], [0, 1, 0, 3], [0, 1, 0, 4], [0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_7 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (0,0,1,0,2)
  h2 := (0,0,1,0,2)
  D := [[0, 1, 0, 2], [0, 1, 0, 3], [0, 1, 0, 4], [0, 1, 0, 0], [0, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_8 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (0,0,1,0,3)
  h2 := (0,0,1,0,3)
  D := [[0, 1, 0, 3], [0, 1, 0, 4], [0, 1, 0, 0], [0, 1, 0, 1], [0, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_9 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (0,0,1,0,4)
  h2 := (0,0,1,0,4)
  D := [[0, 1, 0, 4], [0, 1, 0, 0], [0, 1, 0, 1], [0, 1, 0, 2], [0, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_10 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 2, 0, 0], [0, 2, 0, 2], [0, 2, 0, 4], [0, 2, 0, 1], [0, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_11 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (0,0,2,0,1)
  h2 := (0,0,2,0,1)
  D := [[0, 2, 0, 1], [0, 2, 0, 3], [0, 2, 0, 0], [0, 2, 0, 2], [0, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_12 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (0,0,2,0,2)
  h2 := (0,0,2,0,2)
  D := [[0, 2, 0, 2], [0, 2, 0, 4], [0, 2, 0, 1], [0, 2, 0, 3], [0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_13 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (0,0,2,0,3)
  h2 := (0,0,2,0,3)
  D := [[0, 2, 0, 3], [0, 2, 0, 0], [0, 2, 0, 2], [0, 2, 0, 4], [0, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_14 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (0,0,2,0,4)
  h2 := (0,0,2,0,4)
  D := [[0, 2, 0, 4], [0, 2, 0, 1], [0, 2, 0, 3], [0, 2, 0, 0], [0, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_15 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 3, 0, 0], [0, 3, 0, 3], [0, 3, 0, 1], [0, 3, 0, 4], [0, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_16 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (0,0,3,0,1)
  h2 := (0,0,3,0,1)
  D := [[0, 3, 0, 1], [0, 3, 0, 4], [0, 3, 0, 2], [0, 3, 0, 0], [0, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_17 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (0,0,3,0,2)
  h2 := (0,0,3,0,2)
  D := [[0, 3, 0, 2], [0, 3, 0, 0], [0, 3, 0, 3], [0, 3, 0, 1], [0, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_18 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (0,0,3,0,3)
  h2 := (0,0,3,0,3)
  D := [[0, 3, 0, 3], [0, 3, 0, 1], [0, 3, 0, 4], [0, 3, 0, 2], [0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_19 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (0,0,3,0,4)
  h2 := (0,0,3,0,4)
  D := [[0, 3, 0, 4], [0, 3, 0, 2], [0, 3, 0, 0], [0, 3, 0, 3], [0, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_20 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 4, 0, 0], [0, 4, 0, 4], [0, 4, 0, 3], [0, 4, 0, 2], [0, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_21 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (0,0,4,0,1)
  h2 := (0,0,4,0,1)
  D := [[0, 4, 0, 1], [0, 4, 0, 0], [0, 4, 0, 4], [0, 4, 0, 3], [0, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_22 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (0,0,4,0,2)
  h2 := (0,0,4,0,2)
  D := [[0, 4, 0, 2], [0, 4, 0, 1], [0, 4, 0, 0], [0, 4, 0, 4], [0, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_23 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (0,0,4,0,3)
  h2 := (0,0,4,0,3)
  D := [[0, 4, 0, 3], [0, 4, 0, 2], [0, 4, 0, 1], [0, 4, 0, 0], [0, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_24 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (0,0,4,0,4)
  h2 := (0,0,4,0,4)
  D := [[0, 4, 0, 4], [0, 4, 0, 3], [0, 4, 0, 2], [0, 4, 0, 1], [0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_25 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (1,0,0,4,4)
  h2 := (1,0,0,4,4)
  D := [[1, 0, 4, 0], [1, 0, 3, 1], [1, 0, 2, 2], [1, 0, 1, 3], [1, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_30 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (1,0,1,4,4)
  h2 := (1,0,1,4,4)
  D := [[1, 1, 4, 0], [1, 1, 3, 2], [1, 1, 2, 4], [1, 1, 1, 1], [1, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_35 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (1,0,2,4,4)
  h2 := (1,0,2,4,4)
  D := [[1, 2, 4, 0], [1, 2, 3, 3], [1, 2, 2, 1], [1, 2, 1, 4], [1, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_40 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (1,0,3,4,4)
  h2 := (1,0,3,4,4)
  D := [[1, 3, 4, 0], [1, 3, 3, 4], [1, 3, 2, 3], [1, 3, 1, 2], [1, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_85_45 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨85, by decide⟩
  m := 5
  T1 := T141_85
  T2 := Q2.T141_85_2
  h1 := (1,0,4,4,4)
  h2 := (1,0,4,4,4)
  D := [[1, 4, 4, 0], [1, 4, 3, 0], [1, 4, 2, 0], [1, 4, 1, 0], [1, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_86_5 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨86, by decide⟩
  m := 5
  T1 := T141_86
  T2 := Q2.T141_86_2
  h1 := (1,0,0,4,0)
  h2 := (1,0,0,4,0)
  D := [[1, 0, 4, 1], [1, 0, 3, 2], [1, 0, 2, 3], [1, 0, 1, 4], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_86_6 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨86, by decide⟩
  m := 5
  T1 := T141_86
  T2 := Q2.T141_86_2
  h1 := (1,0,1,3,0)
  h2 := (1,0,1,3,0)
  D := [[1, 1, 3, 2], [1, 1, 2, 4], [1, 1, 1, 1], [1, 1, 0, 3], [1, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
