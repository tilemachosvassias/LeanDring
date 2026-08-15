/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C026
import LeanDring.P5.Data.EntryK.C027

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 29: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_117_117_75 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (3,2,0,4,3)
  h2 := (3,2,0,4,0)
  D := [[3, 0, 3, 4], [3, 0, 0, 0], [3, 0, 2, 1], [3, 0, 4, 2], [3, 0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_80 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (3,2,1,4,3)
  h2 := (3,2,1,4,0)
  D := [[3, 1, 3, 1], [3, 1, 0, 3], [3, 1, 2, 0], [3, 1, 4, 2], [3, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_85 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (3,2,2,4,3)
  h2 := (3,2,2,4,0)
  D := [[3, 2, 3, 3], [3, 2, 0, 1], [3, 2, 2, 4], [3, 2, 4, 2], [3, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_90 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (3,2,3,4,3)
  h2 := (3,2,3,4,0)
  D := [[3, 3, 3, 0], [3, 3, 0, 4], [3, 3, 2, 3], [3, 3, 4, 2], [3, 3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_95 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (3,2,4,4,3)
  h2 := (3,2,4,4,0)
  D := [[3, 4, 3, 2], [3, 4, 0, 2], [3, 4, 2, 2], [3, 4, 4, 2], [3, 4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_100 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (4,1,0,0,3)
  h2 := (4,1,0,0,1)
  D := [[4, 0, 4, 0], [4, 0, 0, 0], [4, 0, 1, 0], [4, 0, 2, 0], [4, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_105 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (4,1,1,0,3)
  h2 := (4,1,1,0,1)
  D := [[4, 1, 4, 3], [4, 1, 0, 4], [4, 1, 1, 0], [4, 1, 2, 1], [4, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_110 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (4,1,2,0,3)
  h2 := (4,1,2,0,1)
  D := [[4, 2, 4, 1], [4, 2, 0, 3], [4, 2, 1, 0], [4, 2, 2, 2], [4, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_115 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (4,1,3,0,3)
  h2 := (4,1,3,0,1)
  D := [[4, 3, 4, 4], [4, 3, 0, 2], [4, 3, 1, 0], [4, 3, 2, 3], [4, 3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_117_120 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨117, by decide⟩
  m := 5
  T1 := T117_117
  T2 := Q2.T117_117_2
  h1 := (4,1,4,0,3)
  h2 := (4,1,4,0,1)
  D := [[4, 4, 4, 2], [4, 4, 0, 1], [4, 4, 1, 0], [4, 4, 2, 4], [4, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_0_0 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨0, by decide⟩
  m := 5
  T1 := T118_0
  T2 := Q2.T118_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_1_0 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨1, by decide⟩
  m := 5
  T1 := T118_1
  T2 := Q2.T118_1_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_1_1 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨1, by decide⟩
  m := 5
  T1 := T118_1
  T2 := Q2.T118_1_2
  h1 := (0,0,1,4,4)
  h2 := (0,0,1,4,4)
  D := [[0, 1, 4, 1], [0, 1, 4, 2], [0, 1, 4, 3], [0, 1, 4, 4], [0, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_1_2 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨1, by decide⟩
  m := 5
  T1 := T118_1
  T2 := Q2.T118_1_2
  h1 := (0,0,2,3,3)
  h2 := (0,0,2,3,3)
  D := [[0, 2, 3, 2], [0, 2, 3, 4], [0, 2, 3, 1], [0, 2, 3, 3], [0, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_1_3 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨1, by decide⟩
  m := 5
  T1 := T118_1
  T2 := Q2.T118_1_2
  h1 := (0,0,3,2,2)
  h2 := (0,0,3,2,2)
  D := [[0, 3, 2, 3], [0, 3, 2, 1], [0, 3, 2, 4], [0, 3, 2, 2], [0, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_1_4 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨1, by decide⟩
  m := 5
  T1 := T118_1
  T2 := Q2.T118_1_2
  h1 := (0,0,4,1,1)
  h2 := (0,0,4,1,1)
  D := [[0, 4, 1, 4], [0, 4, 1, 3], [0, 4, 1, 2], [0, 4, 1, 1], [0, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_6_0 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨6, by decide⟩
  m := 5
  T1 := T118_6
  T2 := Q2.T118_6_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_6_1 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨6, by decide⟩
  m := 5
  T1 := T118_6
  T2 := Q2.T118_6_2
  h1 := (0,0,1,2,4)
  h2 := (0,0,1,2,4)
  D := [[0, 1, 2, 1], [0, 1, 2, 2], [0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_6_2 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨6, by decide⟩
  m := 5
  T1 := T118_6
  T2 := Q2.T118_6_2
  h1 := (0,0,2,4,3)
  h2 := (0,0,2,4,3)
  D := [[0, 2, 4, 2], [0, 2, 4, 4], [0, 2, 4, 1], [0, 2, 4, 3], [0, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_6_3 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨6, by decide⟩
  m := 5
  T1 := T118_6
  T2 := Q2.T118_6_2
  h1 := (0,0,3,1,2)
  h2 := (0,0,3,1,2)
  D := [[0, 3, 1, 3], [0, 3, 1, 1], [0, 3, 1, 4], [0, 3, 1, 2], [0, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_6_4 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨6, by decide⟩
  m := 5
  T1 := T118_6
  T2 := Q2.T118_6_2
  h1 := (0,0,4,3,1)
  h2 := (0,0,4,3,1)
  D := [[0, 4, 3, 4], [0, 4, 3, 3], [0, 4, 3, 2], [0, 4, 3, 1], [0, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_7_0 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨7, by decide⟩
  m := 5
  T1 := T118_7
  T2 := Q2.T118_7_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_7_1 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨7, by decide⟩
  m := 5
  T1 := T118_7
  T2 := Q2.T118_7_2
  h1 := (0,0,1,3,4)
  h2 := (0,0,1,3,4)
  D := [[0, 1, 3, 1], [0, 1, 3, 2], [0, 1, 3, 3], [0, 1, 3, 4], [0, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_7_2 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨7, by decide⟩
  m := 5
  T1 := T118_7
  T2 := Q2.T118_7_2
  h1 := (0,0,2,1,3)
  h2 := (0,0,2,1,3)
  D := [[0, 2, 1, 2], [0, 2, 1, 4], [0, 2, 1, 1], [0, 2, 1, 3], [0, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_7_3 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨7, by decide⟩
  m := 5
  T1 := T118_7
  T2 := Q2.T118_7_2
  h1 := (0,0,3,4,2)
  h2 := (0,0,3,4,2)
  D := [[0, 3, 4, 3], [0, 3, 4, 1], [0, 3, 4, 4], [0, 3, 4, 2], [0, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_7_4 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨7, by decide⟩
  m := 5
  T1 := T118_7
  T2 := Q2.T118_7_2
  h1 := (0,0,4,2,1)
  h2 := (0,0,4,2,1)
  D := [[0, 4, 2, 4], [0, 4, 2, 3], [0, 4, 2, 2], [0, 4, 2, 1], [0, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_8_0 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨8, by decide⟩
  m := 5
  T1 := T118_8
  T2 := Q2.T118_8_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_8_1 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨8, by decide⟩
  m := 5
  T1 := T118_8
  T2 := Q2.T118_8_2
  h1 := (0,0,1,1,4)
  h2 := (0,0,1,1,4)
  D := [[0, 1, 1, 1], [0, 1, 1, 2], [0, 1, 1, 3], [0, 1, 1, 4], [0, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_8_2 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨8, by decide⟩
  m := 5
  T1 := T118_8
  T2 := Q2.T118_8_2
  h1 := (0,0,2,2,3)
  h2 := (0,0,2,2,3)
  D := [[0, 2, 2, 2], [0, 2, 2, 4], [0, 2, 2, 1], [0, 2, 2, 3], [0, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_8_3 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨8, by decide⟩
  m := 5
  T1 := T118_8
  T2 := Q2.T118_8_2
  h1 := (0,0,3,3,2)
  h2 := (0,0,3,3,2)
  D := [[0, 3, 3, 3], [0, 3, 3, 1], [0, 3, 3, 4], [0, 3, 3, 2], [0, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_8_4 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨8, by decide⟩
  m := 5
  T1 := T118_8
  T2 := Q2.T118_8_2
  h1 := (0,0,4,4,1)
  h2 := (0,0,4,4,1)
  D := [[0, 4, 4, 4], [0, 4, 4, 3], [0, 4, 4, 2], [0, 4, 4, 1], [0, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_9_0 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨9, by decide⟩
  m := 5
  T1 := T118_9
  T2 := Q2.T118_9_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_9_1 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨9, by decide⟩
  m := 5
  T1 := T118_9
  T2 := Q2.T118_9_2
  h1 := (0,0,1,0,4)
  h2 := (0,0,1,0,4)
  D := [[0, 1, 0, 1], [0, 1, 0, 2], [0, 1, 0, 3], [0, 1, 0, 4], [0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_9_2 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨9, by decide⟩
  m := 5
  T1 := T118_9
  T2 := Q2.T118_9_2
  h1 := (0,0,2,0,3)
  h2 := (0,0,2,0,3)
  D := [[0, 2, 0, 2], [0, 2, 0, 4], [0, 2, 0, 1], [0, 2, 0, 3], [0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_9_3 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨9, by decide⟩
  m := 5
  T1 := T118_9
  T2 := Q2.T118_9_2
  h1 := (0,0,3,0,2)
  h2 := (0,0,3,0,2)
  D := [[0, 3, 0, 3], [0, 3, 0, 1], [0, 3, 0, 4], [0, 3, 0, 2], [0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_9_4 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨9, by decide⟩
  m := 5
  T1 := T118_9
  T2 := Q2.T118_9_2
  h1 := (0,0,4,0,1)
  h2 := (0,0,4,0,1)
  D := [[0, 4, 0, 4], [0, 4, 0, 3], [0, 4, 0, 2], [0, 4, 0, 1], [0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_10_0 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T118_10
  T2 := Q2.T118_10_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_10_1 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T118_10
  T2 := Q2.T118_10_2
  h1 := (0,0,0,1,4)
  h2 := (0,0,0,1,4)
  D := [[0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_10_2 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T118_10
  T2 := Q2.T118_10_2
  h1 := (0,0,0,2,3)
  h2 := (0,0,0,2,3)
  D := [[0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_10_3 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T118_10
  T2 := Q2.T118_10_2
  h1 := (0,0,0,3,2)
  h2 := (0,0,0,3,2)
  D := [[0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_10_4 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T118_10
  T2 := Q2.T118_10_2
  h1 := (0,0,0,4,1)
  h2 := (0,0,0,4,1)
  D := [[0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_12_0 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T118_12
  T2 := Q2.T118_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_12_1 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T118_12
  T2 := Q2.T118_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_12_2 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T118_12
  T2 := Q2.T118_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_12_3 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T118_12
  T2 := Q2.T118_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_12_4 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T118_12
  T2 := Q2.T118_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_13_0 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T118_13
  T2 := Q2.T118_13_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_13_1 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T118_13
  T2 := Q2.T118_13_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_13_2 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T118_13
  T2 := Q2.T118_13_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_13_3 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T118_13
  T2 := Q2.T118_13_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_13_4 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T118_13
  T2 := Q2.T118_13_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_13_9 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T118_13
  T2 := Q2.T118_13_2
  h1 := (0,0,1,4,4)
  h2 := (0,0,1,4,4)
  D := [[0, 1, 4, 1], [0, 1, 4, 2], [0, 1, 4, 3], [0, 1, 4, 4], [0, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_13_10 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T118_13
  T2 := Q2.T118_13_2
  h1 := (0,0,2,0,3)
  h2 := (0,0,2,0,3)
  D := [[0, 2, 0, 2], [0, 2, 0, 4], [0, 2, 0, 1], [0, 2, 0, 3], [0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_13_11 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T118_13
  T2 := Q2.T118_13_2
  h1 := (0,0,2,1,3)
  h2 := (0,0,2,1,3)
  D := [[0, 2, 1, 2], [0, 2, 1, 4], [0, 2, 1, 1], [0, 2, 1, 3], [0, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_13_12 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T118_13
  T2 := Q2.T118_13_2
  h1 := (0,0,2,2,3)
  h2 := (0,0,2,2,3)
  D := [[0, 2, 2, 2], [0, 2, 2, 4], [0, 2, 2, 1], [0, 2, 2, 3], [0, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_13_13 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T118_13
  T2 := Q2.T118_13_2
  h1 := (0,0,2,3,3)
  h2 := (0,0,2,3,3)
  D := [[0, 2, 3, 2], [0, 2, 3, 4], [0, 2, 3, 1], [0, 2, 3, 3], [0, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_13_14 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T118_13
  T2 := Q2.T118_13_2
  h1 := (0,0,2,4,3)
  h2 := (0,0,2,4,3)
  D := [[0, 2, 4, 2], [0, 2, 4, 4], [0, 2, 4, 1], [0, 2, 4, 3], [0, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_13_15 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T118_13
  T2 := Q2.T118_13_2
  h1 := (0,0,3,0,2)
  h2 := (0,0,3,0,2)
  D := [[0, 3, 0, 3], [0, 3, 0, 1], [0, 3, 0, 4], [0, 3, 0, 2], [0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_13_16 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T118_13
  T2 := Q2.T118_13_2
  h1 := (0,0,3,1,2)
  h2 := (0,0,3,1,2)
  D := [[0, 3, 1, 3], [0, 3, 1, 1], [0, 3, 1, 4], [0, 3, 1, 2], [0, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_13_17 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T118_13
  T2 := Q2.T118_13_2
  h1 := (0,0,3,2,2)
  h2 := (0,0,3,2,2)
  D := [[0, 3, 2, 3], [0, 3, 2, 1], [0, 3, 2, 4], [0, 3, 2, 2], [0, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
