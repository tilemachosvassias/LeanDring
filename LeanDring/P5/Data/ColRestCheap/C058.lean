/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C032

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 57: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_126_48_3 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T126_48
  T2 := Q2.T126_48_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_48_4 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T126_48
  T2 := Q2.T126_48_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_53_0 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T126_53
  T2 := Q2.T126_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_53_1 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T126_53
  T2 := Q2.T126_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_53_2 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T126_53
  T2 := Q2.T126_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_53_3 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T126_53
  T2 := Q2.T126_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_53_4 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T126_53
  T2 := Q2.T126_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_53_5 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T126_53
  T2 := Q2.T126_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_53_10 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T126_53
  T2 := Q2.T126_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_53_15 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T126_53
  T2 := Q2.T126_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_53_20 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T126_53
  T2 := Q2.T126_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_82_0 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T126_82
  T2 := Q2.T126_82_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_82_1 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T126_82
  T2 := Q2.T126_82_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_82_2 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T126_82
  T2 := Q2.T126_82_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_82_3 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T126_82
  T2 := Q2.T126_82_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_82_4 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T126_82
  T2 := Q2.T126_82_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_82_5 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T126_82
  T2 := Q2.T126_82_2
  h1 := (1,0,2,0,0)
  h2 := (1,0,2,0,0)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_82_10 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T126_82
  T2 := Q2.T126_82_2
  h1 := (2,0,4,0,0)
  h2 := (2,0,4,0,0)
  D := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_82_15 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T126_82
  T2 := Q2.T126_82_2
  h1 := (3,0,1,0,0)
  h2 := (3,0,1,0,0)
  D := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_82_20 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T126_82
  T2 := Q2.T126_82_2
  h1 := (4,0,3,0,0)
  h2 := (4,0,3,0,0)
  D := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_93_0 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T126_93
  T2 := Q2.T126_93_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_93_1 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T126_93
  T2 := Q2.T126_93_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_93_2 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T126_93
  T2 := Q2.T126_93_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_93_3 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T126_93
  T2 := Q2.T126_93_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_93_4 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T126_93
  T2 := Q2.T126_93_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_93_5 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T126_93
  T2 := Q2.T126_93_2
  h1 := (1,3,2,1,4)
  h2 := (1,3,2,1,4)
  D := [[1, 3, 3, 0], [1, 3, 3, 2], [1, 3, 3, 4], [1, 3, 3, 1], [1, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_99_0 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T126_99
  T2 := Q2.T126_99_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_99_1 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T126_99
  T2 := Q2.T126_99_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_99_2 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T126_99
  T2 := Q2.T126_99_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_99_3 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T126_99
  T2 := Q2.T126_99_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_99_4 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T126_99
  T2 := Q2.T126_99_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_99_5 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T126_99
  T2 := Q2.T126_99_2
  h1 := (1,1,2,0,0)
  h2 := (1,1,2,0,0)
  D := [[1, 1, 4, 4], [1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1], [1, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_99_10 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T126_99
  T2 := Q2.T126_99_2
  h1 := (2,2,4,1,2)
  h2 := (2,2,4,1,2)
  D := [[2, 2, 2, 2], [2, 2, 2, 0], [2, 2, 2, 3], [2, 2, 2, 1], [2, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_99_15 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T126_99
  T2 := Q2.T126_99_2
  h1 := (3,3,1,3,2)
  h2 := (3,3,1,3,2)
  D := [[3, 3, 4, 0], [3, 3, 4, 2], [3, 3, 4, 4], [3, 3, 4, 1], [3, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_99_20 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T126_99
  T2 := Q2.T126_99_2
  h1 := (4,4,3,1,1)
  h2 := (4,4,3,1,1)
  D := [[4, 4, 0, 4], [4, 4, 0, 0], [4, 4, 0, 1], [4, 4, 0, 2], [4, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_101_0 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T126_101
  T2 := Q2.T126_101_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_101_1 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T126_101
  T2 := Q2.T126_101_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_101_2 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T126_101
  T2 := Q2.T126_101_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_101_3 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T126_101
  T2 := Q2.T126_101_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_101_4 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T126_101
  T2 := Q2.T126_101_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_101_5 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T126_101
  T2 := Q2.T126_101_2
  h1 := (1,4,2,4,3)
  h2 := (1,4,2,4,3)
  D := [[1, 4, 0, 0], [1, 4, 0, 1], [1, 4, 0, 2], [1, 4, 0, 3], [1, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_107_0 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T126_107
  T2 := Q2.T126_107_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_107_1 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T126_107
  T2 := Q2.T126_107_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_107_2 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T126_107
  T2 := Q2.T126_107_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_107_3 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T126_107
  T2 := Q2.T126_107_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_107_4 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T126_107
  T2 := Q2.T126_107_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_107_5 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T126_107
  T2 := Q2.T126_107_2
  h1 := (1,2,2,3,4)
  h2 := (1,2,2,3,4)
  D := [[1, 2, 1, 4], [1, 2, 1, 2], [1, 2, 1, 0], [1, 2, 1, 3], [1, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_107_10 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T126_107
  T2 := Q2.T126_107_2
  h1 := (2,4,4,3,0)
  h2 := (2,4,4,3,0)
  D := [[2, 4, 0, 3], [2, 4, 0, 4], [2, 4, 0, 0], [2, 4, 0, 1], [2, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_110_0 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T126_110
  T2 := Q2.T126_110_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_110_1 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T126_110
  T2 := Q2.T126_110_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_110_2 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T126_110
  T2 := Q2.T126_110_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_110_3 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T126_110
  T2 := Q2.T126_110_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_110_4 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T126_110
  T2 := Q2.T126_110_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_110_5 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T126_110
  T2 := Q2.T126_110_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_110_10 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T126_110
  T2 := Q2.T126_110_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_110_15 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T126_110
  T2 := Q2.T126_110_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_110_20 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T126_110
  T2 := Q2.T126_110_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_110_25 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T126_110
  T2 := Q2.T126_110_2
  h1 := (0,1,0,0,0)
  h2 := (0,1,0,0,0)
  D := [[0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_110_50 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T126_110
  T2 := Q2.T126_110_2
  h1 := (0,2,0,0,0)
  h2 := (0,2,0,0,0)
  D := [[0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_110_75 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T126_110
  T2 := Q2.T126_110_2
  h1 := (0,3,0,0,0)
  h2 := (0,3,0,0,0)
  D := [[0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
