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
rest tier, chunk 120: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_147_80_40 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨80, by decide⟩
  m := 1
  T1 := T147_80
  T2 := Q2.T147_80_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 0, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_80_45 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨80, by decide⟩
  m := 1
  T1 := T147_80
  T2 := Q2.T147_80_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 0, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_80_50 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨80, by decide⟩
  m := 1
  T1 := T147_80
  T2 := Q2.T147_80_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_80_55 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨80, by decide⟩
  m := 1
  T1 := T147_80
  T2 := Q2.T147_80_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 0, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_80_60 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨80, by decide⟩
  m := 1
  T1 := T147_80
  T2 := Q2.T147_80_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 0, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_80_65 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨80, by decide⟩
  m := 1
  T1 := T147_80
  T2 := Q2.T147_80_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 0, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_80_70 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨80, by decide⟩
  m := 1
  T1 := T147_80
  T2 := Q2.T147_80_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 0, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_80_75 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨80, by decide⟩
  m := 1
  T1 := T147_80
  T2 := Q2.T147_80_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_80_80 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨80, by decide⟩
  m := 1
  T1 := T147_80
  T2 := Q2.T147_80_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 0, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_80_85 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨80, by decide⟩
  m := 1
  T1 := T147_80
  T2 := Q2.T147_80_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 0, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_80_90 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨80, by decide⟩
  m := 1
  T1 := T147_80
  T2 := Q2.T147_80_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 0, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_80_95 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨80, by decide⟩
  m := 1
  T1 := T147_80
  T2 := Q2.T147_80_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 0, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_80_100 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨80, by decide⟩
  m := 1
  T1 := T147_80
  T2 := Q2.T147_80_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_80_105 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨80, by decide⟩
  m := 1
  T1 := T147_80
  T2 := Q2.T147_80_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 0, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_80_110 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨80, by decide⟩
  m := 1
  T1 := T147_80
  T2 := Q2.T147_80_2
  h1 := (0,0,4,2,0)
  h2 := (0,0,4,2,0)
  D := [[0, 0, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_80_115 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨80, by decide⟩
  m := 1
  T1 := T147_80
  T2 := Q2.T147_80_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 0, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_80_120 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨80, by decide⟩
  m := 1
  T1 := T147_80
  T2 := Q2.T147_80_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 0, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_81_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨81, by decide⟩
  m := 1
  T1 := T147_81
  T2 := Q2.T147_81_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_81_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨81, by decide⟩
  m := 1
  T1 := T147_81
  T2 := Q2.T147_81_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_81_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨81, by decide⟩
  m := 1
  T1 := T147_81
  T2 := Q2.T147_81_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_81_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨81, by decide⟩
  m := 1
  T1 := T147_81
  T2 := Q2.T147_81_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_81_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨81, by decide⟩
  m := 1
  T1 := T147_81
  T2 := Q2.T147_81_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_81_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨81, by decide⟩
  m := 1
  T1 := T147_81
  T2 := Q2.T147_81_2
  h1 := (1,0,4,0,0)
  h2 := (1,0,4,0,0)
  D := [[1, 0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_81_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨81, by decide⟩
  m := 1
  T1 := T147_81
  T2 := Q2.T147_81_2
  h1 := (2,0,3,0,0)
  h2 := (2,0,3,0,0)
  D := [[2, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_81_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨81, by decide⟩
  m := 1
  T1 := T147_81
  T2 := Q2.T147_81_2
  h1 := (3,0,2,0,0)
  h2 := (3,0,2,0,0)
  D := [[3, 0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_81_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨81, by decide⟩
  m := 1
  T1 := T147_81
  T2 := Q2.T147_81_2
  h1 := (4,0,1,0,0)
  h2 := (4,0,1,0,0)
  D := [[4, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_82_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨82, by decide⟩
  m := 1
  T1 := T147_82
  T2 := Q2.T147_82_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_82_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨82, by decide⟩
  m := 1
  T1 := T147_82
  T2 := Q2.T147_82_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_82_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨82, by decide⟩
  m := 1
  T1 := T147_82
  T2 := Q2.T147_82_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_82_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨82, by decide⟩
  m := 1
  T1 := T147_82
  T2 := Q2.T147_82_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_82_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨82, by decide⟩
  m := 1
  T1 := T147_82
  T2 := Q2.T147_82_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_82_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨82, by decide⟩
  m := 1
  T1 := T147_82
  T2 := Q2.T147_82_2
  h1 := (1,0,2,0,0)
  h2 := (1,0,2,0,0)
  D := [[1, 0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_82_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨82, by decide⟩
  m := 1
  T1 := T147_82
  T2 := Q2.T147_82_2
  h1 := (2,0,4,0,0)
  h2 := (2,0,4,0,0)
  D := [[2, 0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_82_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨82, by decide⟩
  m := 1
  T1 := T147_82
  T2 := Q2.T147_82_2
  h1 := (3,0,1,0,0)
  h2 := (3,0,1,0,0)
  D := [[3, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_82_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨82, by decide⟩
  m := 1
  T1 := T147_82
  T2 := Q2.T147_82_2
  h1 := (4,0,3,0,0)
  h2 := (4,0,3,0,0)
  D := [[4, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_83_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨83, by decide⟩
  m := 1
  T1 := T147_83
  T2 := Q2.T147_83_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_83_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨83, by decide⟩
  m := 1
  T1 := T147_83
  T2 := Q2.T147_83_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_83_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨83, by decide⟩
  m := 1
  T1 := T147_83
  T2 := Q2.T147_83_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_83_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨83, by decide⟩
  m := 1
  T1 := T147_83
  T2 := Q2.T147_83_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_83_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨83, by decide⟩
  m := 1
  T1 := T147_83
  T2 := Q2.T147_83_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_83_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨83, by decide⟩
  m := 1
  T1 := T147_83
  T2 := Q2.T147_83_2
  h1 := (1,0,3,0,0)
  h2 := (1,0,3,0,0)
  D := [[1, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_83_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨83, by decide⟩
  m := 1
  T1 := T147_83
  T2 := Q2.T147_83_2
  h1 := (2,0,1,0,0)
  h2 := (2,0,1,0,0)
  D := [[2, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_83_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨83, by decide⟩
  m := 1
  T1 := T147_83
  T2 := Q2.T147_83_2
  h1 := (3,0,4,0,0)
  h2 := (3,0,4,0,0)
  D := [[3, 0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_83_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨83, by decide⟩
  m := 1
  T1 := T147_83
  T2 := Q2.T147_83_2
  h1 := (4,0,2,0,0)
  h2 := (4,0,2,0,0)
  D := [[4, 0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_84_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨84, by decide⟩
  m := 1
  T1 := T147_84
  T2 := Q2.T147_84_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_84_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨84, by decide⟩
  m := 1
  T1 := T147_84
  T2 := Q2.T147_84_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_84_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨84, by decide⟩
  m := 1
  T1 := T147_84
  T2 := Q2.T147_84_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_84_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨84, by decide⟩
  m := 1
  T1 := T147_84
  T2 := Q2.T147_84_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_84_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨84, by decide⟩
  m := 1
  T1 := T147_84
  T2 := Q2.T147_84_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_84_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨84, by decide⟩
  m := 1
  T1 := T147_84
  T2 := Q2.T147_84_2
  h1 := (1,0,1,0,0)
  h2 := (1,0,1,0,0)
  D := [[1, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_84_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨84, by decide⟩
  m := 1
  T1 := T147_84
  T2 := Q2.T147_84_2
  h1 := (2,0,2,0,0)
  h2 := (2,0,2,0,0)
  D := [[2, 0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_84_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨84, by decide⟩
  m := 1
  T1 := T147_84
  T2 := Q2.T147_84_2
  h1 := (3,0,3,0,0)
  h2 := (3,0,3,0,0)
  D := [[3, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_84_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨84, by decide⟩
  m := 1
  T1 := T147_84
  T2 := Q2.T147_84_2
  h1 := (4,0,4,0,0)
  h2 := (4,0,4,0,0)
  D := [[4, 0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_85_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨85, by decide⟩
  m := 1
  T1 := T147_85
  T2 := Q2.T147_85_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_85_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨85, by decide⟩
  m := 1
  T1 := T147_85
  T2 := Q2.T147_85_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_85_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨85, by decide⟩
  m := 1
  T1 := T147_85
  T2 := Q2.T147_85_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_85_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨85, by decide⟩
  m := 1
  T1 := T147_85
  T2 := Q2.T147_85_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_85_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨85, by decide⟩
  m := 1
  T1 := T147_85
  T2 := Q2.T147_85_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_85_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨85, by decide⟩
  m := 1
  T1 := T147_85
  T2 := Q2.T147_85_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_85_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨85, by decide⟩
  m := 1
  T1 := T147_85
  T2 := Q2.T147_85_2
  h1 := (0,0,1,0,1)
  h2 := (0,0,1,0,1)
  D := [[0, 0, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
