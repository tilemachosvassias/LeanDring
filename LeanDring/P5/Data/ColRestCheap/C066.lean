/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C034

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 65: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_130_36_3 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T130_36
  T2 := Q2.T130_36_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_36_4 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T130_36
  T2 := Q2.T130_36_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_38_0 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T130_38
  T2 := Q2.T130_38_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_38_1 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T130_38
  T2 := Q2.T130_38_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_38_2 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T130_38
  T2 := Q2.T130_38_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_38_3 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T130_38
  T2 := Q2.T130_38_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_38_4 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T130_38
  T2 := Q2.T130_38_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_44_0 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T130_44
  T2 := Q2.T130_44_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_44_1 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T130_44
  T2 := Q2.T130_44_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_44_2 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T130_44
  T2 := Q2.T130_44_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_44_3 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T130_44
  T2 := Q2.T130_44_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_44_4 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T130_44
  T2 := Q2.T130_44_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_44_10 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T130_44
  T2 := Q2.T130_44_2
  h1 := (2,3,3,0,0)
  h2 := (2,3,3,0,1)
  D := [[2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1], [2, 3, 4, 3], [2, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_52_0 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T130_52
  T2 := Q2.T130_52_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_52_1 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T130_52
  T2 := Q2.T130_52_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_52_2 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T130_52
  T2 := Q2.T130_52_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_52_3 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T130_52
  T2 := Q2.T130_52_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_52_4 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T130_52
  T2 := Q2.T130_52_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_53_0 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T130_53
  T2 := Q2.T130_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_53_1 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T130_53
  T2 := Q2.T130_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_53_2 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T130_53
  T2 := Q2.T130_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_53_3 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T130_53
  T2 := Q2.T130_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_53_4 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T130_53
  T2 := Q2.T130_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_53_5 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T130_53
  T2 := Q2.T130_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_53_10 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T130_53
  T2 := Q2.T130_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_53_15 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T130_53
  T2 := Q2.T130_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_53_20 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T130_53
  T2 := Q2.T130_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_82_0 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T130_82
  T2 := Q2.T130_82_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_82_1 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T130_82
  T2 := Q2.T130_82_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_82_2 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T130_82
  T2 := Q2.T130_82_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_82_3 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T130_82
  T2 := Q2.T130_82_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_82_4 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T130_82
  T2 := Q2.T130_82_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_92_0 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T130_92
  T2 := Q2.T130_92_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_92_1 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T130_92
  T2 := Q2.T130_92_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_92_2 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T130_92
  T2 := Q2.T130_92_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_92_3 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T130_92
  T2 := Q2.T130_92_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_92_4 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T130_92
  T2 := Q2.T130_92_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_98_0 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T130_98
  T2 := Q2.T130_98_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_98_1 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T130_98
  T2 := Q2.T130_98_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_98_2 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T130_98
  T2 := Q2.T130_98_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_98_3 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T130_98
  T2 := Q2.T130_98_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_98_4 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T130_98
  T2 := Q2.T130_98_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_98_15 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T130_98
  T2 := Q2.T130_98_2
  h1 := (3,4,3,2,0)
  h2 := (3,4,3,2,1)
  D := [[3, 4, 0, 4], [3, 4, 0, 0], [3, 4, 0, 1], [3, 4, 0, 2], [3, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_100_0 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T130_100
  T2 := Q2.T130_100_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_100_1 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T130_100
  T2 := Q2.T130_100_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_100_2 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T130_100
  T2 := Q2.T130_100_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_100_3 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T130_100
  T2 := Q2.T130_100_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_100_4 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T130_100
  T2 := Q2.T130_100_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_100_5 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T130_100
  T2 := Q2.T130_100_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_100_10 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T130_100
  T2 := Q2.T130_100_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_100_15 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T130_100
  T2 := Q2.T130_100_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_100_20 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T130_100
  T2 := Q2.T130_100_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_106_0 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T130_106
  T2 := Q2.T130_106_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_106_1 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T130_106
  T2 := Q2.T130_106_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_106_2 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T130_106
  T2 := Q2.T130_106_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_106_3 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T130_106
  T2 := Q2.T130_106_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_106_4 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T130_106
  T2 := Q2.T130_106_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_106_10 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T130_106
  T2 := Q2.T130_106_2
  h1 := (2,3,3,2,3)
  h2 := (2,3,3,2,4)
  D := [[2, 3, 1, 1], [2, 3, 1, 3], [2, 3, 1, 0], [2, 3, 1, 2], [2, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_114_0 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T130_114
  T2 := Q2.T130_114_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_114_1 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T130_114
  T2 := Q2.T130_114_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
