/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C033

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 61: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_128_47_3 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T128_47
  T2 := Q2.T128_47_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_47_4 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T128_47
  T2 := Q2.T128_47_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_50_0 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T128_50
  T2 := Q2.T128_50_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_50_1 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T128_50
  T2 := Q2.T128_50_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_50_2 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T128_50
  T2 := Q2.T128_50_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_50_3 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T128_50
  T2 := Q2.T128_50_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_50_4 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T128_50
  T2 := Q2.T128_50_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_53_0 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T128_53
  T2 := Q2.T128_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_53_1 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T128_53
  T2 := Q2.T128_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_53_2 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T128_53
  T2 := Q2.T128_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_53_3 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T128_53
  T2 := Q2.T128_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_53_4 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T128_53
  T2 := Q2.T128_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_53_5 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T128_53
  T2 := Q2.T128_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_53_10 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T128_53
  T2 := Q2.T128_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_53_15 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T128_53
  T2 := Q2.T128_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_53_20 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T128_53
  T2 := Q2.T128_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_82_0 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T128_82
  T2 := Q2.T128_82_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_82_1 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T128_82
  T2 := Q2.T128_82_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_82_2 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T128_82
  T2 := Q2.T128_82_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_82_3 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T128_82
  T2 := Q2.T128_82_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_82_4 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T128_82
  T2 := Q2.T128_82_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_90_0 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T128_90
  T2 := Q2.T128_90_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_90_1 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T128_90
  T2 := Q2.T128_90_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_90_2 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T128_90
  T2 := Q2.T128_90_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_90_3 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T128_90
  T2 := Q2.T128_90_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_90_4 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T128_90
  T2 := Q2.T128_90_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_90_5 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T128_90
  T2 := Q2.T128_90_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_90_10 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T128_90
  T2 := Q2.T128_90_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_90_15 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T128_90
  T2 := Q2.T128_90_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_90_20 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T128_90
  T2 := Q2.T128_90_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_96_0 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T128_96
  T2 := Q2.T128_96_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_96_1 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T128_96
  T2 := Q2.T128_96_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_96_2 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T128_96
  T2 := Q2.T128_96_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_96_3 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T128_96
  T2 := Q2.T128_96_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_96_4 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T128_96
  T2 := Q2.T128_96_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_103_0 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T128_103
  T2 := Q2.T128_103_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_103_1 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T128_103
  T2 := Q2.T128_103_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_103_2 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T128_103
  T2 := Q2.T128_103_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_103_3 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T128_103
  T2 := Q2.T128_103_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_103_4 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T128_103
  T2 := Q2.T128_103_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_103_10 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T128_103
  T2 := Q2.T128_103_2
  h1 := (2,1,3,0,1)
  h2 := (2,1,3,0,2)
  D := [[2, 1, 2, 3], [2, 1, 2, 2], [2, 1, 2, 1], [2, 1, 2, 0], [2, 1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_103_20 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T128_103
  T2 := Q2.T128_103_2
  h1 := (4,2,1,2,1)
  h2 := (4,2,1,2,3)
  D := [[4, 2, 2, 4], [4, 2, 2, 2], [4, 2, 2, 0], [4, 2, 2, 3], [4, 2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_109_0 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T128_109
  T2 := Q2.T128_109_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_109_1 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T128_109
  T2 := Q2.T128_109_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_109_2 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T128_109
  T2 := Q2.T128_109_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_109_3 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T128_109
  T2 := Q2.T128_109_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_109_4 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T128_109
  T2 := Q2.T128_109_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_112_0 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T128_112
  T2 := Q2.T128_112_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_112_1 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T128_112
  T2 := Q2.T128_112_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_112_2 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T128_112
  T2 := Q2.T128_112_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_112_3 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T128_112
  T2 := Q2.T128_112_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_112_4 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T128_112
  T2 := Q2.T128_112_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_112_5 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T128_112
  T2 := Q2.T128_112_2
  h1 := (1,2,0,3,3)
  h2 := (1,2,0,3,3)
  D := [[1, 2, 3, 4], [1, 2, 3, 2], [1, 2, 3, 0], [1, 2, 3, 3], [1, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_112_10 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T128_112
  T2 := Q2.T128_112_2
  h1 := (2,4,0,3,4)
  h2 := (2,4,0,3,4)
  D := [[2, 4, 4, 1], [2, 4, 4, 2], [2, 4, 4, 3], [2, 4, 4, 4], [2, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_128_0 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨128, by decide⟩
  m := 5
  T1 := T128_128
  T2 := Q2.T128_128_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_128_1 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨128, by decide⟩
  m := 5
  T1 := T128_128
  T2 := Q2.T128_128_2
  h1 := (0,1,4,0,2)
  h2 := (0,1,4,0,0)
  D := [[0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_128_2 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨128, by decide⟩
  m := 5
  T1 := T128_128
  T2 := Q2.T128_128_2
  h1 := (0,2,3,0,3)
  h2 := (0,2,3,0,4)
  D := [[0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_128_3 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨128, by decide⟩
  m := 5
  T1 := T128_128
  T2 := Q2.T128_128_2
  h1 := (0,3,2,0,3)
  h2 := (0,3,2,0,2)
  D := [[0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_128_4 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨128, by decide⟩
  m := 5
  T1 := T128_128
  T2 := Q2.T128_128_2
  h1 := (0,4,1,0,2)
  h2 := (0,4,1,0,4)
  D := [[0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_128_128_5 : ColCert where
  rK := ⟨128, by decide⟩
  rH := ⟨128, by decide⟩
  m := 5
  T1 := T128_128
  T2 := Q2.T128_128_2
  h1 := (1,0,2,3,1)
  h2 := (1,0,2,3,0)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
