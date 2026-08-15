/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C027

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 31: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_118_35_3 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T118_35
  T2 := Q2.T118_35_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_35_4 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T118_35
  T2 := Q2.T118_35_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_40_0 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T118_40
  T2 := Q2.T118_40_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_40_1 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T118_40
  T2 := Q2.T118_40_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_40_2 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T118_40
  T2 := Q2.T118_40_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_40_3 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T118_40
  T2 := Q2.T118_40_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_40_4 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T118_40
  T2 := Q2.T118_40_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_45_0 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T118_45
  T2 := Q2.T118_45_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_45_1 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T118_45
  T2 := Q2.T118_45_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_45_2 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T118_45
  T2 := Q2.T118_45_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_45_3 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T118_45
  T2 := Q2.T118_45_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_45_4 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T118_45
  T2 := Q2.T118_45_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_50_0 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T118_50
  T2 := Q2.T118_50_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_50_1 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T118_50
  T2 := Q2.T118_50_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_50_2 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T118_50
  T2 := Q2.T118_50_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_50_3 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T118_50
  T2 := Q2.T118_50_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_50_4 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T118_50
  T2 := Q2.T118_50_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_53_0 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T118_53
  T2 := Q2.T118_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_53_1 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T118_53
  T2 := Q2.T118_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_53_2 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T118_53
  T2 := Q2.T118_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_53_3 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T118_53
  T2 := Q2.T118_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_53_4 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T118_53
  T2 := Q2.T118_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_53_5 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T118_53
  T2 := Q2.T118_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_53_10 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T118_53
  T2 := Q2.T118_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_53_15 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T118_53
  T2 := Q2.T118_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_53_20 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T118_53
  T2 := Q2.T118_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_65_0 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨65, by decide⟩
  m := 5
  T1 := T118_65
  T2 := Q2.T118_65_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_65_1 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨65, by decide⟩
  m := 5
  T1 := T118_65
  T2 := Q2.T118_65_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 1, 0, 2], [0, 1, 0, 3], [0, 1, 0, 4], [0, 1, 0, 0], [0, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_65_2 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨65, by decide⟩
  m := 5
  T1 := T118_65
  T2 := Q2.T118_65_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 2, 0, 4], [0, 2, 0, 1], [0, 2, 0, 3], [0, 2, 0, 0], [0, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_65_3 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨65, by decide⟩
  m := 5
  T1 := T118_65
  T2 := Q2.T118_65_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 3, 0, 1], [0, 3, 0, 4], [0, 3, 0, 2], [0, 3, 0, 0], [0, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_65_4 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨65, by decide⟩
  m := 5
  T1 := T118_65
  T2 := Q2.T118_65_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 4, 0, 3], [0, 4, 0, 2], [0, 4, 0, 1], [0, 4, 0, 0], [0, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_66_0 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T118_66
  T2 := Q2.T118_66_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_66_1 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T118_66
  T2 := Q2.T118_66_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 1, 4, 2], [0, 1, 4, 3], [0, 1, 4, 4], [0, 1, 4, 0], [0, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_66_2 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T118_66
  T2 := Q2.T118_66_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 2, 3, 4], [0, 2, 3, 1], [0, 2, 3, 3], [0, 2, 3, 0], [0, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_66_3 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T118_66
  T2 := Q2.T118_66_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 3, 2, 1], [0, 3, 2, 4], [0, 3, 2, 2], [0, 3, 2, 0], [0, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_66_4 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨66, by decide⟩
  m := 5
  T1 := T118_66
  T2 := Q2.T118_66_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 4, 1, 3], [0, 4, 1, 2], [0, 4, 1, 1], [0, 4, 1, 0], [0, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_67_0 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨67, by decide⟩
  m := 5
  T1 := T118_67
  T2 := Q2.T118_67_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_67_1 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨67, by decide⟩
  m := 5
  T1 := T118_67
  T2 := Q2.T118_67_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_67_2 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨67, by decide⟩
  m := 5
  T1 := T118_67
  T2 := Q2.T118_67_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_67_3 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨67, by decide⟩
  m := 5
  T1 := T118_67
  T2 := Q2.T118_67_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_67_4 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨67, by decide⟩
  m := 5
  T1 := T118_67
  T2 := Q2.T118_67_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_67_5 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨67, by decide⟩
  m := 5
  T1 := T118_67
  T2 := Q2.T118_67_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 1, 3, 2], [0, 1, 3, 3], [0, 1, 3, 4], [0, 1, 3, 0], [0, 1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_67_6 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨67, by decide⟩
  m := 5
  T1 := T118_67
  T2 := Q2.T118_67_2
  h1 := (0,0,1,3,1)
  h2 := (0,0,1,3,1)
  D := [[0, 1, 3, 3], [0, 1, 3, 4], [0, 1, 3, 0], [0, 1, 3, 1], [0, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_67_7 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨67, by decide⟩
  m := 5
  T1 := T118_67
  T2 := Q2.T118_67_2
  h1 := (0,0,1,3,2)
  h2 := (0,0,1,3,2)
  D := [[0, 1, 3, 4], [0, 1, 3, 0], [0, 1, 3, 1], [0, 1, 3, 2], [0, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_67_8 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨67, by decide⟩
  m := 5
  T1 := T118_67
  T2 := Q2.T118_67_2
  h1 := (0,0,1,3,3)
  h2 := (0,0,1,3,3)
  D := [[0, 1, 3, 0], [0, 1, 3, 1], [0, 1, 3, 2], [0, 1, 3, 3], [0, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_67_9 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨67, by decide⟩
  m := 5
  T1 := T118_67
  T2 := Q2.T118_67_2
  h1 := (0,0,1,3,4)
  h2 := (0,0,1,3,4)
  D := [[0, 1, 3, 1], [0, 1, 3, 2], [0, 1, 3, 3], [0, 1, 3, 4], [0, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_67_10 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨67, by decide⟩
  m := 5
  T1 := T118_67
  T2 := Q2.T118_67_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 2, 1, 4], [0, 2, 1, 1], [0, 2, 1, 3], [0, 2, 1, 0], [0, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_67_11 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨67, by decide⟩
  m := 5
  T1 := T118_67
  T2 := Q2.T118_67_2
  h1 := (0,0,2,1,1)
  h2 := (0,0,2,1,1)
  D := [[0, 2, 1, 0], [0, 2, 1, 2], [0, 2, 1, 4], [0, 2, 1, 1], [0, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_67_12 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨67, by decide⟩
  m := 5
  T1 := T118_67
  T2 := Q2.T118_67_2
  h1 := (0,0,2,1,2)
  h2 := (0,0,2,1,2)
  D := [[0, 2, 1, 1], [0, 2, 1, 3], [0, 2, 1, 0], [0, 2, 1, 2], [0, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_67_13 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨67, by decide⟩
  m := 5
  T1 := T118_67
  T2 := Q2.T118_67_2
  h1 := (0,0,2,1,3)
  h2 := (0,0,2,1,3)
  D := [[0, 2, 1, 2], [0, 2, 1, 4], [0, 2, 1, 1], [0, 2, 1, 3], [0, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_67_14 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨67, by decide⟩
  m := 5
  T1 := T118_67
  T2 := Q2.T118_67_2
  h1 := (0,0,2,1,4)
  h2 := (0,0,2,1,4)
  D := [[0, 2, 1, 3], [0, 2, 1, 0], [0, 2, 1, 2], [0, 2, 1, 4], [0, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_67_15 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨67, by decide⟩
  m := 5
  T1 := T118_67
  T2 := Q2.T118_67_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 3, 4, 1], [0, 3, 4, 4], [0, 3, 4, 2], [0, 3, 4, 0], [0, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_67_16 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨67, by decide⟩
  m := 5
  T1 := T118_67
  T2 := Q2.T118_67_2
  h1 := (0,0,3,4,1)
  h2 := (0,0,3,4,1)
  D := [[0, 3, 4, 2], [0, 3, 4, 0], [0, 3, 4, 3], [0, 3, 4, 1], [0, 3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_67_17 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨67, by decide⟩
  m := 5
  T1 := T118_67
  T2 := Q2.T118_67_2
  h1 := (0,0,3,4,2)
  h2 := (0,0,3,4,2)
  D := [[0, 3, 4, 3], [0, 3, 4, 1], [0, 3, 4, 4], [0, 3, 4, 2], [0, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_67_18 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨67, by decide⟩
  m := 5
  T1 := T118_67
  T2 := Q2.T118_67_2
  h1 := (0,0,3,4,3)
  h2 := (0,0,3,4,3)
  D := [[0, 3, 4, 4], [0, 3, 4, 2], [0, 3, 4, 0], [0, 3, 4, 3], [0, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_67_19 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨67, by decide⟩
  m := 5
  T1 := T118_67
  T2 := Q2.T118_67_2
  h1 := (0,0,3,4,4)
  h2 := (0,0,3,4,4)
  D := [[0, 3, 4, 0], [0, 3, 4, 3], [0, 3, 4, 1], [0, 3, 4, 4], [0, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_67_20 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨67, by decide⟩
  m := 5
  T1 := T118_67
  T2 := Q2.T118_67_2
  h1 := (0,0,4,2,0)
  h2 := (0,0,4,2,0)
  D := [[0, 4, 2, 3], [0, 4, 2, 2], [0, 4, 2, 1], [0, 4, 2, 0], [0, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_67_21 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨67, by decide⟩
  m := 5
  T1 := T118_67
  T2 := Q2.T118_67_2
  h1 := (0,0,4,2,1)
  h2 := (0,0,4,2,1)
  D := [[0, 4, 2, 4], [0, 4, 2, 3], [0, 4, 2, 2], [0, 4, 2, 1], [0, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_67_22 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨67, by decide⟩
  m := 5
  T1 := T118_67
  T2 := Q2.T118_67_2
  h1 := (0,0,4,2,2)
  h2 := (0,0,4,2,2)
  D := [[0, 4, 2, 0], [0, 4, 2, 4], [0, 4, 2, 3], [0, 4, 2, 2], [0, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_118_67_23 : ColCert where
  rK := ⟨118, by decide⟩
  rH := ⟨67, by decide⟩
  m := 5
  T1 := T118_67
  T2 := Q2.T118_67_2
  h1 := (0,0,4,2,3)
  h2 := (0,0,4,2,3)
  D := [[0, 4, 2, 1], [0, 4, 2, 0], [0, 4, 2, 4], [0, 4, 2, 3], [0, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
