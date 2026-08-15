/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C038

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 84: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_139_45_15 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T139_45
  T2 := Q2.T139_45_2
  h1 := (3,1,1,2,4)
  h2 := (3,1,1,2,1)
  D := [[3, 1, 1, 2], [3, 1, 1, 1], [3, 1, 1, 0], [3, 1, 1, 4], [3, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_51_0 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T139_51
  T2 := Q2.T139_51_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_51_1 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T139_51
  T2 := Q2.T139_51_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_51_2 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T139_51
  T2 := Q2.T139_51_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_51_3 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T139_51
  T2 := Q2.T139_51_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_51_4 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T139_51
  T2 := Q2.T139_51_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_53_0 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T139_53
  T2 := Q2.T139_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_53_1 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T139_53
  T2 := Q2.T139_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_53_2 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T139_53
  T2 := Q2.T139_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_53_3 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T139_53
  T2 := Q2.T139_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_53_4 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T139_53
  T2 := Q2.T139_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_53_5 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T139_53
  T2 := Q2.T139_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_53_10 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T139_53
  T2 := Q2.T139_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_53_15 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T139_53
  T2 := Q2.T139_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_53_20 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T139_53
  T2 := Q2.T139_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_84_0 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T139_84
  T2 := Q2.T139_84_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_84_1 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T139_84
  T2 := Q2.T139_84_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_84_2 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T139_84
  T2 := Q2.T139_84_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_84_3 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T139_84
  T2 := Q2.T139_84_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_84_4 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T139_84
  T2 := Q2.T139_84_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_94_0 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T139_94
  T2 := Q2.T139_94_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_94_1 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T139_94
  T2 := Q2.T139_94_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_94_2 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T139_94
  T2 := Q2.T139_94_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_94_3 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T139_94
  T2 := Q2.T139_94_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_94_4 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T139_94
  T2 := Q2.T139_94_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_96_0 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T139_96
  T2 := Q2.T139_96_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_96_1 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T139_96
  T2 := Q2.T139_96_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_96_2 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T139_96
  T2 := Q2.T139_96_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_96_3 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T139_96
  T2 := Q2.T139_96_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_96_4 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T139_96
  T2 := Q2.T139_96_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_100_0 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T139_100
  T2 := Q2.T139_100_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_100_1 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T139_100
  T2 := Q2.T139_100_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_100_2 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T139_100
  T2 := Q2.T139_100_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_100_3 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T139_100
  T2 := Q2.T139_100_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_100_4 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T139_100
  T2 := Q2.T139_100_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_100_5 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T139_100
  T2 := Q2.T139_100_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_100_10 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T139_100
  T2 := Q2.T139_100_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_100_15 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T139_100
  T2 := Q2.T139_100_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_100_20 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T139_100
  T2 := Q2.T139_100_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_107_0 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T139_107
  T2 := Q2.T139_107_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_107_1 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T139_107
  T2 := Q2.T139_107_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_107_2 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T139_107
  T2 := Q2.T139_107_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_107_3 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T139_107
  T2 := Q2.T139_107_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_107_4 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T139_107
  T2 := Q2.T139_107_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_107_20 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T139_107
  T2 := Q2.T139_107_2
  h1 := (4,3,3,4,2)
  h2 := (4,3,3,4,3)
  D := [[4, 3, 3, 3], [4, 3, 3, 0], [4, 3, 3, 2], [4, 3, 3, 4], [4, 3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_113_0 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T139_113
  T2 := Q2.T139_113_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_113_1 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T139_113
  T2 := Q2.T139_113_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_113_2 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T139_113
  T2 := Q2.T139_113_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_113_3 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T139_113
  T2 := Q2.T139_113_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_113_4 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T139_113
  T2 := Q2.T139_113_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_113_5 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T139_113
  T2 := Q2.T139_113_2
  h1 := (1,3,0,1,2)
  h2 := (1,3,0,1,2)
  D := [[1, 3, 2, 4], [1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0], [1, 3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_139_0 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨139, by decide⟩
  m := 5
  T1 := T139_139
  T2 := Q2.T139_139_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_139_1 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨139, by decide⟩
  m := 5
  T1 := T139_139
  T2 := Q2.T139_139_2
  h1 := (0,1,3,0,2)
  h2 := (0,1,3,0,3)
  D := [[0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_139_2 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨139, by decide⟩
  m := 5
  T1 := T139_139
  T2 := Q2.T139_139_2
  h1 := (0,2,1,0,2)
  h2 := (0,2,1,0,4)
  D := [[0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_139_3 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨139, by decide⟩
  m := 5
  T1 := T139_139
  T2 := Q2.T139_139_2
  h1 := (0,3,4,0,0)
  h2 := (0,3,4,0,3)
  D := [[0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_139_4 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨139, by decide⟩
  m := 5
  T1 := T139_139
  T2 := Q2.T139_139_2
  h1 := (0,4,2,0,1)
  h2 := (0,4,2,0,0)
  D := [[0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_139_5 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨139, by decide⟩
  m := 5
  T1 := T139_139
  T2 := Q2.T139_139_2
  h1 := (1,0,1,1,4)
  h2 := (1,0,1,1,1)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_139_6 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨139, by decide⟩
  m := 5
  T1 := T139_139
  T2 := Q2.T139_139_2
  h1 := (1,1,4,1,2)
  h2 := (1,1,4,1,0)
  D := [[1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1], [1, 1, 4, 0], [1, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_139_7 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨139, by decide⟩
  m := 5
  T1 := T139_139
  T2 := Q2.T139_139_2
  h1 := (1,2,2,1,3)
  h2 := (1,2,2,1,2)
  D := [[1, 2, 3, 1], [1, 2, 3, 4], [1, 2, 3, 2], [1, 2, 3, 0], [1, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_139_139_8 : ColCert where
  rK := ⟨139, by decide⟩
  rH := ⟨139, by decide⟩
  m := 5
  T1 := T139_139
  T2 := Q2.T139_139_2
  h1 := (1,3,0,1,2)
  h2 := (1,3,0,1,2)
  D := [[1, 3, 2, 4], [1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0], [1, 3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
