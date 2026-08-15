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
rest tier, chunk 82: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_138_44_3 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T138_44
  T2 := Q2.T138_44_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_44_4 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T138_44
  T2 := Q2.T138_44_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_44_20 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T138_44
  T2 := Q2.T138_44_2
  h1 := (4,1,1,1,3)
  h2 := (4,1,1,1,1)
  D := [[4, 1, 0, 3], [4, 1, 0, 2], [4, 1, 0, 1], [4, 1, 0, 0], [4, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_50_0 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T138_50
  T2 := Q2.T138_50_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_50_1 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T138_50
  T2 := Q2.T138_50_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_50_2 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T138_50
  T2 := Q2.T138_50_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_50_3 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T138_50
  T2 := Q2.T138_50_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_50_4 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T138_50
  T2 := Q2.T138_50_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_53_0 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T138_53
  T2 := Q2.T138_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_53_1 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T138_53
  T2 := Q2.T138_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_53_2 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T138_53
  T2 := Q2.T138_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_53_3 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T138_53
  T2 := Q2.T138_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_53_4 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T138_53
  T2 := Q2.T138_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_53_5 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T138_53
  T2 := Q2.T138_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_53_10 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T138_53
  T2 := Q2.T138_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_53_15 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T138_53
  T2 := Q2.T138_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_53_20 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T138_53
  T2 := Q2.T138_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_84_0 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T138_84
  T2 := Q2.T138_84_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_84_1 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T138_84
  T2 := Q2.T138_84_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_84_2 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T138_84
  T2 := Q2.T138_84_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_84_3 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T138_84
  T2 := Q2.T138_84_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_84_4 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T138_84
  T2 := Q2.T138_84_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_93_0 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T138_93
  T2 := Q2.T138_93_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_93_1 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T138_93
  T2 := Q2.T138_93_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_93_2 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T138_93
  T2 := Q2.T138_93_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_93_3 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T138_93
  T2 := Q2.T138_93_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_93_4 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T138_93
  T2 := Q2.T138_93_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_95_0 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T138_95
  T2 := Q2.T138_95_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_95_1 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T138_95
  T2 := Q2.T138_95_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_95_2 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T138_95
  T2 := Q2.T138_95_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_95_3 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T138_95
  T2 := Q2.T138_95_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_95_4 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T138_95
  T2 := Q2.T138_95_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_95_5 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T138_95
  T2 := Q2.T138_95_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_95_10 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T138_95
  T2 := Q2.T138_95_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_95_15 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T138_95
  T2 := Q2.T138_95_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_95_20 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T138_95
  T2 := Q2.T138_95_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_104_0 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T138_104
  T2 := Q2.T138_104_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_104_1 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T138_104
  T2 := Q2.T138_104_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_104_2 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T138_104
  T2 := Q2.T138_104_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_104_3 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T138_104
  T2 := Q2.T138_104_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_104_4 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T138_104
  T2 := Q2.T138_104_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_106_0 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T138_106
  T2 := Q2.T138_106_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_106_1 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T138_106
  T2 := Q2.T138_106_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_106_2 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T138_106
  T2 := Q2.T138_106_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_106_3 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T138_106
  T2 := Q2.T138_106_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_106_4 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T138_106
  T2 := Q2.T138_106_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_106_20 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T138_106
  T2 := Q2.T138_106_2
  h1 := (4,1,1,0,3)
  h2 := (4,1,1,0,1)
  D := [[4, 1, 4, 2], [4, 1, 4, 1], [4, 1, 4, 0], [4, 1, 4, 4], [4, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_112_0 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T138_112
  T2 := Q2.T138_112_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_112_1 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T138_112
  T2 := Q2.T138_112_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_112_2 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T138_112
  T2 := Q2.T138_112_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_112_3 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T138_112
  T2 := Q2.T138_112_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_112_4 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T138_112
  T2 := Q2.T138_112_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_112_5 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T138_112
  T2 := Q2.T138_112_2
  h1 := (1,2,0,3,3)
  h2 := (1,2,0,3,3)
  D := [[1, 2, 3, 3], [1, 2, 3, 1], [1, 2, 3, 4], [1, 2, 3, 2], [1, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_112_10 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T138_112
  T2 := Q2.T138_112_2
  h1 := (2,4,0,3,4)
  h2 := (2,4,0,3,4)
  D := [[2, 4, 4, 2], [2, 4, 4, 3], [2, 4, 4, 4], [2, 4, 4, 0], [2, 4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_138_0 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨138, by decide⟩
  m := 5
  T1 := T138_138
  T2 := Q2.T138_138_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_138_1 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨138, by decide⟩
  m := 5
  T1 := T138_138
  T2 := Q2.T138_138_2
  h1 := (0,1,2,0,4)
  h2 := (0,1,2,0,0)
  D := [[0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_138_2 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨138, by decide⟩
  m := 5
  T1 := T138_138
  T2 := Q2.T138_138_2
  h1 := (0,2,4,0,0)
  h2 := (0,2,4,0,2)
  D := [[0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_138_3 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨138, by decide⟩
  m := 5
  T1 := T138_138
  T2 := Q2.T138_138_2
  h1 := (0,3,1,0,3)
  h2 := (0,3,1,0,1)
  D := [[0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_138_4 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨138, by decide⟩
  m := 5
  T1 := T138_138
  T2 := Q2.T138_138_2
  h1 := (0,4,3,0,3)
  h2 := (0,4,3,0,2)
  D := [[0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_138_138_5 : ColCert where
  rK := ⟨138, by decide⟩
  rH := ⟨138, by decide⟩
  m := 5
  T1 := T138_138
  T2 := Q2.T138_138_2
  h1 := (1,0,1,3,1)
  h2 := (1,0,1,3,4)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
