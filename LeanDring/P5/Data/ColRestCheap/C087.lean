/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C039

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 86: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_140_52_1 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T140_52
  T2 := Q2.T140_52_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_52_2 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T140_52
  T2 := Q2.T140_52_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_52_3 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T140_52
  T2 := Q2.T140_52_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_52_4 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T140_52
  T2 := Q2.T140_52_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_53_0 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T140_53
  T2 := Q2.T140_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_53_1 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T140_53
  T2 := Q2.T140_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_53_2 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T140_53
  T2 := Q2.T140_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_53_3 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T140_53
  T2 := Q2.T140_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_53_4 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T140_53
  T2 := Q2.T140_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_53_5 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T140_53
  T2 := Q2.T140_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_53_10 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T140_53
  T2 := Q2.T140_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_53_15 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T140_53
  T2 := Q2.T140_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_53_20 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T140_53
  T2 := Q2.T140_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_84_0 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T140_84
  T2 := Q2.T140_84_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_84_1 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T140_84
  T2 := Q2.T140_84_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_84_2 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T140_84
  T2 := Q2.T140_84_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_84_3 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T140_84
  T2 := Q2.T140_84_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_84_4 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T140_84
  T2 := Q2.T140_84_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_90_0 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T140_90
  T2 := Q2.T140_90_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_90_1 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T140_90
  T2 := Q2.T140_90_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_90_2 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T140_90
  T2 := Q2.T140_90_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_90_3 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T140_90
  T2 := Q2.T140_90_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_90_4 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T140_90
  T2 := Q2.T140_90_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_90_5 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T140_90
  T2 := Q2.T140_90_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_90_10 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T140_90
  T2 := Q2.T140_90_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_90_15 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T140_90
  T2 := Q2.T140_90_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_90_20 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T140_90
  T2 := Q2.T140_90_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_97_0 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T140_97
  T2 := Q2.T140_97_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_97_1 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T140_97
  T2 := Q2.T140_97_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_97_2 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T140_97
  T2 := Q2.T140_97_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_97_3 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T140_97
  T2 := Q2.T140_97_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_97_4 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T140_97
  T2 := Q2.T140_97_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_101_0 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T140_101
  T2 := Q2.T140_101_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_101_1 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T140_101
  T2 := Q2.T140_101_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_101_2 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T140_101
  T2 := Q2.T140_101_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_101_3 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T140_101
  T2 := Q2.T140_101_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_101_4 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T140_101
  T2 := Q2.T140_101_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_101_15 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T140_101
  T2 := Q2.T140_101_2
  h1 := (3,2,1,4,1)
  h2 := (3,2,1,4,3)
  D := [[3, 2, 3, 2], [3, 2, 3, 0], [3, 2, 3, 3], [3, 2, 3, 1], [3, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_108_0 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T140_108
  T2 := Q2.T140_108_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_108_1 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T140_108
  T2 := Q2.T140_108_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_108_2 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T140_108
  T2 := Q2.T140_108_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_108_3 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T140_108
  T2 := Q2.T140_108_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_108_4 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T140_108
  T2 := Q2.T140_108_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_114_0 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T140_114
  T2 := Q2.T140_114_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_114_1 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T140_114
  T2 := Q2.T140_114_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_114_2 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T140_114
  T2 := Q2.T140_114_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_114_3 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T140_114
  T2 := Q2.T140_114_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_114_4 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T140_114
  T2 := Q2.T140_114_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_114_5 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T140_114
  T2 := Q2.T140_114_2
  h1 := (1,1,0,0,0)
  h2 := (1,1,0,0,0)
  D := [[1, 1, 4, 2], [1, 1, 4, 1], [1, 1, 4, 0], [1, 1, 4, 4], [1, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_114_10 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T140_114
  T2 := Q2.T140_114_2
  h1 := (2,2,0,1,0)
  h2 := (2,2,0,1,0)
  D := [[2, 2, 2, 2], [2, 2, 2, 0], [2, 2, 2, 3], [2, 2, 2, 1], [2, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_114_15 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T140_114
  T2 := Q2.T140_114_2
  h1 := (3,3,0,3,1)
  h2 := (3,3,0,3,1)
  D := [[3, 3, 4, 1], [3, 3, 4, 3], [3, 3, 4, 0], [3, 3, 4, 2], [3, 3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_114_20 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T140_114
  T2 := Q2.T140_114_2
  h1 := (4,4,0,1,4)
  h2 := (4,4,0,1,4)
  D := [[4, 4, 0, 0], [4, 4, 0, 1], [4, 4, 0, 2], [4, 4, 0, 3], [4, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_140_0 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨140, by decide⟩
  m := 5
  T1 := T140_140
  T2 := Q2.T140_140_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_140_1 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨140, by decide⟩
  m := 5
  T1 := T140_140
  T2 := Q2.T140_140_2
  h1 := (0,1,4,0,2)
  h2 := (0,1,4,0,0)
  D := [[0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_140_2 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨140, by decide⟩
  m := 5
  T1 := T140_140
  T2 := Q2.T140_140_2
  h1 := (0,2,3,0,3)
  h2 := (0,2,3,0,4)
  D := [[0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_140_3 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨140, by decide⟩
  m := 5
  T1 := T140_140
  T2 := Q2.T140_140_2
  h1 := (0,3,2,0,3)
  h2 := (0,3,2,0,2)
  D := [[0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_140_4 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨140, by decide⟩
  m := 5
  T1 := T140_140
  T2 := Q2.T140_140_2
  h1 := (0,4,1,0,2)
  h2 := (0,4,1,0,4)
  D := [[0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_140_5 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨140, by decide⟩
  m := 5
  T1 := T140_140
  T2 := Q2.T140_140_2
  h1 := (1,0,1,0,2)
  h2 := (1,0,1,0,4)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_140_6 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨140, by decide⟩
  m := 5
  T1 := T140_140
  T2 := Q2.T140_140_2
  h1 := (1,1,0,0,0)
  h2 := (1,1,0,0,0)
  D := [[1, 1, 4, 2], [1, 1, 4, 1], [1, 1, 4, 0], [1, 1, 4, 4], [1, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_140_140_7 : ColCert where
  rK := ⟨140, by decide⟩
  rH := ⟨140, by decide⟩
  m := 5
  T1 := T140_140
  T2 := Q2.T140_140_2
  h1 := (1,2,4,0,2)
  h2 := (1,2,4,0,0)
  D := [[1, 2, 3, 4], [1, 2, 3, 2], [1, 2, 3, 0], [1, 2, 3, 3], [1, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
