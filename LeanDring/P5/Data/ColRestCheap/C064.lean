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
rest tier, chunk 63: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_129_43_0 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T129_43
  T2 := Q2.T129_43_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_43_1 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T129_43
  T2 := Q2.T129_43_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_43_2 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T129_43
  T2 := Q2.T129_43_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_43_3 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T129_43
  T2 := Q2.T129_43_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_43_4 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T129_43
  T2 := Q2.T129_43_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_51_0 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T129_51
  T2 := Q2.T129_51_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_51_1 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T129_51
  T2 := Q2.T129_51_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_51_2 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T129_51
  T2 := Q2.T129_51_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_51_3 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T129_51
  T2 := Q2.T129_51_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_51_4 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T129_51
  T2 := Q2.T129_51_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_53_0 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T129_53
  T2 := Q2.T129_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_53_1 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T129_53
  T2 := Q2.T129_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_53_2 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T129_53
  T2 := Q2.T129_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_53_3 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T129_53
  T2 := Q2.T129_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_53_4 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T129_53
  T2 := Q2.T129_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_53_5 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T129_53
  T2 := Q2.T129_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_53_10 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T129_53
  T2 := Q2.T129_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_53_15 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T129_53
  T2 := Q2.T129_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_53_20 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T129_53
  T2 := Q2.T129_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_82_0 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T129_82
  T2 := Q2.T129_82_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_82_1 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T129_82
  T2 := Q2.T129_82_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_82_2 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T129_82
  T2 := Q2.T129_82_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_82_3 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T129_82
  T2 := Q2.T129_82_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_82_4 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T129_82
  T2 := Q2.T129_82_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_82_5 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T129_82
  T2 := Q2.T129_82_2
  h1 := (1,0,2,0,0)
  h2 := (1,0,2,0,0)
  D := [[1, 0, 4, 3], [1, 0, 4, 3], [1, 0, 4, 3], [1, 0, 4, 3], [1, 0, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_82_10 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T129_82
  T2 := Q2.T129_82_2
  h1 := (2,0,4,0,0)
  h2 := (2,0,4,0,0)
  D := [[2, 0, 3, 2], [2, 0, 3, 2], [2, 0, 3, 2], [2, 0, 3, 2], [2, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_82_15 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T129_82
  T2 := Q2.T129_82_2
  h1 := (3,0,1,0,0)
  h2 := (3,0,1,0,0)
  D := [[3, 0, 2, 2], [3, 0, 2, 2], [3, 0, 2, 2], [3, 0, 2, 2], [3, 0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_82_20 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T129_82
  T2 := Q2.T129_82_2
  h1 := (4,0,3,0,0)
  h2 := (4,0,3,0,0)
  D := [[4, 0, 1, 3], [4, 0, 1, 3], [4, 0, 1, 3], [4, 0, 1, 3], [4, 0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_91_0 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T129_91
  T2 := Q2.T129_91_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_91_1 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T129_91
  T2 := Q2.T129_91_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_91_2 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T129_91
  T2 := Q2.T129_91_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_91_3 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T129_91
  T2 := Q2.T129_91_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_91_4 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T129_91
  T2 := Q2.T129_91_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_91_5 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T129_91
  T2 := Q2.T129_91_2
  h1 := (1,4,1,4,4)
  h2 := (1,4,1,4,4)
  D := [[1, 4, 4, 4], [1, 4, 4, 0], [1, 4, 4, 1], [1, 4, 4, 2], [1, 4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_97_0 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T129_97
  T2 := Q2.T129_97_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_97_1 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T129_97
  T2 := Q2.T129_97_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_97_2 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T129_97
  T2 := Q2.T129_97_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_97_3 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T129_97
  T2 := Q2.T129_97_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_97_4 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T129_97
  T2 := Q2.T129_97_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_97_5 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T129_97
  T2 := Q2.T129_97_2
  h1 := (1,2,4,3,0)
  h2 := (1,2,4,3,0)
  D := [[1, 2, 0, 0], [1, 2, 0, 3], [1, 2, 0, 1], [1, 2, 0, 4], [1, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_97_10 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T129_97
  T2 := Q2.T129_97_2
  h1 := (2,4,3,3,1)
  h2 := (2,4,3,3,1)
  D := [[2, 4, 3, 1], [2, 4, 3, 2], [2, 4, 3, 3], [2, 4, 3, 4], [2, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_104_0 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T129_104
  T2 := Q2.T129_104_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_104_1 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T129_104
  T2 := Q2.T129_104_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_104_2 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T129_104
  T2 := Q2.T129_104_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_104_3 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T129_104
  T2 := Q2.T129_104_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_104_4 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T129_104
  T2 := Q2.T129_104_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_104_5 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T129_104
  T2 := Q2.T129_104_2
  h1 := (1,1,3,0,0)
  h2 := (1,1,3,0,0)
  D := [[1, 1, 3, 1], [1, 1, 3, 0], [1, 1, 3, 4], [1, 1, 3, 3], [1, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_104_10 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T129_104
  T2 := Q2.T129_104_2
  h1 := (2,2,1,1,3)
  h2 := (2,2,1,1,3)
  D := [[2, 2, 0, 2], [2, 2, 0, 0], [2, 2, 0, 3], [2, 2, 0, 1], [2, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_104_15 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T129_104
  T2 := Q2.T129_104_2
  h1 := (3,3,4,3,0)
  h2 := (3,3,4,3,0)
  D := [[3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_104_20 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T129_104
  T2 := Q2.T129_104_2
  h1 := (4,4,2,1,2)
  h2 := (4,4,2,1,2)
  D := [[4, 4, 1, 3], [4, 4, 1, 4], [4, 4, 1, 0], [4, 4, 1, 1], [4, 4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_105_0 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T129_105
  T2 := Q2.T129_105_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_105_1 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T129_105
  T2 := Q2.T129_105_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_105_2 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T129_105
  T2 := Q2.T129_105_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_105_3 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T129_105
  T2 := Q2.T129_105_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_105_4 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T129_105
  T2 := Q2.T129_105_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_105_5 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T129_105
  T2 := Q2.T129_105_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_105_10 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T129_105
  T2 := Q2.T129_105_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_105_15 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T129_105
  T2 := Q2.T129_105_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_105_20 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T129_105
  T2 := Q2.T129_105_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_129_105_25 : ColCert where
  rK := ⟨129, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T129_105
  T2 := Q2.T129_105_2
  h1 := (0,1,1,0,0)
  h2 := (0,1,1,0,0)
  D := [[0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
