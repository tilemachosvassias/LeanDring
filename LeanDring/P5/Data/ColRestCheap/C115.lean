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
rest tier, chunk 114: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_147_47_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨47, by decide⟩
  m := 1
  T1 := T147_47
  T2 := Q2.T147_47_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_47_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨47, by decide⟩
  m := 1
  T1 := T147_47
  T2 := Q2.T147_47_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_47_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨47, by decide⟩
  m := 1
  T1 := T147_47
  T2 := Q2.T147_47_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_47_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨47, by decide⟩
  m := 1
  T1 := T147_47
  T2 := Q2.T147_47_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_48_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨48, by decide⟩
  m := 1
  T1 := T147_48
  T2 := Q2.T147_48_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_48_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨48, by decide⟩
  m := 1
  T1 := T147_48
  T2 := Q2.T147_48_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_48_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨48, by decide⟩
  m := 1
  T1 := T147_48
  T2 := Q2.T147_48_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_48_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨48, by decide⟩
  m := 1
  T1 := T147_48
  T2 := Q2.T147_48_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_48_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨48, by decide⟩
  m := 1
  T1 := T147_48
  T2 := Q2.T147_48_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_49_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨49, by decide⟩
  m := 1
  T1 := T147_49
  T2 := Q2.T147_49_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_49_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨49, by decide⟩
  m := 1
  T1 := T147_49
  T2 := Q2.T147_49_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_49_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨49, by decide⟩
  m := 1
  T1 := T147_49
  T2 := Q2.T147_49_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_49_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨49, by decide⟩
  m := 1
  T1 := T147_49
  T2 := Q2.T147_49_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_49_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨49, by decide⟩
  m := 1
  T1 := T147_49
  T2 := Q2.T147_49_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_49_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨49, by decide⟩
  m := 1
  T1 := T147_49
  T2 := Q2.T147_49_2
  h1 := (1,4,0,3,4)
  h2 := (1,4,0,3,4)
  D := [[1, 4, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_50_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨50, by decide⟩
  m := 1
  T1 := T147_50
  T2 := Q2.T147_50_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_50_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨50, by decide⟩
  m := 1
  T1 := T147_50
  T2 := Q2.T147_50_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_50_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨50, by decide⟩
  m := 1
  T1 := T147_50
  T2 := Q2.T147_50_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_50_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨50, by decide⟩
  m := 1
  T1 := T147_50
  T2 := Q2.T147_50_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_50_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨50, by decide⟩
  m := 1
  T1 := T147_50
  T2 := Q2.T147_50_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_51_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨51, by decide⟩
  m := 1
  T1 := T147_51
  T2 := Q2.T147_51_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_51_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨51, by decide⟩
  m := 1
  T1 := T147_51
  T2 := Q2.T147_51_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_51_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨51, by decide⟩
  m := 1
  T1 := T147_51
  T2 := Q2.T147_51_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_51_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨51, by decide⟩
  m := 1
  T1 := T147_51
  T2 := Q2.T147_51_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_51_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨51, by decide⟩
  m := 1
  T1 := T147_51
  T2 := Q2.T147_51_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_52_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨52, by decide⟩
  m := 1
  T1 := T147_52
  T2 := Q2.T147_52_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_52_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨52, by decide⟩
  m := 1
  T1 := T147_52
  T2 := Q2.T147_52_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_52_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨52, by decide⟩
  m := 1
  T1 := T147_52
  T2 := Q2.T147_52_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_52_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨52, by decide⟩
  m := 1
  T1 := T147_52
  T2 := Q2.T147_52_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_52_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨52, by decide⟩
  m := 1
  T1 := T147_52
  T2 := Q2.T147_52_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_53_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨53, by decide⟩
  m := 1
  T1 := T147_53
  T2 := Q2.T147_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_53_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨53, by decide⟩
  m := 1
  T1 := T147_53
  T2 := Q2.T147_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_53_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨53, by decide⟩
  m := 1
  T1 := T147_53
  T2 := Q2.T147_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_53_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨53, by decide⟩
  m := 1
  T1 := T147_53
  T2 := Q2.T147_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_53_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨53, by decide⟩
  m := 1
  T1 := T147_53
  T2 := Q2.T147_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_53_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨53, by decide⟩
  m := 1
  T1 := T147_53
  T2 := Q2.T147_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_53_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨53, by decide⟩
  m := 1
  T1 := T147_53
  T2 := Q2.T147_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_53_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨53, by decide⟩
  m := 1
  T1 := T147_53
  T2 := Q2.T147_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_53_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨53, by decide⟩
  m := 1
  T1 := T147_53
  T2 := Q2.T147_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_54_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨54, by decide⟩
  m := 1
  T1 := T147_54
  T2 := Q2.T147_54_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_54_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨54, by decide⟩
  m := 1
  T1 := T147_54
  T2 := Q2.T147_54_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_54_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨54, by decide⟩
  m := 1
  T1 := T147_54
  T2 := Q2.T147_54_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_54_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨54, by decide⟩
  m := 1
  T1 := T147_54
  T2 := Q2.T147_54_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_54_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨54, by decide⟩
  m := 1
  T1 := T147_54
  T2 := Q2.T147_54_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_54_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨54, by decide⟩
  m := 1
  T1 := T147_54
  T2 := Q2.T147_54_2
  h1 := (1,0,0,4,4)
  h2 := (1,0,0,4,4)
  D := [[1, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_54_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨54, by decide⟩
  m := 1
  T1 := T147_54
  T2 := Q2.T147_54_2
  h1 := (2,0,0,3,2)
  h2 := (2,0,0,3,2)
  D := [[2, 0, 0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_54_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨54, by decide⟩
  m := 1
  T1 := T147_54
  T2 := Q2.T147_54_2
  h1 := (3,0,0,2,4)
  h2 := (3,0,0,2,4)
  D := [[3, 0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_54_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨54, by decide⟩
  m := 1
  T1 := T147_54
  T2 := Q2.T147_54_2
  h1 := (4,0,0,1,0)
  h2 := (4,0,0,1,0)
  D := [[4, 0, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_55_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨55, by decide⟩
  m := 1
  T1 := T147_55
  T2 := Q2.T147_55_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_55_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨55, by decide⟩
  m := 1
  T1 := T147_55
  T2 := Q2.T147_55_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_55_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨55, by decide⟩
  m := 1
  T1 := T147_55
  T2 := Q2.T147_55_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_55_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨55, by decide⟩
  m := 1
  T1 := T147_55
  T2 := Q2.T147_55_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_55_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨55, by decide⟩
  m := 1
  T1 := T147_55
  T2 := Q2.T147_55_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_56_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨56, by decide⟩
  m := 1
  T1 := T147_56
  T2 := Q2.T147_56_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_56_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨56, by decide⟩
  m := 1
  T1 := T147_56
  T2 := Q2.T147_56_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 0, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_56_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨56, by decide⟩
  m := 1
  T1 := T147_56
  T2 := Q2.T147_56_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 0, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_56_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨56, by decide⟩
  m := 1
  T1 := T147_56
  T2 := Q2.T147_56_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 0, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_56_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨56, by decide⟩
  m := 1
  T1 := T147_56
  T2 := Q2.T147_56_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 0, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_57_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨57, by decide⟩
  m := 1
  T1 := T147_57
  T2 := Q2.T147_57_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_57_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨57, by decide⟩
  m := 1
  T1 := T147_57
  T2 := Q2.T147_57_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 0, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
