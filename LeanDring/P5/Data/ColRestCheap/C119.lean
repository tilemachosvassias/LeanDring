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
rest tier, chunk 118: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_147_72_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨72, by decide⟩
  m := 1
  T1 := T147_72
  T2 := Q2.T147_72_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 0, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_72_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨72, by decide⟩
  m := 1
  T1 := T147_72
  T2 := Q2.T147_72_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 0, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_72_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨72, by decide⟩
  m := 1
  T1 := T147_72
  T2 := Q2.T147_72_2
  h1 := (0,0,4,2,0)
  h2 := (0,0,4,2,0)
  D := [[0, 0, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 0, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (0,0,1,2,1)
  h2 := (0,0,1,2,1)
  D := [[0, 0, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (0,0,1,2,2)
  h2 := (0,0,1,2,2)
  D := [[0, 0, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (0,0,1,2,3)
  h2 := (0,0,1,2,3)
  D := [[0, 0, 1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (0,0,1,2,4)
  h2 := (0,0,1,2,4)
  D := [[0, 0, 1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 0, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_11 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (0,0,2,4,1)
  h2 := (0,0,2,4,1)
  D := [[0, 0, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_12 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (0,0,2,4,2)
  h2 := (0,0,2,4,2)
  D := [[0, 0, 2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_13 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (0,0,2,4,3)
  h2 := (0,0,2,4,3)
  D := [[0, 0, 2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_14 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (0,0,2,4,4)
  h2 := (0,0,2,4,4)
  D := [[0, 0, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 0, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_16 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (0,0,3,1,1)
  h2 := (0,0,3,1,1)
  D := [[0, 0, 3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_17 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (0,0,3,1,2)
  h2 := (0,0,3,1,2)
  D := [[0, 0, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_18 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (0,0,3,1,3)
  h2 := (0,0,3,1,3)
  D := [[0, 0, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_19 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (0,0,3,1,4)
  h2 := (0,0,3,1,4)
  D := [[0, 0, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 0, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_21 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (0,0,4,3,1)
  h2 := (0,0,4,3,1)
  D := [[0, 0, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_22 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (0,0,4,3,2)
  h2 := (0,0,4,3,2)
  D := [[0, 0, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (0,0,4,3,3)
  h2 := (0,0,4,3,3)
  D := [[0, 0, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (0,0,4,3,4)
  h2 := (0,0,4,3,4)
  D := [[0, 0, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_25 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (1,3,0,0,0)
  h2 := (1,3,0,0,0)
  D := [[1, 3, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_30 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (1,3,1,2,0)
  h2 := (1,3,1,2,0)
  D := [[1, 3, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_35 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (1,3,2,4,0)
  h2 := (1,3,2,4,0)
  D := [[1, 3, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_40 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (1,3,3,1,0)
  h2 := (1,3,3,1,0)
  D := [[1, 3, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_73_45 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (1,3,4,3,0)
  h2 := (1,3,4,3,0)
  D := [[1, 3, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_74_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨74, by decide⟩
  m := 1
  T1 := T147_74
  T2 := Q2.T147_74_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_74_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨74, by decide⟩
  m := 1
  T1 := T147_74
  T2 := Q2.T147_74_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 0, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_74_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨74, by decide⟩
  m := 1
  T1 := T147_74
  T2 := Q2.T147_74_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 0, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_74_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨74, by decide⟩
  m := 1
  T1 := T147_74
  T2 := Q2.T147_74_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 0, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_74_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨74, by decide⟩
  m := 1
  T1 := T147_74
  T2 := Q2.T147_74_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 0, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_74_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨74, by decide⟩
  m := 1
  T1 := T147_74
  T2 := Q2.T147_74_2
  h1 := (1,3,0,0,0)
  h2 := (1,3,0,0,0)
  D := [[1, 3, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_74_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨74, by decide⟩
  m := 1
  T1 := T147_74
  T2 := Q2.T147_74_2
  h1 := (1,3,1,1,0)
  h2 := (1,3,1,1,0)
  D := [[1, 3, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_74_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨74, by decide⟩
  m := 1
  T1 := T147_74
  T2 := Q2.T147_74_2
  h1 := (1,3,2,2,0)
  h2 := (1,3,2,2,0)
  D := [[1, 3, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_74_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨74, by decide⟩
  m := 1
  T1 := T147_74
  T2 := Q2.T147_74_2
  h1 := (1,3,3,3,0)
  h2 := (1,3,3,3,0)
  D := [[1, 3, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_74_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨74, by decide⟩
  m := 1
  T1 := T147_74
  T2 := Q2.T147_74_2
  h1 := (1,3,4,4,0)
  h2 := (1,3,4,4,0)
  D := [[1, 3, 4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_75_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨75, by decide⟩
  m := 1
  T1 := T147_75
  T2 := Q2.T147_75_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_75_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨75, by decide⟩
  m := 1
  T1 := T147_75
  T2 := Q2.T147_75_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_75_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨75, by decide⟩
  m := 1
  T1 := T147_75
  T2 := Q2.T147_75_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_75_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨75, by decide⟩
  m := 1
  T1 := T147_75
  T2 := Q2.T147_75_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_75_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨75, by decide⟩
  m := 1
  T1 := T147_75
  T2 := Q2.T147_75_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_76_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨76, by decide⟩
  m := 1
  T1 := T147_76
  T2 := Q2.T147_76_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_76_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨76, by decide⟩
  m := 1
  T1 := T147_76
  T2 := Q2.T147_76_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_76_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨76, by decide⟩
  m := 1
  T1 := T147_76
  T2 := Q2.T147_76_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_76_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨76, by decide⟩
  m := 1
  T1 := T147_76
  T2 := Q2.T147_76_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_76_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨76, by decide⟩
  m := 1
  T1 := T147_76
  T2 := Q2.T147_76_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_76_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨76, by decide⟩
  m := 1
  T1 := T147_76
  T2 := Q2.T147_76_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 0, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_76_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨76, by decide⟩
  m := 1
  T1 := T147_76
  T2 := Q2.T147_76_2
  h1 := (0,0,1,4,1)
  h2 := (0,0,1,4,1)
  D := [[0, 0, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_76_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨76, by decide⟩
  m := 1
  T1 := T147_76
  T2 := Q2.T147_76_2
  h1 := (0,0,1,4,2)
  h2 := (0,0,1,4,2)
  D := [[0, 0, 1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_76_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨76, by decide⟩
  m := 1
  T1 := T147_76
  T2 := Q2.T147_76_2
  h1 := (0,0,1,4,3)
  h2 := (0,0,1,4,3)
  D := [[0, 0, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_76_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨76, by decide⟩
  m := 1
  T1 := T147_76
  T2 := Q2.T147_76_2
  h1 := (0,0,1,4,4)
  h2 := (0,0,1,4,4)
  D := [[0, 0, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_76_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨76, by decide⟩
  m := 1
  T1 := T147_76
  T2 := Q2.T147_76_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 0, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_76_11 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨76, by decide⟩
  m := 1
  T1 := T147_76
  T2 := Q2.T147_76_2
  h1 := (0,0,2,3,1)
  h2 := (0,0,2,3,1)
  D := [[0, 0, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
