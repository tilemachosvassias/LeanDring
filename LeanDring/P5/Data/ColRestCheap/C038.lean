/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C028

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 37: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_119_53_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T119_53
  T2 := Q2.T119_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_53_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T119_53
  T2 := Q2.T119_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_53_5 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T119_53
  T2 := Q2.T119_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_53_10 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T119_53
  T2 := Q2.T119_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_53_15 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T119_53
  T2 := Q2.T119_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_53_20 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T119_53
  T2 := Q2.T119_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_70_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T119_70
  T2 := Q2.T119_70_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_70_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T119_70
  T2 := Q2.T119_70_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 1, 0, 3], [0, 1, 0, 4], [0, 1, 0, 0], [0, 1, 0, 1], [0, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_70_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T119_70
  T2 := Q2.T119_70_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 2, 0, 1], [0, 2, 0, 3], [0, 2, 0, 0], [0, 2, 0, 2], [0, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_70_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T119_70
  T2 := Q2.T119_70_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 3, 0, 4], [0, 3, 0, 2], [0, 3, 0, 0], [0, 3, 0, 3], [0, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_70_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨70, by decide⟩
  m := 5
  T1 := T119_70
  T2 := Q2.T119_70_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 4, 0, 2], [0, 4, 0, 1], [0, 4, 0, 0], [0, 4, 0, 4], [0, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_71_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T119_71
  T2 := Q2.T119_71_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_71_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T119_71
  T2 := Q2.T119_71_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 1, 4, 3], [0, 1, 4, 4], [0, 1, 4, 0], [0, 1, 4, 1], [0, 1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_71_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T119_71
  T2 := Q2.T119_71_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 2, 3, 1], [0, 2, 3, 3], [0, 2, 3, 0], [0, 2, 3, 2], [0, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_71_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T119_71
  T2 := Q2.T119_71_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 3, 2, 4], [0, 3, 2, 2], [0, 3, 2, 0], [0, 3, 2, 3], [0, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_71_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T119_71
  T2 := Q2.T119_71_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 4, 1, 2], [0, 4, 1, 1], [0, 4, 1, 0], [0, 4, 1, 4], [0, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_72_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨72, by decide⟩
  m := 5
  T1 := T119_72
  T2 := Q2.T119_72_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_72_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨72, by decide⟩
  m := 5
  T1 := T119_72
  T2 := Q2.T119_72_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 1, 3, 3], [0, 1, 3, 4], [0, 1, 3, 0], [0, 1, 3, 1], [0, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_72_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨72, by decide⟩
  m := 5
  T1 := T119_72
  T2 := Q2.T119_72_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 2, 1, 1], [0, 2, 1, 3], [0, 2, 1, 0], [0, 2, 1, 2], [0, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_72_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨72, by decide⟩
  m := 5
  T1 := T119_72
  T2 := Q2.T119_72_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 3, 4, 4], [0, 3, 4, 2], [0, 3, 4, 0], [0, 3, 4, 3], [0, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_72_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨72, by decide⟩
  m := 5
  T1 := T119_72
  T2 := Q2.T119_72_2
  h1 := (0,0,4,2,0)
  h2 := (0,0,4,2,0)
  D := [[0, 4, 2, 2], [0, 4, 2, 1], [0, 4, 2, 0], [0, 4, 2, 4], [0, 4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_5 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 2, 0], [0, 1, 2, 1], [0, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_6 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (0,0,1,2,1)
  h2 := (0,0,1,2,1)
  D := [[0, 1, 2, 4], [0, 1, 2, 0], [0, 1, 2, 1], [0, 1, 2, 2], [0, 1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_7 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (0,0,1,2,2)
  h2 := (0,0,1,2,2)
  D := [[0, 1, 2, 0], [0, 1, 2, 1], [0, 1, 2, 2], [0, 1, 2, 3], [0, 1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_8 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (0,0,1,2,3)
  h2 := (0,0,1,2,3)
  D := [[0, 1, 2, 1], [0, 1, 2, 2], [0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_9 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (0,0,1,2,4)
  h2 := (0,0,1,2,4)
  D := [[0, 1, 2, 2], [0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 2, 0], [0, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_10 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 2, 4, 1], [0, 2, 4, 3], [0, 2, 4, 0], [0, 2, 4, 2], [0, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_11 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (0,0,2,4,1)
  h2 := (0,0,2,4,1)
  D := [[0, 2, 4, 2], [0, 2, 4, 4], [0, 2, 4, 1], [0, 2, 4, 3], [0, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_12 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (0,0,2,4,2)
  h2 := (0,0,2,4,2)
  D := [[0, 2, 4, 3], [0, 2, 4, 0], [0, 2, 4, 2], [0, 2, 4, 4], [0, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_13 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (0,0,2,4,3)
  h2 := (0,0,2,4,3)
  D := [[0, 2, 4, 4], [0, 2, 4, 1], [0, 2, 4, 3], [0, 2, 4, 0], [0, 2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_14 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (0,0,2,4,4)
  h2 := (0,0,2,4,4)
  D := [[0, 2, 4, 0], [0, 2, 4, 2], [0, 2, 4, 4], [0, 2, 4, 1], [0, 2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_15 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 3, 1, 4], [0, 3, 1, 2], [0, 3, 1, 0], [0, 3, 1, 3], [0, 3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_16 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (0,0,3,1,1)
  h2 := (0,0,3,1,1)
  D := [[0, 3, 1, 0], [0, 3, 1, 3], [0, 3, 1, 1], [0, 3, 1, 4], [0, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_17 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (0,0,3,1,2)
  h2 := (0,0,3,1,2)
  D := [[0, 3, 1, 1], [0, 3, 1, 4], [0, 3, 1, 2], [0, 3, 1, 0], [0, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_18 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (0,0,3,1,3)
  h2 := (0,0,3,1,3)
  D := [[0, 3, 1, 2], [0, 3, 1, 0], [0, 3, 1, 3], [0, 3, 1, 1], [0, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_19 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (0,0,3,1,4)
  h2 := (0,0,3,1,4)
  D := [[0, 3, 1, 3], [0, 3, 1, 1], [0, 3, 1, 4], [0, 3, 1, 2], [0, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_20 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 4, 3, 2], [0, 4, 3, 1], [0, 4, 3, 0], [0, 4, 3, 4], [0, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_21 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (0,0,4,3,1)
  h2 := (0,0,4,3,1)
  D := [[0, 4, 3, 3], [0, 4, 3, 2], [0, 4, 3, 1], [0, 4, 3, 0], [0, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_22 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (0,0,4,3,2)
  h2 := (0,0,4,3,2)
  D := [[0, 4, 3, 4], [0, 4, 3, 3], [0, 4, 3, 2], [0, 4, 3, 1], [0, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_23 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (0,0,4,3,3)
  h2 := (0,0,4,3,3)
  D := [[0, 4, 3, 0], [0, 4, 3, 4], [0, 4, 3, 3], [0, 4, 3, 2], [0, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_24 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (0,0,4,3,4)
  h2 := (0,0,4,3,4)
  D := [[0, 4, 3, 1], [0, 4, 3, 0], [0, 4, 3, 4], [0, 4, 3, 3], [0, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_25 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (1,3,0,0,0)
  h2 := (1,3,0,0,0)
  D := [[1, 0, 1, 2], [1, 0, 0, 3], [1, 0, 4, 4], [1, 0, 3, 0], [1, 0, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_30 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (1,3,1,2,0)
  h2 := (1,3,1,2,0)
  D := [[1, 1, 3, 0], [1, 1, 2, 2], [1, 1, 1, 4], [1, 1, 0, 1], [1, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_35 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (1,3,2,4,0)
  h2 := (1,3,2,4,0)
  D := [[1, 2, 0, 3], [1, 2, 4, 1], [1, 2, 3, 4], [1, 2, 2, 2], [1, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_40 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (1,3,3,1,0)
  h2 := (1,3,3,1,0)
  D := [[1, 3, 2, 1], [1, 3, 1, 0], [1, 3, 0, 4], [1, 3, 4, 3], [1, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_45 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (1,3,4,3,0)
  h2 := (1,3,4,3,0)
  D := [[1, 4, 4, 4], [1, 4, 3, 4], [1, 4, 2, 4], [1, 4, 1, 4], [1, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_50 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (2,1,0,3,1)
  h2 := (2,1,0,3,2)
  D := [[2, 0, 2, 3], [2, 0, 0, 1], [2, 0, 3, 4], [2, 0, 1, 2], [2, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_55 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (2,1,1,0,1)
  h2 := (2,1,1,0,2)
  D := [[2, 1, 4, 1], [2, 1, 2, 0], [2, 1, 0, 4], [2, 1, 3, 3], [2, 1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_60 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (2,1,2,2,1)
  h2 := (2,1,2,2,2)
  D := [[2, 2, 1, 4], [2, 2, 4, 4], [2, 2, 2, 4], [2, 2, 0, 4], [2, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_65 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (2,1,3,4,1)
  h2 := (2,1,3,4,2)
  D := [[2, 3, 3, 2], [2, 3, 1, 3], [2, 3, 4, 4], [2, 3, 2, 0], [2, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_70 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (2,1,4,1,1)
  h2 := (2,1,4,1,2)
  D := [[2, 4, 0, 0], [2, 4, 3, 2], [2, 4, 1, 4], [2, 4, 4, 1], [2, 4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_75 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (3,4,0,4,4)
  h2 := (3,4,0,4,0)
  D := [[3, 0, 3, 3], [3, 0, 0, 4], [3, 0, 2, 0], [3, 0, 4, 1], [3, 0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_80 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (3,4,1,1,4)
  h2 := (3,4,1,1,0)
  D := [[3, 1, 0, 1], [3, 1, 2, 3], [3, 1, 4, 0], [3, 1, 1, 2], [3, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_85 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (3,4,2,3,4)
  h2 := (3,4,2,3,0)
  D := [[3, 2, 2, 4], [3, 2, 4, 2], [3, 2, 1, 0], [3, 2, 3, 3], [3, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_73_90 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T119_73
  T2 := Q2.T119_73_2
  h1 := (3,4,3,0,4)
  h2 := (3,4,3,0,0)
  D := [[3, 3, 4, 2], [3, 3, 1, 1], [3, 3, 3, 0], [3, 3, 0, 4], [3, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
