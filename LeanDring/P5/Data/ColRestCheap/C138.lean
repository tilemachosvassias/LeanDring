/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C044
import LeanDring.P5.Data.EntryK.C003
import LeanDring.P5.Data.EntryK.C004

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 137: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_147_147_73 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (2,4,3,0,0)
  h2 := (2,4,3,0,0)
  D := [[2, 4, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_74 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (2,4,4,0,0)
  h2 := (2,4,4,0,0)
  D := [[2, 4, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_75 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (3,0,0,0,0)
  h2 := (3,0,0,0,0)
  D := [[3, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_76 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (3,0,1,0,0)
  h2 := (3,0,1,0,0)
  D := [[3, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_77 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (3,0,2,0,0)
  h2 := (3,0,2,0,0)
  D := [[3, 0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_78 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (3,0,3,0,0)
  h2 := (3,0,3,0,0)
  D := [[3, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_79 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (3,0,4,0,0)
  h2 := (3,0,4,0,0)
  D := [[3, 0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_80 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (3,1,0,0,0)
  h2 := (3,1,0,0,0)
  D := [[3, 1, 0, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_81 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (3,1,1,0,0)
  h2 := (3,1,1,0,0)
  D := [[3, 1, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_82 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (3,1,2,0,0)
  h2 := (3,1,2,0,0)
  D := [[3, 1, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_83 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (3,1,3,0,0)
  h2 := (3,1,3,0,0)
  D := [[3, 1, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_84 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (3,1,4,0,0)
  h2 := (3,1,4,0,0)
  D := [[3, 1, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_85 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (3,2,0,0,0)
  h2 := (3,2,0,0,0)
  D := [[3, 2, 0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_86 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (3,2,1,0,0)
  h2 := (3,2,1,0,0)
  D := [[3, 2, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_87 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (3,2,2,0,0)
  h2 := (3,2,2,0,0)
  D := [[3, 2, 2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_88 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (3,2,3,0,0)
  h2 := (3,2,3,0,0)
  D := [[3, 2, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_89 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (3,2,4,0,0)
  h2 := (3,2,4,0,0)
  D := [[3, 2, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_90 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (3,3,0,0,0)
  h2 := (3,3,0,0,0)
  D := [[3, 3, 0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_91 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (3,3,1,0,0)
  h2 := (3,3,1,0,0)
  D := [[3, 3, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_92 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (3,3,2,0,0)
  h2 := (3,3,2,0,0)
  D := [[3, 3, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_93 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (3,3,3,0,0)
  h2 := (3,3,3,0,0)
  D := [[3, 3, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_94 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (3,3,4,0,0)
  h2 := (3,3,4,0,0)
  D := [[3, 3, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_95 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (3,4,0,0,0)
  h2 := (3,4,0,0,0)
  D := [[3, 4, 0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_96 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (3,4,1,0,0)
  h2 := (3,4,1,0,0)
  D := [[3, 4, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_97 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (3,4,2,0,0)
  h2 := (3,4,2,0,0)
  D := [[3, 4, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_98 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (3,4,3,0,0)
  h2 := (3,4,3,0,0)
  D := [[3, 4, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_99 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (3,4,4,0,0)
  h2 := (3,4,4,0,0)
  D := [[3, 4, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_100 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (4,0,0,0,0)
  h2 := (4,0,0,0,0)
  D := [[4, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_101 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (4,0,1,0,0)
  h2 := (4,0,1,0,0)
  D := [[4, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_102 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (4,0,2,0,0)
  h2 := (4,0,2,0,0)
  D := [[4, 0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_103 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (4,0,3,0,0)
  h2 := (4,0,3,0,0)
  D := [[4, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_104 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (4,0,4,0,0)
  h2 := (4,0,4,0,0)
  D := [[4, 0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_105 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (4,1,0,0,0)
  h2 := (4,1,0,0,0)
  D := [[4, 1, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_106 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (4,1,1,0,0)
  h2 := (4,1,1,0,0)
  D := [[4, 1, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_107 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (4,1,2,0,0)
  h2 := (4,1,2,0,0)
  D := [[4, 1, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_108 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (4,1,3,0,0)
  h2 := (4,1,3,0,0)
  D := [[4, 1, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_109 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (4,1,4,0,0)
  h2 := (4,1,4,0,0)
  D := [[4, 1, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_110 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (4,2,0,0,0)
  h2 := (4,2,0,0,0)
  D := [[4, 2, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_111 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (4,2,1,0,0)
  h2 := (4,2,1,0,0)
  D := [[4, 2, 1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_112 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (4,2,2,0,0)
  h2 := (4,2,2,0,0)
  D := [[4, 2, 2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_113 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (4,2,3,0,0)
  h2 := (4,2,3,0,0)
  D := [[4, 2, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_114 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (4,2,4,0,0)
  h2 := (4,2,4,0,0)
  D := [[4, 2, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_115 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (4,3,0,0,0)
  h2 := (4,3,0,0,0)
  D := [[4, 3, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_116 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (4,3,1,0,0)
  h2 := (4,3,1,0,0)
  D := [[4, 3, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_117 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (4,3,2,0,0)
  h2 := (4,3,2,0,0)
  D := [[4, 3, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_118 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (4,3,3,0,0)
  h2 := (4,3,3,0,0)
  D := [[4, 3, 3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_119 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (4,3,4,0,0)
  h2 := (4,3,4,0,0)
  D := [[4, 3, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_120 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (4,4,0,0,0)
  h2 := (4,4,0,0,0)
  D := [[4, 4, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_121 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (4,4,1,0,0)
  h2 := (4,4,1,0,0)
  D := [[4, 4, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_122 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (4,4,2,0,0)
  h2 := (4,4,2,0,0)
  D := [[4, 4, 2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_123 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (4,4,3,0,0)
  h2 := (4,4,3,0,0)
  D := [[4, 4, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_124 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (4,4,4,0,0)
  h2 := (4,4,4,0,0)
  D := [[4, 4, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_2_2_0 : ColCert where
  rK := ⟨2, by decide⟩
  rH := ⟨2, by decide⟩
  m := 25
  T1 := T2_2
  T2 := Q2.T2_2_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]]
  bind1 := by decide
  bind2 := by decide

def colCert_2_2_1 : ColCert where
  rK := ⟨2, by decide⟩
  rH := ⟨2, by decide⟩
  m := 25
  T1 := T2_2
  T2 := Q2.T2_2_2
  h1 := (1,0,4,1,0)
  h2 := (1,0,4,1,0)
  D := [[1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1]]
  bind1 := by decide
  bind2 := by decide

def colCert_2_2_2 : ColCert where
  rK := ⟨2, by decide⟩
  rH := ⟨2, by decide⟩
  m := 25
  T1 := T2_2
  T2 := Q2.T2_2_2
  h1 := (2,0,3,2,1)
  h2 := (2,0,3,2,1)
  D := [[2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2]]
  bind1 := by decide
  bind2 := by decide

def colCert_2_2_3 : ColCert where
  rK := ⟨2, by decide⟩
  rH := ⟨2, by decide⟩
  m := 25
  T1 := T2_2
  T2 := Q2.T2_2_2
  h1 := (3,0,2,3,3)
  h2 := (3,0,2,3,3)
  D := [[3], [3], [3], [3], [3], [3], [3], [3], [3], [3], [3], [3], [3], [3], [3], [3], [3], [3], [3], [3], [3], [3], [3], [3], [3]]
  bind1 := by decide
  bind2 := by decide

def colCert_2_2_4 : ColCert where
  rK := ⟨2, by decide⟩
  rH := ⟨2, by decide⟩
  m := 25
  T1 := T2_2
  T2 := Q2.T2_2_2
  h1 := (4,0,1,4,1)
  h2 := (4,0,1,4,1)
  D := [[4], [4], [4], [4], [4], [4], [4], [4], [4], [4], [4], [4], [4], [4], [4], [4], [4], [4], [4], [4], [4], [4], [4], [4], [4]]
  bind1 := by decide
  bind2 := by decide

def colCert_3_3_0 : ColCert where
  rK := ⟨3, by decide⟩
  rH := ⟨3, by decide⟩
  m := 25
  T1 := T3_3
  T2 := Q2.T3_3_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]]
  bind1 := by decide
  bind2 := by decide

def colCert_3_3_1 : ColCert where
  rK := ⟨3, by decide⟩
  rH := ⟨3, by decide⟩
  m := 25
  T1 := T3_3
  T2 := Q2.T3_3_2
  h1 := (1,0,2,3,1)
  h2 := (1,0,2,3,1)
  D := [[1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1], [1]]
  bind1 := by decide
  bind2 := by decide

def colCert_3_3_2 : ColCert where
  rK := ⟨3, by decide⟩
  rH := ⟨3, by decide⟩
  m := 25
  T1 := T3_3
  T2 := Q2.T3_3_2
  h1 := (2,0,4,1,0)
  h2 := (2,0,4,1,0)
  D := [[2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2], [2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
