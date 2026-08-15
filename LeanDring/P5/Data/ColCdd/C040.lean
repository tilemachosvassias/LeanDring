/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C017
import LeanDring.P5.Data.EntryK.C018

/-!
# Species-table cell data, stage 2 — column-data-divergent columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
cdd tier, chunk 39: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_74_36_15 : ColCertDiv where
  rK := ⟨74, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T74_36
  T2 := Q2.T74_36_2
  h1 := (3,4,3,4,1)
  h2 := (3,4,3,4,0)
  D1 := [[3, 3, 0], [3, 3, 2], [3, 3, 4], [3, 3, 1], [3, 3, 3]]
  D2 := [[3, 3, 3], [3, 3, 0], [3, 3, 2], [3, 3, 4], [3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_74_36_20 : ColCertDiv where
  rK := ⟨74, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T74_36
  T2 := Q2.T74_36_2
  h1 := (4,2,4,3,1)
  h2 := (4,2,4,3,2)
  D1 := [[4, 4, 2], [4, 4, 3], [4, 4, 4], [4, 4, 0], [4, 4, 1]]
  D2 := [[4, 4, 1], [4, 4, 2], [4, 4, 3], [4, 4, 4], [4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_74_41_5 : ColCertDiv where
  rK := ⟨74, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T74_41
  T2 := Q2.T74_41_2
  h1 := (1,3,4,0,0)
  h2 := (1,3,4,0,1)
  D1 := [[1, 4, 4], [1, 4, 3], [1, 4, 2], [1, 4, 1], [1, 4, 0]]
  D2 := [[1, 4, 0], [1, 4, 4], [1, 4, 3], [1, 4, 2], [1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_74_41_10 : ColCertDiv where
  rK := ⟨74, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T74_41
  T2 := Q2.T74_41_2
  h1 := (2,1,3,3,3)
  h2 := (2,1,3,3,1)
  D1 := [[2, 3, 2], [2, 3, 0], [2, 3, 3], [2, 3, 1], [2, 3, 4]]
  D2 := [[2, 3, 4], [2, 3, 2], [2, 3, 0], [2, 3, 3], [2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_74_41_15 : ColCertDiv where
  rK := ⟨74, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T74_41
  T2 := Q2.T74_41_2
  h1 := (3,4,2,4,0)
  h2 := (3,4,2,4,4)
  D1 := [[3, 2, 4], [3, 2, 1], [3, 2, 3], [3, 2, 0], [3, 2, 2]]
  D2 := [[3, 2, 2], [3, 2, 4], [3, 2, 1], [3, 2, 3], [3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_74_41_20 : ColCertDiv where
  rK := ⟨74, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T74_41
  T2 := Q2.T74_41_2
  h1 := (4,2,1,3,1)
  h2 := (4,2,1,3,2)
  D1 := [[4, 1, 0], [4, 1, 1], [4, 1, 2], [4, 1, 3], [4, 1, 4]]
  D2 := [[4, 1, 4], [4, 1, 0], [4, 1, 1], [4, 1, 2], [4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_74_46_5 : ColCertDiv where
  rK := ⟨74, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T74_46
  T2 := Q2.T74_46_2
  h1 := (1,3,3,0,2)
  h2 := (1,3,3,0,3)
  D1 := [[1, 3, 1], [1, 3, 0], [1, 3, 4], [1, 3, 3], [1, 3, 2]]
  D2 := [[1, 3, 2], [1, 3, 1], [1, 3, 0], [1, 3, 4], [1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_74_46_10 : ColCertDiv where
  rK := ⟨74, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T74_46
  T2 := Q2.T74_46_2
  h1 := (2,1,1,3,4)
  h2 := (2,1,1,3,2)
  D1 := [[2, 1, 0], [2, 1, 3], [2, 1, 1], [2, 1, 4], [2, 1, 2]]
  D2 := [[2, 1, 2], [2, 1, 0], [2, 1, 3], [2, 1, 1], [2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_74_46_15 : ColCertDiv where
  rK := ⟨74, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T74_46
  T2 := Q2.T74_46_2
  h1 := (3,4,4,4,2)
  h2 := (3,4,4,4,1)
  D1 := [[3, 4, 2], [3, 4, 4], [3, 4, 1], [3, 4, 3], [3, 4, 0]]
  D2 := [[3, 4, 0], [3, 4, 2], [3, 4, 4], [3, 4, 1], [3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_74_46_20 : ColCertDiv where
  rK := ⟨74, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T74_46
  T2 := Q2.T74_46_2
  h1 := (4,2,2,3,1)
  h2 := (4,2,2,3,2)
  D1 := [[4, 2, 2], [4, 2, 3], [4, 2, 4], [4, 2, 0], [4, 2, 1]]
  D2 := [[4, 2, 1], [4, 2, 2], [4, 2, 3], [4, 2, 4], [4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_74_51_5 : ColCertDiv where
  rK := ⟨74, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T74_51
  T2 := Q2.T74_51_2
  h1 := (1,3,0,0,3)
  h2 := (1,3,0,0,4)
  D1 := [[1, 0, 0], [1, 0, 4], [1, 0, 3], [1, 0, 2], [1, 0, 1]]
  D2 := [[1, 0, 1], [1, 0, 0], [1, 0, 4], [1, 0, 3], [1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_74_51_10 : ColCertDiv where
  rK := ⟨74, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T74_51
  T2 := Q2.T74_51_2
  h1 := (2,1,0,3,2)
  h2 := (2,1,0,3,0)
  D1 := [[2, 0, 0], [2, 0, 3], [2, 0, 1], [2, 0, 4], [2, 0, 2]]
  D2 := [[2, 0, 2], [2, 0, 0], [2, 0, 3], [2, 0, 1], [2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_74_51_15 : ColCertDiv where
  rK := ⟨74, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T74_51
  T2 := Q2.T74_51_2
  h1 := (3,4,0,4,3)
  h2 := (3,4,0,4,2)
  D1 := [[3, 0, 0], [3, 0, 2], [3, 0, 4], [3, 0, 1], [3, 0, 3]]
  D2 := [[3, 0, 3], [3, 0, 0], [3, 0, 2], [3, 0, 4], [3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_74_51_20 : ColCertDiv where
  rK := ⟨74, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T74_51
  T2 := Q2.T74_51_2
  h1 := (4,2,0,3,1)
  h2 := (4,2,0,3,2)
  D1 := [[4, 0, 0], [4, 0, 1], [4, 0, 2], [4, 0, 3], [4, 0, 4]]
  D2 := [[4, 0, 4], [4, 0, 0], [4, 0, 1], [4, 0, 2], [4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_77_32_5 : ColCertDiv where
  rK := ⟨77, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T77_32
  T2 := Q2.T77_32_2
  h1 := (1,1,4,4,0)
  h2 := (1,1,4,4,3)
  D1 := [[1, 4, 0], [1, 4, 4], [1, 4, 3], [1, 4, 2], [1, 4, 1]]
  D2 := [[1, 4, 2], [1, 4, 1], [1, 4, 0], [1, 4, 4], [1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_77_32_10 : ColCertDiv where
  rK := ⟨77, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T77_32
  T2 := Q2.T77_32_2
  h1 := (2,2,3,4,3)
  h2 := (2,2,3,4,4)
  D1 := [[2, 3, 4], [2, 3, 2], [2, 3, 0], [2, 3, 3], [2, 3, 1]]
  D2 := [[2, 3, 3], [2, 3, 1], [2, 3, 4], [2, 3, 2], [2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_77_32_15 : ColCertDiv where
  rK := ⟨77, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T77_32
  T2 := Q2.T77_32_2
  h1 := (3,3,2,0,0)
  h2 := (3,3,2,0,4)
  D1 := [[3, 2, 2], [3, 2, 4], [3, 2, 1], [3, 2, 3], [3, 2, 0]]
  D2 := [[3, 2, 3], [3, 2, 0], [3, 2, 2], [3, 2, 4], [3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_77_32_20 : ColCertDiv where
  rK := ⟨77, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T77_32
  T2 := Q2.T77_32_2
  h1 := (4,4,1,2,2)
  h2 := (4,4,1,2,4)
  D1 := [[4, 1, 4], [4, 1, 0], [4, 1, 1], [4, 1, 2], [4, 1, 3]]
  D2 := [[4, 1, 2], [4, 1, 3], [4, 1, 4], [4, 1, 0], [4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_77_37_5 : ColCertDiv where
  rK := ⟨77, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T77_37
  T2 := Q2.T77_37_2
  h1 := (1,1,2,4,3)
  h2 := (1,1,2,4,1)
  D1 := [[1, 2, 1], [1, 2, 0], [1, 2, 4], [1, 2, 3], [1, 2, 2]]
  D2 := [[1, 2, 3], [1, 2, 2], [1, 2, 1], [1, 2, 0], [1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_77_37_10 : ColCertDiv where
  rK := ⟨77, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T77_37
  T2 := Q2.T77_37_2
  h1 := (2,2,4,4,2)
  h2 := (2,2,4,4,3)
  D1 := [[2, 4, 4], [2, 4, 2], [2, 4, 0], [2, 4, 3], [2, 4, 1]]
  D2 := [[2, 4, 3], [2, 4, 1], [2, 4, 4], [2, 4, 2], [2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_77_37_15 : ColCertDiv where
  rK := ⟨77, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T77_37
  T2 := Q2.T77_37_2
  h1 := (3,3,1,0,3)
  h2 := (3,3,1,0,2)
  D1 := [[3, 1, 4], [3, 1, 1], [3, 1, 3], [3, 1, 0], [3, 1, 2]]
  D2 := [[3, 1, 0], [3, 1, 2], [3, 1, 4], [3, 1, 1], [3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_77_37_20 : ColCertDiv where
  rK := ⟨77, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T77_37
  T2 := Q2.T77_37_2
  h1 := (4,4,3,2,2)
  h2 := (4,4,3,2,4)
  D1 := [[4, 3, 1], [4, 3, 2], [4, 3, 3], [4, 3, 4], [4, 3, 0]]
  D2 := [[4, 3, 4], [4, 3, 0], [4, 3, 1], [4, 3, 2], [4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_77_42_5 : ColCertDiv where
  rK := ⟨77, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T77_42
  T2 := Q2.T77_42_2
  h1 := (1,1,3,4,4)
  h2 := (1,1,3,4,2)
  D1 := [[1, 3, 1], [1, 3, 0], [1, 3, 4], [1, 3, 3], [1, 3, 2]]
  D2 := [[1, 3, 3], [1, 3, 2], [1, 3, 1], [1, 3, 0], [1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_77_42_10 : ColCertDiv where
  rK := ⟨77, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T77_42
  T2 := Q2.T77_42_2
  h1 := (2,2,1,4,0)
  h2 := (2,2,1,4,1)
  D1 := [[2, 1, 0], [2, 1, 3], [2, 1, 1], [2, 1, 4], [2, 1, 2]]
  D2 := [[2, 1, 4], [2, 1, 2], [2, 1, 0], [2, 1, 3], [2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_77_42_15 : ColCertDiv where
  rK := ⟨77, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T77_42
  T2 := Q2.T77_42_2
  h1 := (3,3,4,0,4)
  h2 := (3,3,4,0,3)
  D1 := [[3, 4, 2], [3, 4, 4], [3, 4, 1], [3, 4, 3], [3, 4, 0]]
  D2 := [[3, 4, 3], [3, 4, 0], [3, 4, 2], [3, 4, 4], [3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_77_42_20 : ColCertDiv where
  rK := ⟨77, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T77_42
  T2 := Q2.T77_42_2
  h1 := (4,4,2,2,2)
  h2 := (4,4,2,2,4)
  D1 := [[4, 2, 2], [4, 2, 3], [4, 2, 4], [4, 2, 0], [4, 2, 1]]
  D2 := [[4, 2, 0], [4, 2, 1], [4, 2, 2], [4, 2, 3], [4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_77_47_5 : ColCertDiv where
  rK := ⟨77, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T77_47
  T2 := Q2.T77_47_2
  h1 := (1,1,1,4,2)
  h2 := (1,1,1,4,0)
  D1 := [[1, 1, 0], [1, 1, 4], [1, 1, 3], [1, 1, 2], [1, 1, 1]]
  D2 := [[1, 1, 2], [1, 1, 1], [1, 1, 0], [1, 1, 4], [1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_77_47_10 : ColCertDiv where
  rK := ⟨77, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T77_47
  T2 := Q2.T77_47_2
  h1 := (2,2,2,4,4)
  h2 := (2,2,2,4,0)
  D1 := [[2, 2, 1], [2, 2, 4], [2, 2, 2], [2, 2, 0], [2, 2, 3]]
  D2 := [[2, 2, 0], [2, 2, 3], [2, 2, 1], [2, 2, 4], [2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_77_47_15 : ColCertDiv where
  rK := ⟨77, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T77_47
  T2 := Q2.T77_47_2
  h1 := (3,3,3,0,2)
  h2 := (3,3,3,0,1)
  D1 := [[3, 3, 3], [3, 3, 0], [3, 3, 2], [3, 3, 4], [3, 3, 1]]
  D2 := [[3, 3, 4], [3, 3, 1], [3, 3, 3], [3, 3, 0], [3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_77_47_20 : ColCertDiv where
  rK := ⟨77, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T77_47
  T2 := Q2.T77_47_2
  h1 := (4,4,4,2,2)
  h2 := (4,4,4,2,4)
  D1 := [[4, 4, 1], [4, 4, 2], [4, 4, 3], [4, 4, 4], [4, 4, 0]]
  D2 := [[4, 4, 4], [4, 4, 0], [4, 4, 1], [4, 4, 2], [4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_77_52_5 : ColCertDiv where
  rK := ⟨77, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T77_52
  T2 := Q2.T77_52_2
  h1 := (1,1,0,4,1)
  h2 := (1,1,0,4,4)
  D1 := [[1, 0, 3], [1, 0, 2], [1, 0, 1], [1, 0, 0], [1, 0, 4]]
  D2 := [[1, 0, 0], [1, 0, 4], [1, 0, 3], [1, 0, 2], [1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_77_52_10 : ColCertDiv where
  rK := ⟨77, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T77_52
  T2 := Q2.T77_52_2
  h1 := (2,2,0,4,1)
  h2 := (2,2,0,4,2)
  D1 := [[2, 0, 1], [2, 0, 4], [2, 0, 2], [2, 0, 0], [2, 0, 3]]
  D2 := [[2, 0, 0], [2, 0, 3], [2, 0, 1], [2, 0, 4], [2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_77_52_15 : ColCertDiv where
  rK := ⟨77, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T77_52
  T2 := Q2.T77_52_2
  h1 := (3,3,0,0,1)
  h2 := (3,3,0,0,0)
  D1 := [[3, 0, 4], [3, 0, 1], [3, 0, 3], [3, 0, 0], [3, 0, 2]]
  D2 := [[3, 0, 0], [3, 0, 2], [3, 0, 4], [3, 0, 1], [3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_77_52_20 : ColCertDiv where
  rK := ⟨77, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T77_52
  T2 := Q2.T77_52_2
  h1 := (4,4,0,2,2)
  h2 := (4,4,0,2,4)
  D1 := [[4, 0, 2], [4, 0, 3], [4, 0, 4], [4, 0, 0], [4, 0, 1]]
  D2 := [[4, 0, 0], [4, 0, 1], [4, 0, 2], [4, 0, 3], [4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_78_32_5 : ColCertDiv where
  rK := ⟨78, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T78_32
  T2 := Q2.T78_32_2
  h1 := (1,1,4,4,0)
  h2 := (1,1,4,4,3)
  D1 := [[1, 4, 2], [1, 4, 1], [1, 4, 0], [1, 4, 4], [1, 4, 3]]
  D2 := [[1, 4, 4], [1, 4, 3], [1, 4, 2], [1, 4, 1], [1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_78_32_10 : ColCertDiv where
  rK := ⟨78, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T78_32
  T2 := Q2.T78_32_2
  h1 := (2,2,3,4,3)
  h2 := (2,2,3,4,4)
  D1 := [[2, 3, 2], [2, 3, 0], [2, 3, 3], [2, 3, 1], [2, 3, 4]]
  D2 := [[2, 3, 1], [2, 3, 4], [2, 3, 2], [2, 3, 0], [2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_78_32_15 : ColCertDiv where
  rK := ⟨78, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T78_32
  T2 := Q2.T78_32_2
  h1 := (3,3,2,0,0)
  h2 := (3,3,2,0,4)
  D1 := [[3, 2, 0], [3, 2, 2], [3, 2, 4], [3, 2, 1], [3, 2, 3]]
  D2 := [[3, 2, 1], [3, 2, 3], [3, 2, 0], [3, 2, 2], [3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_78_32_20 : ColCertDiv where
  rK := ⟨78, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T78_32
  T2 := Q2.T78_32_2
  h1 := (4,4,1,2,2)
  h2 := (4,4,1,2,4)
  D1 := [[4, 1, 1], [4, 1, 2], [4, 1, 3], [4, 1, 4], [4, 1, 0]]
  D2 := [[4, 1, 4], [4, 1, 0], [4, 1, 1], [4, 1, 2], [4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_78_37_5 : ColCertDiv where
  rK := ⟨78, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T78_37
  T2 := Q2.T78_37_2
  h1 := (1,1,2,4,3)
  h2 := (1,1,2,4,1)
  D1 := [[1, 2, 1], [1, 2, 0], [1, 2, 4], [1, 2, 3], [1, 2, 2]]
  D2 := [[1, 2, 3], [1, 2, 2], [1, 2, 1], [1, 2, 0], [1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_78_37_10 : ColCertDiv where
  rK := ⟨78, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T78_37
  T2 := Q2.T78_37_2
  h1 := (2,2,4,4,2)
  h2 := (2,2,4,4,3)
  D1 := [[2, 4, 1], [2, 4, 4], [2, 4, 2], [2, 4, 0], [2, 4, 3]]
  D2 := [[2, 4, 0], [2, 4, 3], [2, 4, 1], [2, 4, 4], [2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_78_37_15 : ColCertDiv where
  rK := ⟨78, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T78_37
  T2 := Q2.T78_37_2
  h1 := (3,3,1,0,3)
  h2 := (3,3,1,0,2)
  D1 := [[3, 1, 0], [3, 1, 2], [3, 1, 4], [3, 1, 1], [3, 1, 3]]
  D2 := [[3, 1, 1], [3, 1, 3], [3, 1, 0], [3, 1, 2], [3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_78_37_20 : ColCertDiv where
  rK := ⟨78, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T78_37
  T2 := Q2.T78_37_2
  h1 := (4,4,3,2,2)
  h2 := (4,4,3,2,4)
  D1 := [[4, 3, 3], [4, 3, 4], [4, 3, 0], [4, 3, 1], [4, 3, 2]]
  D2 := [[4, 3, 1], [4, 3, 2], [4, 3, 3], [4, 3, 4], [4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_78_42_5 : ColCertDiv where
  rK := ⟨78, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T78_42
  T2 := Q2.T78_42_2
  h1 := (1,1,3,4,4)
  h2 := (1,1,3,4,2)
  D1 := [[1, 3, 1], [1, 3, 0], [1, 3, 4], [1, 3, 3], [1, 3, 2]]
  D2 := [[1, 3, 3], [1, 3, 2], [1, 3, 1], [1, 3, 0], [1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_78_42_10 : ColCertDiv where
  rK := ⟨78, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T78_42
  T2 := Q2.T78_42_2
  h1 := (2,2,1,4,0)
  h2 := (2,2,1,4,1)
  D1 := [[2, 1, 3], [2, 1, 1], [2, 1, 4], [2, 1, 2], [2, 1, 0]]
  D2 := [[2, 1, 2], [2, 1, 0], [2, 1, 3], [2, 1, 1], [2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_78_42_15 : ColCertDiv where
  rK := ⟨78, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T78_42
  T2 := Q2.T78_42_2
  h1 := (3,3,4,0,4)
  h2 := (3,3,4,0,3)
  D1 := [[3, 4, 1], [3, 4, 3], [3, 4, 0], [3, 4, 2], [3, 4, 4]]
  D2 := [[3, 4, 2], [3, 4, 4], [3, 4, 1], [3, 4, 3], [3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_78_42_20 : ColCertDiv where
  rK := ⟨78, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T78_42
  T2 := Q2.T78_42_2
  h1 := (4,4,2,2,2)
  h2 := (4,4,2,2,4)
  D1 := [[4, 2, 0], [4, 2, 1], [4, 2, 2], [4, 2, 3], [4, 2, 4]]
  D2 := [[4, 2, 3], [4, 2, 4], [4, 2, 0], [4, 2, 1], [4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_78_47_5 : ColCertDiv where
  rK := ⟨78, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T78_47
  T2 := Q2.T78_47_2
  h1 := (1,1,1,4,2)
  h2 := (1,1,1,4,0)
  D1 := [[1, 1, 2], [1, 1, 1], [1, 1, 0], [1, 1, 4], [1, 1, 3]]
  D2 := [[1, 1, 4], [1, 1, 3], [1, 1, 2], [1, 1, 1], [1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_78_47_10 : ColCertDiv where
  rK := ⟨78, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T78_47
  T2 := Q2.T78_47_2
  h1 := (2,2,2,4,4)
  h2 := (2,2,2,4,0)
  D1 := [[2, 2, 1], [2, 2, 4], [2, 2, 2], [2, 2, 0], [2, 2, 3]]
  D2 := [[2, 2, 0], [2, 2, 3], [2, 2, 1], [2, 2, 4], [2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_78_47_15 : ColCertDiv where
  rK := ⟨78, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T78_47
  T2 := Q2.T78_47_2
  h1 := (3,3,3,0,2)
  h2 := (3,3,3,0,1)
  D1 := [[3, 3, 2], [3, 3, 4], [3, 3, 1], [3, 3, 3], [3, 3, 0]]
  D2 := [[3, 3, 3], [3, 3, 0], [3, 3, 2], [3, 3, 4], [3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_78_47_20 : ColCertDiv where
  rK := ⟨78, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T78_47
  T2 := Q2.T78_47_2
  h1 := (4,4,4,2,2)
  h2 := (4,4,4,2,4)
  D1 := [[4, 4, 0], [4, 4, 1], [4, 4, 2], [4, 4, 3], [4, 4, 4]]
  D2 := [[4, 4, 3], [4, 4, 4], [4, 4, 0], [4, 4, 1], [4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_78_52_5 : ColCertDiv where
  rK := ⟨78, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T78_52
  T2 := Q2.T78_52_2
  h1 := (1,1,0,4,1)
  h2 := (1,1,0,4,4)
  D1 := [[1, 0, 4], [1, 0, 3], [1, 0, 2], [1, 0, 1], [1, 0, 0]]
  D2 := [[1, 0, 1], [1, 0, 0], [1, 0, 4], [1, 0, 3], [1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_78_52_10 : ColCertDiv where
  rK := ⟨78, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T78_52
  T2 := Q2.T78_52_2
  h1 := (2,2,0,4,1)
  h2 := (2,2,0,4,2)
  D1 := [[2, 0, 3], [2, 0, 1], [2, 0, 4], [2, 0, 2], [2, 0, 0]]
  D2 := [[2, 0, 2], [2, 0, 0], [2, 0, 3], [2, 0, 1], [2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_78_52_15 : ColCertDiv where
  rK := ⟨78, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T78_52
  T2 := Q2.T78_52_2
  h1 := (3,3,0,0,1)
  h2 := (3,3,0,0,0)
  D1 := [[3, 0, 2], [3, 0, 4], [3, 0, 1], [3, 0, 3], [3, 0, 0]]
  D2 := [[3, 0, 3], [3, 0, 0], [3, 0, 2], [3, 0, 4], [3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_78_52_20 : ColCertDiv where
  rK := ⟨78, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T78_52
  T2 := Q2.T78_52_2
  h1 := (4,4,0,2,2)
  h2 := (4,4,0,2,4)
  D1 := [[4, 0, 1], [4, 0, 2], [4, 0, 3], [4, 0, 4], [4, 0, 0]]
  D2 := [[4, 0, 4], [4, 0, 0], [4, 0, 1], [4, 0, 2], [4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_79_32_5 : ColCertDiv where
  rK := ⟨79, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T79_32
  T2 := Q2.T79_32_2
  h1 := (1,1,4,4,0)
  h2 := (1,1,4,4,3)
  D1 := [[1, 4, 1], [1, 4, 0], [1, 4, 4], [1, 4, 3], [1, 4, 2]]
  D2 := [[1, 4, 4], [1, 4, 3], [1, 4, 2], [1, 4, 1], [1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_79_32_10 : ColCertDiv where
  rK := ⟨79, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T79_32
  T2 := Q2.T79_32_2
  h1 := (2,2,3,4,3)
  h2 := (2,2,3,4,4)
  D1 := [[2, 3, 4], [2, 3, 2], [2, 3, 0], [2, 3, 3], [2, 3, 1]]
  D2 := [[2, 3, 0], [2, 3, 3], [2, 3, 1], [2, 3, 4], [2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_79_32_15 : ColCertDiv where
  rK := ⟨79, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T79_32
  T2 := Q2.T79_32_2
  h1 := (3,3,2,0,0)
  h2 := (3,3,2,0,4)
  D1 := [[3, 2, 4], [3, 2, 1], [3, 2, 3], [3, 2, 0], [3, 2, 2]]
  D2 := [[3, 2, 3], [3, 2, 0], [3, 2, 2], [3, 2, 4], [3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_79_32_20 : ColCertDiv where
  rK := ⟨79, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T79_32
  T2 := Q2.T79_32_2
  h1 := (4,4,1,2,2)
  h2 := (4,4,1,2,4)
  D1 := [[4, 1, 1], [4, 1, 2], [4, 1, 3], [4, 1, 4], [4, 1, 0]]
  D2 := [[4, 1, 3], [4, 1, 4], [4, 1, 0], [4, 1, 1], [4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_79_37_5 : ColCertDiv where
  rK := ⟨79, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T79_37
  T2 := Q2.T79_37_2
  h1 := (1,1,2,4,3)
  h2 := (1,1,2,4,1)
  D1 := [[1, 2, 3], [1, 2, 2], [1, 2, 1], [1, 2, 0], [1, 2, 4]]
  D2 := [[1, 2, 1], [1, 2, 0], [1, 2, 4], [1, 2, 3], [1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_79_37_10 : ColCertDiv where
  rK := ⟨79, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T79_37
  T2 := Q2.T79_37_2
  h1 := (2,2,4,4,2)
  h2 := (2,2,4,4,3)
  D1 := [[2, 4, 2], [2, 4, 0], [2, 4, 3], [2, 4, 1], [2, 4, 4]]
  D2 := [[2, 4, 3], [2, 4, 1], [2, 4, 4], [2, 4, 2], [2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
