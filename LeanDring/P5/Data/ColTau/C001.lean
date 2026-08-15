/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryA.C001
import LeanDring.P5.Data.EntryK.C025
import LeanDring.P5.Data.EntryK.C026
import LeanDring.P5.Data.EntryK.C027
import LeanDring.P5.Data.EntryK.C028
import LeanDring.P5.Data.EntryK.C029

/-!
# Species-table cell data, stage 2 — τ-moved columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
tau tier, chunk 0: 28 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_13_13_5 : ColCertDiv where
  rK := ⟨13, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T13_13
  T2 := Q2.T13_13_2
  h1 := (0,0,1,0,4)
  h2 := (0,0,1,0,4)
  D1 := [[1, 0], [1, 0], [1, 0], [1, 0], [1, 0]]
  D2 := [[1, 0], [1, 0], [1, 0], [1, 0], [1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_13_13_6 : ColCertDiv where
  rK := ⟨13, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T13_13
  T2 := Q2.T13_13_2
  h1 := (0,0,1,1,4)
  h2 := (0,0,1,1,4)
  D1 := [[1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]
  D2 := [[1, 1], [1, 1], [1, 1], [1, 1], [1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_13_13_7 : ColCertDiv where
  rK := ⟨13, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T13_13
  T2 := Q2.T13_13_2
  h1 := (0,0,1,2,4)
  h2 := (0,0,1,2,4)
  D1 := [[1, 2], [1, 2], [1, 2], [1, 2], [1, 2]]
  D2 := [[1, 2], [1, 2], [1, 2], [1, 2], [1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_13_13_8 : ColCertDiv where
  rK := ⟨13, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T13_13
  T2 := Q2.T13_13_2
  h1 := (0,0,1,3,4)
  h2 := (0,0,1,3,4)
  D1 := [[1, 3], [1, 3], [1, 3], [1, 3], [1, 3]]
  D2 := [[1, 3], [1, 3], [1, 3], [1, 3], [1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_13_5 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T116_13
  T2 := Q2.T116_13_2
  h1 := (0,0,1,0,4)
  h2 := (0,0,1,0,4)
  D1 := [[0, 1, 0, 4], [0, 1, 0, 4], [0, 1, 0, 4], [0, 1, 0, 4], [0, 1, 0, 4]]
  D2 := [[0, 1, 0, 4], [0, 1, 0, 4], [0, 1, 0, 4], [0, 1, 0, 4], [0, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_13_6 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T116_13
  T2 := Q2.T116_13_2
  h1 := (0,0,1,1,4)
  h2 := (0,0,1,1,4)
  D1 := [[0, 1, 1, 4], [0, 1, 1, 0], [0, 1, 1, 1], [0, 1, 1, 2], [0, 1, 1, 3]]
  D2 := [[0, 1, 1, 4], [0, 1, 1, 0], [0, 1, 1, 1], [0, 1, 1, 2], [0, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_13_7 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T116_13
  T2 := Q2.T116_13_2
  h1 := (0,0,1,2,4)
  h2 := (0,0,1,2,4)
  D1 := [[0, 1, 2, 4], [0, 1, 2, 1], [0, 1, 2, 3], [0, 1, 2, 0], [0, 1, 2, 2]]
  D2 := [[0, 1, 2, 4], [0, 1, 2, 1], [0, 1, 2, 3], [0, 1, 2, 0], [0, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_13_8 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T116_13
  T2 := Q2.T116_13_2
  h1 := (0,0,1,3,4)
  h2 := (0,0,1,3,4)
  D1 := [[0, 1, 3, 4], [0, 1, 3, 2], [0, 1, 3, 0], [0, 1, 3, 3], [0, 1, 3, 1]]
  D2 := [[0, 1, 3, 4], [0, 1, 3, 2], [0, 1, 3, 0], [0, 1, 3, 3], [0, 1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_117_13_5 : ColCertDiv where
  rK := ⟨117, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T117_13
  T2 := Q2.T117_13_2
  h1 := (0,0,1,0,4)
  h2 := (0,0,1,0,4)
  D1 := [[0, 1, 0, 3], [0, 1, 0, 4], [0, 1, 0, 0], [0, 1, 0, 1], [0, 1, 0, 2]]
  D2 := [[0, 1, 0, 3], [0, 1, 0, 4], [0, 1, 0, 0], [0, 1, 0, 1], [0, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_117_13_6 : ColCertDiv where
  rK := ⟨117, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T117_13
  T2 := Q2.T117_13_2
  h1 := (0,0,1,1,4)
  h2 := (0,0,1,1,4)
  D1 := [[0, 1, 1, 3], [0, 1, 1, 4], [0, 1, 1, 0], [0, 1, 1, 1], [0, 1, 1, 2]]
  D2 := [[0, 1, 1, 3], [0, 1, 1, 4], [0, 1, 1, 0], [0, 1, 1, 1], [0, 1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_117_13_7 : ColCertDiv where
  rK := ⟨117, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T117_13
  T2 := Q2.T117_13_2
  h1 := (0,0,1,2,4)
  h2 := (0,0,1,2,4)
  D1 := [[0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 2, 0], [0, 1, 2, 1], [0, 1, 2, 2]]
  D2 := [[0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 2, 0], [0, 1, 2, 1], [0, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_117_13_8 : ColCertDiv where
  rK := ⟨117, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T117_13
  T2 := Q2.T117_13_2
  h1 := (0,0,1,3,4)
  h2 := (0,0,1,3,4)
  D1 := [[0, 1, 3, 3], [0, 1, 3, 4], [0, 1, 3, 0], [0, 1, 3, 1], [0, 1, 3, 2]]
  D2 := [[0, 1, 3, 3], [0, 1, 3, 4], [0, 1, 3, 0], [0, 1, 3, 1], [0, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_13_5 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T118_13
  T2 := Q2.T118_13_2
  h1 := (0,0,1,0,4)
  h2 := (0,0,1,0,4)
  D1 := [[0, 1, 0, 1], [0, 1, 0, 2], [0, 1, 0, 3], [0, 1, 0, 4], [0, 1, 0, 0]]
  D2 := [[0, 1, 0, 1], [0, 1, 0, 2], [0, 1, 0, 3], [0, 1, 0, 4], [0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_13_6 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T118_13
  T2 := Q2.T118_13_2
  h1 := (0,0,1,1,4)
  h2 := (0,0,1,1,4)
  D1 := [[0, 1, 1, 1], [0, 1, 1, 2], [0, 1, 1, 3], [0, 1, 1, 4], [0, 1, 1, 0]]
  D2 := [[0, 1, 1, 1], [0, 1, 1, 2], [0, 1, 1, 3], [0, 1, 1, 4], [0, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_13_7 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T118_13
  T2 := Q2.T118_13_2
  h1 := (0,0,1,2,4)
  h2 := (0,0,1,2,4)
  D1 := [[0, 1, 2, 1], [0, 1, 2, 2], [0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 2, 0]]
  D2 := [[0, 1, 2, 1], [0, 1, 2, 2], [0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_13_8 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T118_13
  T2 := Q2.T118_13_2
  h1 := (0,0,1,3,4)
  h2 := (0,0,1,3,4)
  D1 := [[0, 1, 3, 1], [0, 1, 3, 2], [0, 1, 3, 3], [0, 1, 3, 4], [0, 1, 3, 0]]
  D2 := [[0, 1, 3, 1], [0, 1, 3, 2], [0, 1, 3, 3], [0, 1, 3, 4], [0, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_68_19 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T118_68
  T2 := Q2.T118_68_2
  h1 := (3,1,4,0,4)
  h2 := (3,1,4,0,1)
  D1 := [[3, 4, 4, 4], [3, 4, 1, 4], [3, 4, 3, 4], [3, 4, 0, 4], [3, 4, 2, 4]]
  D2 := [[3, 4, 4, 0], [3, 4, 1, 0], [3, 4, 3, 0], [3, 4, 0, 0], [3, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_68_20 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T118_68
  T2 := Q2.T118_68_2
  h1 := (4,3,0,0,1)
  h2 := (4,3,0,0,0)
  D1 := [[4, 0, 3, 3], [4, 0, 4, 3], [4, 0, 0, 3], [4, 0, 1, 3], [4, 0, 2, 3]]
  D2 := [[4, 0, 3, 1], [4, 0, 4, 1], [4, 0, 0, 1], [4, 0, 1, 1], [4, 0, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_68_21 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T118_68
  T2 := Q2.T118_68_2
  h1 := (4,3,1,2,1)
  h2 := (4,3,1,2,0)
  D1 := [[4, 1, 0, 4], [4, 1, 1, 0], [4, 1, 2, 1], [4, 1, 3, 2], [4, 1, 4, 3]]
  D2 := [[4, 1, 0, 2], [4, 1, 1, 3], [4, 1, 2, 4], [4, 1, 3, 0], [4, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_118_68_22 : ColCertDiv where
  rK := ⟨118, by decide⟩
  rH := ⟨68, by decide⟩
  m := 5
  T1 := T118_68
  T2 := Q2.T118_68_2
  h1 := (4,3,2,4,1)
  h2 := (4,3,2,4,0)
  D1 := [[4, 2, 2, 0], [4, 2, 3, 2], [4, 2, 4, 4], [4, 2, 0, 1], [4, 2, 1, 3]]
  D2 := [[4, 2, 2, 3], [4, 2, 3, 0], [4, 2, 4, 2], [4, 2, 0, 4], [4, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_13_5 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T119_13
  T2 := Q2.T119_13_2
  h1 := (0,0,1,0,4)
  h2 := (0,0,1,0,4)
  D1 := [[0, 1, 0, 2], [0, 1, 0, 3], [0, 1, 0, 4], [0, 1, 0, 0], [0, 1, 0, 1]]
  D2 := [[0, 1, 0, 2], [0, 1, 0, 3], [0, 1, 0, 4], [0, 1, 0, 0], [0, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_13_6 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T119_13
  T2 := Q2.T119_13_2
  h1 := (0,0,1,1,4)
  h2 := (0,0,1,1,4)
  D1 := [[0, 1, 1, 2], [0, 1, 1, 3], [0, 1, 1, 4], [0, 1, 1, 0], [0, 1, 1, 1]]
  D2 := [[0, 1, 1, 2], [0, 1, 1, 3], [0, 1, 1, 4], [0, 1, 1, 0], [0, 1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_13_7 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T119_13
  T2 := Q2.T119_13_2
  h1 := (0,0,1,2,4)
  h2 := (0,0,1,2,4)
  D1 := [[0, 1, 2, 2], [0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 2, 0], [0, 1, 2, 1]]
  D2 := [[0, 1, 2, 2], [0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 2, 0], [0, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_119_13_8 : ColCertDiv where
  rK := ⟨119, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T119_13
  T2 := Q2.T119_13_2
  h1 := (0,0,1,3,4)
  h2 := (0,0,1,3,4)
  D1 := [[0, 1, 3, 2], [0, 1, 3, 3], [0, 1, 3, 4], [0, 1, 3, 0], [0, 1, 3, 1]]
  D2 := [[0, 1, 3, 2], [0, 1, 3, 3], [0, 1, 3, 4], [0, 1, 3, 0], [0, 1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_13_5 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T120_13
  T2 := Q2.T120_13_2
  h1 := (0,0,1,0,4)
  h2 := (0,0,1,0,4)
  D1 := [[0, 1, 0, 0], [0, 1, 0, 1], [0, 1, 0, 2], [0, 1, 0, 3], [0, 1, 0, 4]]
  D2 := [[0, 1, 0, 0], [0, 1, 0, 1], [0, 1, 0, 2], [0, 1, 0, 3], [0, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_13_6 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T120_13
  T2 := Q2.T120_13_2
  h1 := (0,0,1,1,4)
  h2 := (0,0,1,1,4)
  D1 := [[0, 1, 1, 0], [0, 1, 1, 1], [0, 1, 1, 2], [0, 1, 1, 3], [0, 1, 1, 4]]
  D2 := [[0, 1, 1, 0], [0, 1, 1, 1], [0, 1, 1, 2], [0, 1, 1, 3], [0, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_13_7 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T120_13
  T2 := Q2.T120_13_2
  h1 := (0,0,1,2,4)
  h2 := (0,0,1,2,4)
  D1 := [[0, 1, 2, 0], [0, 1, 2, 1], [0, 1, 2, 2], [0, 1, 2, 3], [0, 1, 2, 4]]
  D2 := [[0, 1, 2, 0], [0, 1, 2, 1], [0, 1, 2, 2], [0, 1, 2, 3], [0, 1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_120_13_8 : ColCertDiv where
  rK := ⟨120, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T120_13
  T2 := Q2.T120_13_2
  h1 := (0,0,1,3,4)
  h2 := (0,0,1,3,4)
  D1 := [[0, 1, 3, 0], [0, 1, 3, 1], [0, 1, 3, 2], [0, 1, 3, 3], [0, 1, 3, 4]]
  D2 := [[0, 1, 3, 0], [0, 1, 3, 1], [0, 1, 3, 2], [0, 1, 3, 3], [0, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
