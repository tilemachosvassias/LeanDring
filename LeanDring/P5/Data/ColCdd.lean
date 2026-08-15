/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C001
import LeanDring.P5.Data.ColCdd.C002
import LeanDring.P5.Data.ColCdd.C003
import LeanDring.P5.Data.ColCdd.C004
import LeanDring.P5.Data.ColCdd.C005
import LeanDring.P5.Data.ColCdd.C006
import LeanDring.P5.Data.ColCdd.C007
import LeanDring.P5.Data.ColCdd.C008
import LeanDring.P5.Data.ColCdd.C009
import LeanDring.P5.Data.ColCdd.C010
import LeanDring.P5.Data.ColCdd.C011
import LeanDring.P5.Data.ColCdd.C012
import LeanDring.P5.Data.ColCdd.C013
import LeanDring.P5.Data.ColCdd.C014
import LeanDring.P5.Data.ColCdd.C015
import LeanDring.P5.Data.ColCdd.C016
import LeanDring.P5.Data.ColCdd.C017
import LeanDring.P5.Data.ColCdd.C018
import LeanDring.P5.Data.ColCdd.C019
import LeanDring.P5.Data.ColCdd.C020
import LeanDring.P5.Data.ColCdd.C021
import LeanDring.P5.Data.ColCdd.C022
import LeanDring.P5.Data.ColCdd.C023
import LeanDring.P5.Data.ColCdd.C024
import LeanDring.P5.Data.ColCdd.C025
import LeanDring.P5.Data.ColCdd.C026
import LeanDring.P5.Data.ColCdd.C027
import LeanDring.P5.Data.ColCdd.C028
import LeanDring.P5.Data.ColCdd.C029
import LeanDring.P5.Data.ColCdd.C030
import LeanDring.P5.Data.ColCdd.C031
import LeanDring.P5.Data.ColCdd.C032
import LeanDring.P5.Data.ColCdd.C033
import LeanDring.P5.Data.ColCdd.C034
import LeanDring.P5.Data.ColCdd.C035
import LeanDring.P5.Data.ColCdd.C036
import LeanDring.P5.Data.ColCdd.C037
import LeanDring.P5.Data.ColCdd.C038
import LeanDring.P5.Data.ColCdd.C039
import LeanDring.P5.Data.ColCdd.C040
import LeanDring.P5.Data.ColCdd.C041

/-!
# P5 Data family: ColCdd (41 chunks)

# Species-table cell data, stage 2 — column-data-divergent columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.

This index imports all 41 chunks of the `ColCdd` family in
`LeanDring/P5/Data/ColCdd/`. Files in this family are machine-emitted
data certificates (see the per-chunk docstrings and the emitter scripts
referenced there); they are not intended to be read chunk-by-chunk and are
skippable for readers auditing the hand-written mathematics in
`LeanDring/Theory/`, `LeanDring/P4/`, and `LeanDring/P5/Certificate/`.
-/

