/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C001
import LeanDring.P5.Data.EntryA.C002
import LeanDring.P5.Data.EntryA.C003
import LeanDring.P5.Data.EntryA.C004
import LeanDring.P5.Data.EntryA.C005
import LeanDring.P5.Data.EntryA.C006
import LeanDring.P5.Data.EntryA.C007
import LeanDring.P5.Data.EntryA.C008
import LeanDring.P5.Data.EntryA.C009
import LeanDring.P5.Data.EntryA.C010
import LeanDring.P5.Data.EntryA.C011
import LeanDring.P5.Data.EntryA.C012
import LeanDring.P5.Data.EntryA.C013
import LeanDring.P5.Data.EntryA.C014
import LeanDring.P5.Data.EntryA.C015
import LeanDring.P5.Data.EntryA.C016
import LeanDring.P5.Data.EntryA.C017
import LeanDring.P5.Data.EntryA.C018
import LeanDring.P5.Data.EntryA.C019
import LeanDring.P5.Data.EntryA.C020
import LeanDring.P5.Data.EntryA.C021
import LeanDring.P5.Data.EntryA.C022
import LeanDring.P5.Data.EntryA.C023
import LeanDring.P5.Data.EntryA.C024
import LeanDring.P5.Data.EntryA.C025
import LeanDring.P5.Data.EntryA.C026
import LeanDring.P5.Data.EntryA.C027
import LeanDring.P5.Data.EntryA.C028
import LeanDring.P5.Data.EntryA.C029
import LeanDring.P5.Data.EntryA.C030
import LeanDring.P5.Data.EntryA.C031
import LeanDring.P5.Data.EntryA.C032
import LeanDring.P5.Data.EntryA.C033
import LeanDring.P5.Data.EntryA.C034
import LeanDring.P5.Data.EntryA.C035
import LeanDring.P5.Data.EntryA.C036
import LeanDring.P5.Data.EntryA.C037
import LeanDring.P5.Data.EntryA.C038
import LeanDring.P5.Data.EntryA.C039
import LeanDring.P5.Data.EntryA.C040
import LeanDring.P5.Data.EntryA.C041
import LeanDring.P5.Data.EntryA.C042

/-!
# P5 Data family: EntryA (42 chunks)

# Species-table cells, A-block data (rK = 13): certified per-cell species-entry instantiations

The emit-embed-decide loop landed for the order-25 A-block class `rK = 13`
(`|G/K| = 125`), q=1.  The full 125-coset transversal `R13` and the `H`-fixed
sub-transversals `T13_rH` are embedded as kernel data; injectivity
(`reduceAux`-proxy), fixedness (`siftB`), and the fixed-point count (filter over
`R13`) are discharged by `decide` and fed through the
`LeanDring/P5/Certificate/SpeciesTable/EntryTransA.lean` adapters to
produce, per cell, a species-entry-as-power-sum theorem parametric in the certified
character `e` and the column element `h`.

This index imports all 42 chunks of the `EntryA` family in
`LeanDring/P5/Data/EntryA/`. Files in this family are machine-emitted
data certificates (see the per-chunk docstrings and the emitter scripts
referenced there); they are not intended to be read chunk-by-chunk and are
skippable for readers auditing the hand-written mathematics in
`LeanDring/Theory/`, `LeanDring/P4/`, and `LeanDring/P5/Certificate/`.
-/

