/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.FixZero.C001
import LeanDring.P5.Data.FixZero.C002
import LeanDring.P5.Data.FixZero.C003
import LeanDring.P5.Data.FixZero.C004
import LeanDring.P5.Data.FixZero.C005
import LeanDring.P5.Data.FixZero.C006
import LeanDring.P5.Data.FixZero.C007
import LeanDring.P5.Data.FixZero.C008
import LeanDring.P5.Data.FixZero.C009
import LeanDring.P5.Data.FixZero.C010
import LeanDring.P5.Data.FixZero.C011
import LeanDring.P5.Data.FixZero.C012
import LeanDring.P5.Data.FixZero.C013
import LeanDring.P5.Data.FixZero.C014
import LeanDring.P5.Data.FixZero.C015
import LeanDring.P5.Data.FixZero.C016
import LeanDring.P5.Data.FixZero.C017
import LeanDring.P5.Data.FixZero.C018
import LeanDring.P5.Data.FixZero.C019
import LeanDring.P5.Data.FixZero.C020
import LeanDring.P5.Data.FixZero.C021
import LeanDring.P5.Data.FixZero.C022
import LeanDring.P5.Data.FixZero.C023
import LeanDring.P5.Data.FixZero.C024
import LeanDring.P5.Data.FixZero.C025
import LeanDring.P5.Data.FixZero.C026
import LeanDring.P5.Data.FixZero.C027
import LeanDring.P5.Data.FixZero.C028
import LeanDring.P5.Data.FixZero.C029
import LeanDring.P5.Data.FixZero.C030
import LeanDring.P5.Data.FixZero.C031
import LeanDring.P5.Data.FixZero.C032
import LeanDring.P5.Data.FixZero.C033
import LeanDring.P5.Data.FixZero.C034
import LeanDring.P5.Data.FixZero.C035
import LeanDring.P5.Data.FixZero.C036
import LeanDring.P5.Data.FixZero.C037
import LeanDring.P5.Data.FixZero.C038
import LeanDring.P5.Data.FixZero.C039
import LeanDring.P5.Data.FixZero.C040
import LeanDring.P5.Data.FixZero.C041
import LeanDring.P5.Data.FixZero.C042
import LeanDring.P5.Data.FixZero.C043
import LeanDring.P5.Data.FixZero.C044
import LeanDring.P5.Data.FixZero.C045
import LeanDring.P5.Data.FixZero.C046
import LeanDring.P5.Data.FixZero.C047
import LeanDring.P5.Data.FixZero.C048
import LeanDring.P5.Data.FixZero.C049
import LeanDring.P5.Data.FixZero.C050
import LeanDring.P5.Data.FixZero.C051
import LeanDring.P5.Data.FixZero.C052
import LeanDring.P5.Data.FixZero.C053
import LeanDring.P5.Data.FixZero.C054
import LeanDring.P5.Data.FixZero.C055
import LeanDring.P5.Data.FixZero.C056
import LeanDring.P5.Data.FixZero.C057
import LeanDring.P5.Data.FixZero.C058
import LeanDring.P5.Data.FixZero.C059
import LeanDring.P5.Data.FixZero.C060
import LeanDring.P5.Data.FixZero.C061
import LeanDring.P5.Data.FixZero.C062
import LeanDring.P5.Data.FixZero.C063
import LeanDring.P5.Data.FixZero.C064
import LeanDring.P5.Data.FixZero.C065
import LeanDring.P5.Data.FixZero.C066
import LeanDring.P5.Data.FixZero.C067
import LeanDring.P5.Data.FixZero.C068
import LeanDring.P5.Data.FixZero.C069
import LeanDring.P5.Data.FixZero.C070
import LeanDring.P5.Data.FixZero.C071
import LeanDring.P5.Data.FixZero.C072
import LeanDring.P5.Data.FixZero.C073
import LeanDring.P5.Data.FixZero.C074
import LeanDring.P5.Data.FixZero.C075
import LeanDring.P5.Data.FixZero.C076
import LeanDring.P5.Data.FixZero.C077
import LeanDring.P5.Data.FixZero.C078
import LeanDring.P5.Data.FixZero.C079
import LeanDring.P5.Data.FixZero.C080
import LeanDring.P5.Data.FixZero.C081
import LeanDring.P5.Data.FixZero.C082
import LeanDring.P5.Data.FixZero.C083
import LeanDring.P5.Data.FixZero.C084
import LeanDring.P5.Data.FixZero.C085
import LeanDring.P5.Data.FixZero.C086
import LeanDring.P5.Data.FixZero.C087
import LeanDring.P5.Data.FixZero.C088

/-!
# P5 Data family: FixZero (88 chunks)

# Species-table cells, off-support emptiness certificates

For each `(rK, rH)` in this chunk the `H`-fixed part of `G/K` is EMPTY (while
`|H| <= |K|`, so the order bound does not apply): one batched kernel `decide` per
class scans the certified full transversal `R<rK>`, and the per-pair theorems
reflect it through `repsFixedCard` into the fixed-point count.  Feeds
`species_zero_of_fixCard_zero` (`LeanDring/P5/Certificate/Support/Stage5Core.lean`).
Auto-emitted by `python/p5_fixzero_emit.py`.

This index imports all 88 chunks of the `FixZero` family in
`LeanDring/P5/Data/FixZero/`. Files in this family are machine-emitted
data certificates (see the per-chunk docstrings and the emitter scripts
referenced there); they are not intended to be read chunk-by-chunk and are
skippable for readers auditing the hand-written mathematics in
`LeanDring/Theory/`, `LeanDring/P4/`, and `LeanDring/P5/Certificate/`.
-/

