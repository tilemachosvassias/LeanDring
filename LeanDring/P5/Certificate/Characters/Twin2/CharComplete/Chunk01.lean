/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharExhaust

/-!
# Discharging `CharsAtComplete` by decided exhaustiveness (Step 3, q=2, `k = 3` chunk a)

Kernel `decide` of the q=2 `exhaustiveCheck2` over representatives 55…62 (each with
`k = 3` echelon generators, a `25³`-element enumeration on the q=2 solution set).
q=2 twin of `LeanDring.P5.Certificate.Characters.Twin1.CharComplete.Chunk01`; the
vector sets differ for the divergent classes but the enumeration and count are
identical in shape.
-/

namespace LeanDring.P5Presentation

namespace Q2

set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
-- kernel decide over large certified lists needs extra heartbeats
/-- **Exhaustiveness for representatives 55…62 (q=2).** -/
theorem exhaustiveCheck2_r55_62 : (List.range' 55 8).all exhaustiveCheck2 = true := by decide

end Q2

end LeanDring.P5Presentation
