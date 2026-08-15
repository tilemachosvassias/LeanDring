/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin1.CharExhaust

/-!
# Discharging `CharsAtComplete` by decided exhaustiveness (`k = 3`, chunk b)

Kernel `decide` of `exhaustiveCheck` over representatives `63…70` (each with `k = 3`
echelon generators, a `25³`-element enumeration). Sibling chunk of
`LeanDring.P5.Certificate.Characters.Twin1.CharComplete`; see that file's
module doc for the overall plan.
-/

namespace LeanDring.P5Presentation

set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
-- kernel decide over large certified lists needs extra heartbeats
/-- **Exhaustiveness for representatives `63…70`.** -/
theorem exhaustiveCheck_r63_70 : (List.range' 63 8).all exhaustiveCheck = true := by decide

end LeanDring.P5Presentation
