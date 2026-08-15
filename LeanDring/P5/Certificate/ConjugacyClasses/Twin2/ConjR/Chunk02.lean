/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.ConjugacyClasses.Twin2.ConjData

/-!
# q=2 conjugation row 1 check : `(subAt i)^{g_1} = subAt (conjMove 1 i)`, all 676 `i`.

A single kernel `decide` over the zip of `Q2.allBases` with row 1 of `conjTab`,
isolated in its own process. No `native_decide`.
-/

namespace LeanDring.P5Presentation

namespace Q2

set_option maxRecDepth 100000

set_option maxHeartbeats 10000000 in
-- kernel decide over large certified lists needs extra heartbeats
theorem conjRowCheck_1 : conjRowCheck 1 = true := by decide

end Q2

end LeanDring.P5Presentation
