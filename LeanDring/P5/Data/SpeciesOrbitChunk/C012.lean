/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin2.SpeciesOrbitData

/-! Species-side orbit chunk, q=2, 5: kernel `decide` of the coset-orbit checkers over reps [96, 104).
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace LeanDring.P5Presentation.Q2

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem cosetOrbChunk5 : cosetOrbCheckRange 96 104  = true := by decide

end LeanDring.P5Presentation.Q2
