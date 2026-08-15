/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.ConjugacyClasses.Twin2.NormOrbitData

/-! Orbit chunk 0 (q=2): kernel `decide` of the action/tree/len checkers over 37 reps. -/

namespace LeanDring.P5Presentation.Q2
set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
-- kernel decide over large certified lists needs extra heartbeats
theorem normActChunk0 : ((List.range 148).take 37).all checkAct = true := by decide
set_option maxHeartbeats 4000000 in
-- kernel decide over large certified lists needs extra heartbeats
theorem normTreeChunk0 : ((List.range 148).take 37).all checkTree = true := by decide
set_option maxHeartbeats 4000000 in
-- kernel decide over large certified lists needs extra heartbeats
theorem normLenChunk0 : ((List.range 148).take 37).all checkLen = true := by decide

end LeanDring.P5Presentation.Q2
