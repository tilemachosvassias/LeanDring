/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.ConjugacyClasses.Twin1.NormOrbitData

/-! Normalizer-orbit checks, chunk 0: kernel `decide` of the action, tree and
length checkers over the first 37 representatives. -/

namespace LeanDring.P5Presentation
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

end LeanDring.P5Presentation
