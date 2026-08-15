/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.ConjugacyClasses.Twin2.ConjData

/-!
# q=2 class-label bound and representative-consistency checks (conjugacy classes, twin q=2).
-/

namespace LeanDring.P5Presentation

namespace Q2

set_option maxRecDepth 100000

set_option maxHeartbeats 10000000 in
-- kernel decide over large certified lists needs extra heartbeats
theorem classOfBound_true :
    (List.range 676).all (fun i => Nat.blt (classOfD i) 148) = true :=
  all676_of_chunks _ (by decide) (by decide) (by decide) (by decide)

set_option maxHeartbeats 10000000 in
-- kernel decide over large certified lists needs extra heartbeats
theorem repRange_true :
    (List.range 148).all (fun c =>
      Nat.blt (classRepsData.getD c 0) 676 && Nat.beq (classOfD (classRepsData.getD c 0)) c)
      = true := by decide

set_option maxHeartbeats 10000000 in
-- kernel decide over large certified lists needs extra heartbeats
theorem repIdx_true :
    (List.range 676).all (fun i =>
      !(isRepData.getD i false) || Nat.beq (classRepsData.getD (classOfD i) 0) i) = true :=
  all676_of_chunks _ (by decide) (by decide) (by decide) (by decide)

end Q2

end LeanDring.P5Presentation
