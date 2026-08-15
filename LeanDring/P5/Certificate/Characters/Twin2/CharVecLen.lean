/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharCert

/-!
# Per-representative q=2 character-vector length certification (character-vector length, twin q=2)

The q=2 twin of `LeanDring/P5/Certificate/Characters/Twin1/CharVecLen.lean`. Every embedded q=2
exponent vector of `reps r` has
length equal to the number of pcgs generators (`(basisAt2 r).length`), needed for
the injectivity of `e ↦ charOfVec2 r e`. Pure `Nat`-length arithmetic over the
embedded data, chunked into four 37-representative kernel `decide`s.
-/

namespace LeanDring.P5Presentation

namespace Q2

set_option maxRecDepth 100000

/-- Every embedded q=2 character vector of `reps r` has length equal to the number
of echelon generators of `reps r`. -/
def checkVecLen2 (r : Nat) : Bool :=
  (repChars2.getD r []).all (fun e => Nat.beq e.length (repBases2.getD r []).length)

theorem vecLenChunk2_0 : ((List.range 148).take 37).all checkVecLen2 = true := by decide

theorem vecLenChunk2_1 : (((List.range 148).drop 37).take 37).all checkVecLen2 = true := by decide

theorem vecLenChunk2_2 :
    ((((List.range 148).drop 37).drop 37).take 37).all checkVecLen2 = true := by decide

theorem vecLenChunk2_3 :
    ((((List.range 148).drop 37).drop 37).drop 37).all checkVecLen2 = true := by decide

end Q2

end LeanDring.P5Presentation
