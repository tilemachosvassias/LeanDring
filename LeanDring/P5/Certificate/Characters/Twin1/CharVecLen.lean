/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin1.CharCert

/-!
# Per-representative character-vector length certification

The character-realization layer
(`LeanDring.P5.Certificate.Characters.Twin1.CharExtend`) needs that *every*
embedded exponent vector of `reps r` has length equal to the number of pcgs
generators (`(basisAt r).length`).  Without this the injectivity of
`e ↦ charOfVec r e` on the certified list would fail: two list-distinct vectors
agreeing on the first `k` entries (but differing beyond `k`) would define the
same character.

The check `checkVecLen` is pure `Nat`-length arithmetic over the embedded data
(no sift, no `ZMod` multiplication); it is nonetheless chunked into four
37-representative kernel `decide`s (mirroring the `checkCount` chunking) because
materialising the full `repChars` literal in the kernel is the dominant cost.
-/

namespace LeanDring.P5Presentation

set_option maxRecDepth 100000

/-- Every embedded character vector of `reps r` has length equal to the number
of echelon generators of `reps r`. -/
def checkVecLen (r : Nat) : Bool :=
  (repChars.getD r []).all (fun e => Nat.beq e.length (repBases.getD r []).length)

theorem vecLenChunk0 : ((List.range 148).take 37).all checkVecLen = true := by decide

theorem vecLenChunk1 : (((List.range 148).drop 37).take 37).all checkVecLen = true := by decide

theorem vecLenChunk2 :
    ((((List.range 148).drop 37).drop 37).take 37).all checkVecLen = true := by decide

theorem vecLenChunk3 :
    ((((List.range 148).drop 37).drop 37).drop 37).all checkVecLen = true := by decide

end LeanDring.P5Presentation
