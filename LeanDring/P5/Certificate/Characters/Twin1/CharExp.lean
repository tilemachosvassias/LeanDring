/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.ComputableModel.Twin1.Cgs

/-!
# The ambient group `Coordinate 1` has exponent dividing `25`

A single group-theoretic fact needed for the completeness half of the character
count: every element of `Coordinate 1` is killed by `25`, so every character
value is a `25`-th root of unity. It is a finite check on the computable `mpow`
power map (3125 elements, each a 25-fold `mulC`), split into five `Fin 5`-indexed
chunks of 625 by the leading coordinate to keep each kernel `decide` within
budget. The bridge to the group power (`pow25_eq_one`) lives in
`LeanDring.P5.Certificate.Characters.Twin1.CharExtend`.
-/

namespace LeanDring.P5Presentation

set_option maxRecDepth 100000
-- file-level maxHeartbeats: the kernel `decide`s below exceed the default budget
set_option linter.style.setOption false
set_option maxHeartbeats 2000000

theorem mpow25_c0 : ∀ b c d e : Fin 5,
    mpow 1 ((0 : Fin 5), b, c, d, e) 25 = ((0, 0, 0, 0, 0) : Coordinates) := by decide

theorem mpow25_c1 : ∀ b c d e : Fin 5,
    mpow 1 ((1 : Fin 5), b, c, d, e) 25 = ((0, 0, 0, 0, 0) : Coordinates) := by decide

theorem mpow25_c2 : ∀ b c d e : Fin 5,
    mpow 1 ((2 : Fin 5), b, c, d, e) 25 = ((0, 0, 0, 0, 0) : Coordinates) := by decide

theorem mpow25_c3 : ∀ b c d e : Fin 5,
    mpow 1 ((3 : Fin 5), b, c, d, e) 25 = ((0, 0, 0, 0, 0) : Coordinates) := by decide

theorem mpow25_c4 : ∀ b c d e : Fin 5,
    mpow 1 ((4 : Fin 5), b, c, d, e) 25 = ((0, 0, 0, 0, 0) : Coordinates) := by decide

/-- The computable `mpow` power map kills every element of `Coordinate 1` at
exponent `25` (glued from the five leading-coordinate chunks). -/
theorem mpow25_all (y : Coordinates) : mpow 1 y 25 = ((0, 0, 0, 0, 0) : Coordinates) := by
  obtain ⟨a, b, c, d, e⟩ := y
  fin_cases a
  · exact mpow25_c0 b c d e
  · exact mpow25_c1 b c d e
  · exact mpow25_c2 b c d e
  · exact mpow25_c3 b c d e
  · exact mpow25_c4 b c d e

end LeanDring.P5Presentation
