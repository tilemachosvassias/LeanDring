/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.ComputableModel.Twin1.Cgs

/-!
# The ambient group `Coordinate 2` has exponent dividing `25` (q=2 mirror of
`LeanDring/P5/Certificate/Characters/Twin1/CharExp.lean`)

Every element of `Coordinate 2` (SmallGroup(3125,69)) is killed by `25`, so every
linear-character value is a `25`-th root of unity — the q=2 twin of `mpow25_all`.
Despite the changed collection relation (`f₂⁵ = f₅²` vs the twin's `f₅`), the
exponent still divides 25: `g₀²⁵ = (g₀⁵)⁵ = (g₁²)⁵ = g₁¹⁰ = 1` since `g₁⁵ = 1`.
A finite check on the computable `mpow 2` power map, split into five `Fin 5`
chunks of 625 by the leading coordinate to keep each kernel `decide` in budget.
-/

namespace LeanDring.P5Presentation

namespace Q2

set_option maxRecDepth 100000
-- file-level maxHeartbeats: the kernel `decide`s below exceed the default budget
set_option linter.style.setOption false
set_option maxHeartbeats 2000000

theorem mpow25_c0 : ∀ b c d e : Fin 5,
    mpow 2 ((0 : Fin 5), b, c, d, e) 25 = ((0, 0, 0, 0, 0) : Coordinates) := by decide

theorem mpow25_c1 : ∀ b c d e : Fin 5,
    mpow 2 ((1 : Fin 5), b, c, d, e) 25 = ((0, 0, 0, 0, 0) : Coordinates) := by decide

theorem mpow25_c2 : ∀ b c d e : Fin 5,
    mpow 2 ((2 : Fin 5), b, c, d, e) 25 = ((0, 0, 0, 0, 0) : Coordinates) := by decide

theorem mpow25_c3 : ∀ b c d e : Fin 5,
    mpow 2 ((3 : Fin 5), b, c, d, e) 25 = ((0, 0, 0, 0, 0) : Coordinates) := by decide

theorem mpow25_c4 : ∀ b c d e : Fin 5,
    mpow 2 ((4 : Fin 5), b, c, d, e) 25 = ((0, 0, 0, 0, 0) : Coordinates) := by decide

/-- The computable `mpow` power map kills every element of `Coordinate 2` at
exponent `25` (glued from the five leading-coordinate chunks). The q=2 twin of
`mpow25_all`. -/
theorem mpow25_all (y : Coordinates) : mpow 2 y 25 = ((0, 0, 0, 0, 0) : Coordinates) := by
  obtain ⟨a, b, c, d, e⟩ := y
  fin_cases a
  · exact mpow25_c0 b c d e
  · exact mpow25_c1 b c d e
  · exact mpow25_c2 b c d e
  · exact mpow25_c3 b c d e
  · exact mpow25_c4 b c d e

end Q2

end LeanDring.P5Presentation
