/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# The quadratic Gauss sum: its square and its modulus

Self-contained, Mathlib-upstreamable development of the classical quadratic
Gauss sum over `ZMod p` (`p` an odd prime), with the **standard** additive
character `ψ = ZMod.stdAddChar` (`j ↦ exp(2πi·j/p)`) and `χ` the quadratic
(Legendre) character interpreted in `ℂ`:

`g(p) = gaussSum χ ψ = ∑_{n} χ(n)·exp(2πi·n/p) = ∑_{n} exp(2πi·n²/p)`.

This file has **no D-ring imports** and is intended to become a stand-alone
number-theory contribution.

## This file

* `gaussSum_quadratic_sq` — `g² = χ(-1)·p` (Mathlib's `gaussSum_sq` for the
  standard primitive character);
* `norm_gaussSum_quadratic` — `‖g‖ = √p`.

Together these pin `g` to one of `±√p`, `±i√p`. Determining which — Gauss's
sign theorem, `g = √p` for `p ≡ 1 (mod 4)` and `g = i·√p` for `p ≡ 3 (mod 4)`
— is the classical content, proved in `GaussSignTheorem.lean` (`gauss_eq`) and
restated as `rootNumber χ = 1` in `GaussRootNumber.lean`.
-/

namespace LeanDring.GaussSign

open scoped Real
open Complex ZMod

variable (p : ℕ) [Fact p.Prime]

/-- The quadratic (Legendre) character of `ZMod p`, valued in `ℂ`. -/
noncomputable def χℂ : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

/-- The quadratic Gauss sum `∑_n exp(2πi n²/p)`, as `gaussSum χ ψ` with the
standard additive character. -/
noncomputable def gauss : ℂ := gaussSum (χℂ p) stdAddChar

variable {p} in
/-- The composed quadratic character is nontrivial for odd `p`. -/
theorem χℂ_ne_one (hp2 : p ≠ 2) : χℂ p ≠ 1 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; exact hp2
  exact (MulChar.ringHomComp_ne_one_iff Int.cast_injective).mpr
    (quadraticChar_ne_one hchar)

/-- The composed quadratic character is quadratic. -/
theorem χℂ_isQuadratic : (χℂ p).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod p)).comp _

variable {p} in
/-- **The square of the quadratic Gauss sum**: `g² = χ(-1)·p`. -/
theorem gaussSum_quadratic_sq (hp2 : p ≠ 2) :
    gauss p ^ 2 = χℂ p (-1) * p := by
  have h : gauss p ^ 2 = χℂ p (-1) * (Fintype.card (ZMod p) : ℂ) :=
    gaussSum_sq (χℂ_ne_one hp2) (χℂ_isQuadratic p) (isPrimitive_stdAddChar p)
  rw [h, ZMod.card]

/-- `χ(-1)` has modulus `1`. -/
theorem norm_χℂ_neg_one : ‖χℂ p (-1)‖ = 1 := by
  have hval : χℂ p (-1) = ((quadraticChar (ZMod p) (-1) : ℤ) : ℂ) := rfl
  have hsq : quadraticChar (ZMod p) (-1) ^ 2 = 1 :=
    quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero)
  have hpm : quadraticChar (ZMod p) (-1) = 1 ∨
      quadraticChar (ZMod p) (-1) = -1 :=
    mul_self_eq_one_iff.mp (by rw [← pow_two]; exact hsq)
  rw [hval]
  rcases hpm with h | h <;> rw [h] <;> norm_num

variable {p} in
/-- **The modulus of the quadratic Gauss sum**: `‖g‖ = √p`. -/
theorem norm_gaussSum_quadratic (hp2 : p ≠ 2) : ‖gauss p‖ = Real.sqrt p := by
  have hnormsq : ‖gauss p‖ ^ 2 = p := by
    rw [← norm_pow, gaussSum_quadratic_sq hp2, norm_mul, norm_χℂ_neg_one,
      one_mul, Complex.norm_natCast]
  rw [← Real.sqrt_sq (norm_nonneg _), hnormsq]

end LeanDring.GaussSign
