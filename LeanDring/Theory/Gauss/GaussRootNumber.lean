/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.Gauss.GaussSignTheorem
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# The root number of the quadratic character is `1`

The canonical (Dirichlet) form of Gauss's sign theorem. Mathlib defines
`DirichletCharacter.rootNumber χ = gaussSum χ stdAddChar / I^a / N^{1/2}`
(with `a = 0` if `χ` is even, `1` if odd) but only evaluates it for the mod-1
character. Here we prove `rootNumber = 1` for the quadratic character mod an
odd prime `p`, using `GaussSign.gauss_eq` (`g = √p` if `p ≡ 1 (4)`, `i√p` if
`p ≡ 3 (4)`).

This is the textbook statement "the root number of the quadratic Dirichlet
character is `+1`", and is intended for Mathlib upstreaming alongside
`GaussSign.lean`/`GaussSignTheorem.lean`. No D-ring imports.
-/

namespace LeanDring.GaussSign

open Complex ZMod

variable {p : ℕ} [Fact p.Prime]

/-- The quadratic character mod `p` is even iff `p ≡ 1 (mod 4)`
(`χ(-1) = 1 ⟺ -1` is a square `⟺ p ≢ 3 (4)`). -/
theorem χℂ_even_iff (hp2 : p ≠ 2) :
    DirichletCharacter.Even (χℂ p) ↔ p % 4 = 1 := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp2)
  have hne : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  unfold DirichletCharacter.Even
  rw [show χℂ p (-1) = ((quadraticChar (ZMod p) (-1) : ℤ) : ℂ) from rfl]
  constructor
  · intro h
    have hq : quadraticChar (ZMod p) (-1) = 1 := by exact_mod_cast h
    have hsq : IsSquare (-1 : ZMod p) :=
      (quadraticChar_one_iff_isSquare hne).mp hq
    have := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mp hsq
    omega
  · intro h
    have hsq : IsSquare (-1 : ZMod p) :=
      (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr (by omega)
    rw [(quadraticChar_one_iff_isSquare hne).mpr hsq]
    norm_num

omit [Fact p.Prime] in
/-- `(p : ℂ)^{1/2} = √p`. -/
theorem cpow_half_eq_sqrt : (p : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt p : ℂ) := by
  rw [show (Real.sqrt p : ℂ) = (((p : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) by
      rw [← Real.sqrt_eq_rpow],
    Complex.ofReal_cpow (by positivity)]
  norm_num

theorem sqrt_p_ne_zero : (Real.sqrt p : ℂ) ≠ 0 := by
  have : (0 : ℝ) < Real.sqrt p :=
    Real.sqrt_pos.mpr (by exact_mod_cast (Fact.out : p.Prime).pos)
  exact_mod_cast this.ne'

/-- **Gauss's sign theorem, canonical form**: the root number of the quadratic
Dirichlet character mod an odd prime `p` is `1`. -/
theorem rootNumber_χℂ_eq_one (hp2 : p ≠ 2) :
    DirichletCharacter.rootNumber (χℂ p) = 1 := by
  unfold DirichletCharacter.rootNumber
  rw [show gaussSum (χℂ p) stdAddChar = gauss p from rfl, gauss_eq hp2,
    cpow_half_eq_sqrt]
  by_cases hp1 : p % 4 = 1
  · rw [if_pos hp1, if_pos ((χℂ_even_iff hp2).mpr hp1), pow_zero, div_one,
      div_self sqrt_p_ne_zero]
  · rw [if_neg hp1, if_neg (fun h => hp1 ((χℂ_even_iff hp2).mp h)), pow_one,
      div_div, div_self (mul_ne_zero Complex.I_ne_zero sqrt_p_ne_zero)]

end LeanDring.GaussSign
