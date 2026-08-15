/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The arithmetic endgame of the `p⁴` twin separation

The separation of the order-`p⁴` groups (xii)/(xiii) bottoms out in the
unsolvability of the value equation: no species entry
`√p · ζ₈ₚ^{p-(1+2β)²} · ζ_{p²}^{1+mp}` of `G₁` can equal the
distinguished entry `(-1)^{(p²+7)/8} c(p) √p · ζ₈ₚ^{-d⁻¹(p+1)³} · ζ_{p²}`
of `G₂`. After cancelling `√p ζ_{p²}`, this is a root-of-unity
identity in `ζ₈ₚ`, refuted **mod 8**: the left exponent is `≡ p − 1`, the
right side contributes `ε(p) = ζ₈ₚ^{4p}, ζ₈ₚ^{2p}, 1, ζ₈ₚ^{6p}` according
to `p mod 8`, and `p − 1 ≢ 4p, 2p, 0, 6p (mod 8)` in the respective cases.

`value_equation_impossible` formalizes exactly this: for every odd prime `p`,
all `m β : ℕ` and every `d' : ℤ` (covering `d⁻¹`),
`ζ₈ₚ^{p-(1+2β)²+8m} ≠ (-1)^{(p²+7)/8} c(p) · ζ₈ₚ^{-d'(p+1)³}`
with `ζ₈ₚ = exp(2πi/8p)` and `c(p) = 1` or `i` for `p ≡ 1, 3 (mod 4)`.

This file is pure `ζ₈ₚ` arithmetic and imports nothing from the group models.
The species-side inputs that produce the two entry values — the models
(xii)/(xiii) with their orbit and species analysis, and the exact quadratic
Gauss sum value — are supplied by `LeanDring.P4.TwinSeparation` and
`LeanDring.Theory.Gauss.GaussSignTheorem`.
-/

namespace LeanDring

namespace P4

open Complex

/-- `(1+2β)² ≡ 1 (mod 8)`. -/
theorem odd_sq_mod_eight (β : ℤ) : ∃ s : ℤ, (1 + 2 * β) ^ 2 = 8 * s + 1 := by
  obtain ⟨s, hs⟩ := Int.even_mul_succ_self β
  exact ⟨s, by linear_combination 4 * hs⟩

/-- For odd `p`, `8 ∣ (p+1)³`. -/
theorem eight_dvd_succ_cube {p : ℕ} (hodd : Odd p) :
    ∃ w : ℤ, ((p : ℤ) + 1) ^ 3 = 8 * w := by
  obtain ⟨w, hw⟩ := hodd
  exact ⟨((w : ℤ) + 1) ^ 3, by push_cast [hw]; ring⟩

/-- **The endgame of the twin separation**: the value equation has no
solution. For an odd prime `p`, with `ζ = exp(2πi/8p)`, there are no
`m, β : ℕ`, `d' : ℤ` with
`ζ^{p-(1+2β)²+8m} = (-1)^{(p²+7)/8} · c(p) · ζ^{-d'(p+1)³}`. -/
theorem value_equation_impossible (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (m β : ℕ) (d' : ℤ) :
    Complex.exp (2 * Real.pi * I / ((8 * p : ℕ) : ℂ)) ^
        ((p : ℤ) - (1 + 2 * (β : ℤ)) ^ 2 + 8 * (m : ℤ)) ≠
      (-1 : ℂ) ^ ((p ^ 2 + 7) / 8) * (if p % 4 = 1 then (1 : ℂ) else I) *
        Complex.exp (2 * Real.pi * I / ((8 * p : ℕ) : ℂ)) ^
          (-(d' * ((p : ℤ) + 1) ^ 3)) := by
  intro heq
  set ζ : ℂ := Complex.exp (2 * Real.pi * I / ((8 * p : ℕ) : ℂ)) with hζdef
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hz : ζ ≠ 0 := Complex.exp_ne_zero _
  have hζ : IsPrimitiveRoot ζ (8 * p) :=
    Complex.isPrimitiveRoot_exp (8 * p) (Nat.mul_ne_zero (by norm_num) hp.ne_zero)
  -- the two special values `ζ^{4p} = -1`, `ζ^{2p} = i`
  have h4p : ζ ^ (4 * (p : ℤ)) = -1 := by
    rw [show 4 * (p : ℤ) = ((4 * p : ℕ) : ℤ) by push_cast; ring, hζdef,
      zpow_natCast, ← Complex.exp_nat_mul]
    rw [show ((4 * p : ℕ) : ℂ) * (2 * Real.pi * I / ((8 * p : ℕ) : ℂ)) =
      (Real.pi : ℂ) * I by push_cast; field_simp; ring]
    exact Complex.exp_pi_mul_I
  have h2p : ζ ^ (2 * (p : ℤ)) = I := by
    rw [show 2 * (p : ℤ) = ((2 * p : ℕ) : ℤ) by push_cast; ring, hζdef,
      zpow_natCast, ← Complex.exp_nat_mul]
    rw [show ((2 * p : ℕ) : ℂ) * (2 * Real.pi * I / ((8 * p : ℕ) : ℂ)) =
      (Real.pi : ℂ) / 2 * I by push_cast; field_simp; ring]
    exact Complex.exp_pi_div_two_mul_I
  -- uniform final step: an equality of `ζ`-powers forces a mod-8 congruence
  have key : ∀ E : ℤ,
      ζ ^ ((p : ℤ) - (1 + 2 * (β : ℤ)) ^ 2 + 8 * (m : ℤ)) =
        ζ ^ E * ζ ^ (-(d' * ((p : ℤ) + 1) ^ 3)) →
      (8 : ℤ) ∣ ((p : ℤ) - (1 + 2 * (β : ℤ)) ^ 2 + 8 * (m : ℤ) -
        (E + -(d' * ((p : ℤ) + 1) ^ 3))) := by
    intro E hE
    rw [← zpow_add₀ hz] at hE
    have hone : ζ ^ ((p : ℤ) - (1 + 2 * (β : ℤ)) ^ 2 + 8 * (m : ℤ) -
        (E + -(d' * ((p : ℤ) + 1) ^ 3))) = 1 := by
      rw [zpow_sub₀ hz, hE, div_self (zpow_ne_zero _ hz)]
    have hdvd := (hζ.zpow_eq_one_iff_dvd _).mp hone
    exact dvd_trans ⟨(p : ℤ), by push_cast; ring⟩ hdvd
  -- arithmetic facts
  obtain ⟨s, hs⟩ := odd_sq_mod_eight (β : ℤ)
  obtain ⟨w, hw⟩ := eight_dvd_succ_cube hodd
  have hpmod2 : p % 2 = 1 := Nat.odd_iff.mp hodd
  have hr : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  rcases hr with hr | hr | hr | hr
  · -- `p ≡ 1 (mod 8)`: `ε = -1 = ζ^{4p}`, and `p - 1 ≢ 4p (mod 8)`
    obtain ⟨k, hk⟩ : ∃ k, p = 8 * k + 1 := ⟨p / 8, by omega⟩
    have hdiv : (p ^ 2 + 7) / 8 = 8 * k ^ 2 + 2 * k + 1 := by
      have h8 : p ^ 2 + 7 = 8 * (8 * k ^ 2 + 2 * k + 1) := by subst hk; ring
      omega
    have hodd' : Odd ((p ^ 2 + 7) / 8) := by
      rw [hdiv, Nat.odd_iff]; omega
    have hif : (if p % 4 = 1 then (1 : ℂ) else I) = 1 := if_pos (by omega)
    rw [hodd'.neg_one_pow, hif, mul_one,
      show (-1 : ℂ) = ζ ^ (4 * (p : ℤ)) from h4p.symm] at heq
    obtain ⟨q, hq⟩ := key _ heq
    rw [hs, hw] at hq
    have hq2 : (p : ℤ) - (8 * s + 1) + 8 * (m : ℤ) - 4 * (p : ℤ) +
        8 * (d' * w) = 8 * q := by linear_combination hq
    generalize d' * w = W at hq2
    have hp' : (p : ℤ) = 8 * (k : ℤ) + 1 := by exact_mod_cast hk
    rw [hp'] at hq2
    omega
  · -- `p ≡ 3 (mod 8)`: `ε = i = ζ^{2p}`, and `p - 1 ≢ 2p (mod 8)`
    obtain ⟨k, hk⟩ : ∃ k, p = 8 * k + 3 := ⟨p / 8, by omega⟩
    have hdiv : (p ^ 2 + 7) / 8 = 8 * k ^ 2 + 6 * k + 2 := by
      have h8 : p ^ 2 + 7 = 8 * (8 * k ^ 2 + 6 * k + 2) := by subst hk; ring
      omega
    have heven : Even ((p ^ 2 + 7) / 8) := by
      rw [hdiv, Nat.even_iff]; omega
    have hif : (if p % 4 = 1 then (1 : ℂ) else I) = I := if_neg (by omega)
    rw [heven.neg_one_pow, hif, one_mul,
      show (I : ℂ) = ζ ^ (2 * (p : ℤ)) from h2p.symm] at heq
    obtain ⟨q, hq⟩ := key _ heq
    rw [hs, hw] at hq
    have hq2 : (p : ℤ) - (8 * s + 1) + 8 * (m : ℤ) - 2 * (p : ℤ) +
        8 * (d' * w) = 8 * q := by linear_combination hq
    generalize d' * w = W at hq2
    have hp' : (p : ℤ) = 8 * (k : ℤ) + 3 := by exact_mod_cast hk
    rw [hp'] at hq2
    omega
  · -- `p ≡ 5 (mod 8)`: `ε = 1 = ζ^0`, and `p - 1 ≢ 0 (mod 8)`
    obtain ⟨k, hk⟩ : ∃ k, p = 8 * k + 5 := ⟨p / 8, by omega⟩
    have hdiv : (p ^ 2 + 7) / 8 = 8 * k ^ 2 + 10 * k + 4 := by
      have h8 : p ^ 2 + 7 = 8 * (8 * k ^ 2 + 10 * k + 4) := by subst hk; ring
      omega
    have heven : Even ((p ^ 2 + 7) / 8) := by
      rw [hdiv, Nat.even_iff]; omega
    have hif : (if p % 4 = 1 then (1 : ℂ) else I) = 1 := if_pos (by omega)
    rw [heven.neg_one_pow, hif, mul_one,
      show (1 : ℂ) = ζ ^ (0 : ℤ) from (zpow_zero ζ).symm] at heq
    obtain ⟨q, hq⟩ := key _ heq
    rw [hs, hw] at hq
    have hq2 : (p : ℤ) - (8 * s + 1) + 8 * (m : ℤ) + 8 * (d' * w) = 8 * q := by
      linear_combination hq
    generalize d' * w = W at hq2
    have hp' : (p : ℤ) = 8 * (k : ℤ) + 5 := by exact_mod_cast hk
    rw [hp'] at hq2
    omega
  · -- `p ≡ 7 (mod 8)`: `ε = -i = ζ^{6p}`, and `p - 1 ≢ 6p (mod 8)`
    obtain ⟨k, hk⟩ : ∃ k, p = 8 * k + 7 := ⟨p / 8, by omega⟩
    have hdiv : (p ^ 2 + 7) / 8 = 8 * k ^ 2 + 14 * k + 7 := by
      have h8 : p ^ 2 + 7 = 8 * (8 * k ^ 2 + 14 * k + 7) := by subst hk; ring
      omega
    have hodd' : Odd ((p ^ 2 + 7) / 8) := by
      rw [hdiv, Nat.odd_iff]; omega
    have hif : (if p % 4 = 1 then (1 : ℂ) else I) = I := if_neg (by omega)
    have hmi : (-1 : ℂ) * I = ζ ^ (6 * (p : ℤ)) := by
      rw [show 6 * (p : ℤ) = 4 * (p : ℤ) + 2 * (p : ℤ) by ring,
        zpow_add₀ hz, h4p, h2p]
    rw [hodd'.neg_one_pow, hif, hmi] at heq
    obtain ⟨q, hq⟩ := key _ heq
    rw [hs, hw] at hq
    have hq2 : (p : ℤ) - (8 * s + 1) + 8 * (m : ℤ) - 6 * (p : ℤ) +
        8 * (d' * w) = 8 * q := by linear_combination hq
    generalize d' * w = W at hq2
    have hp' : (p : ℤ) = 8 * (k : ℤ) + 7 := by exact_mod_cast hk
    rw [hp'] at hq2
    omega

end P4

end LeanDring
