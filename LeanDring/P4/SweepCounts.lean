/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P4.ARowDetect
import LeanDring.P4.Abelian
import LeanDring.P4.ModularModels
import LeanDring.P4.LastModels

/-!
# Element counts toward the full order-`p⁴` pairwise sweep

The `|Ω₂|` counts (`#{x : x^{p²} = 1}`) for the order-`p⁴` models that need one.
Each is an input to that model's order-`p²` subgroup count (`card_p2_subgroups`
and the centralizer counts of `P4ColTwoExp`), and thence to the pairwise
species-table separations.

Every model treated here has exponent `p²`, so in each case `Ω₂` is the whole
group and the count is `p⁴`; the work is the exponent law itself, proved from
the model's power formula.
-/

namespace LeanDring.P4

open Model

variable {p : ℕ} [Fact p.Prime] [Fact (Odd p)]

/-- **`|Ω₂| = p⁴` for the twin `Model p d`.**  Since `Model p d` has exponent `p²`
(`model_pow_psq`), every element satisfies `x^{p²}=1`, so `Ω₂` is the whole
group. -/
theorem card_omega2_model {d : ZMod p} (hp5 : 5 ≤ p) :
    Nat.card {x : Model p d // x ^ (p ^ 2) = 1} = p ^ 4 := by
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv (model_pow_psq hp5)), card_model]

omit [Fact (Odd p)] in
theorem a211_pow_psq (x : A211 p) : x ^ (p ^ 2) = 1 := by
  have h_pow : (p ^ 2 : ℕ) • x.toAdd = 0 := by
    rcases x.toAdd with ⟨u, v, w⟩
    ext <;> simp
  exact h_pow

omit [Fact (Odd p)] in
theorem card_omega2_a211 : Nat.card {x : A211 p // x ^ (p ^ 2) = 1} = p ^ 4 := by
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv a211_pow_psq)]
  change Nat.card (ZMod (p ^ 2) × ZMod p × ZMod p) = p ^ 4
  simp [ZMod.card]
  ring

theorem mod3_pow_psq (x : Mod3 p) : x ^ (p ^ 2) = 1 := by
  rw [Mod3.pow_formula]
  ext
  · change ((p ^ 2 : ℕ) : ZMod (p ^ 2)) * _ + liftp p (tri p ((p ^ 2 : ℕ) : ZMod p) * _) = 0
    have hp2 : ((p ^ 2 : ℕ) : ZMod (p ^ 2)) = 0 := by simp
    have hp : ((p ^ 2 : ℕ) : ZMod p) = 0 := by simp [pow_two]
    rw [hp2, hp]
    have htri : tri p (0 : ZMod p) = 0 := by unfold tri; ring
    simp [htri, liftp_zero]
  · change ((p ^ 2 : ℕ) : ZMod p) * _ = 0
    have hp : ((p ^ 2 : ℕ) : ZMod p) = 0 := by simp [pow_two]
    simp [hp]

theorem g9_pow_psq (x : G9 p) : x ^ (p ^ 2) = 1 := by
  have h1 : (x ^ (p ^ 2)).1 = 1 := mod3_pow_psq x.1
  have h2 : (x ^ (p ^ 2)).2 = 1 := by
    change x.2 ^ (p ^ 2) = 1
    rw [show p ^ 2 = p * p by ring, pow_mul, multZMod_pow_p]
  exact Prod.ext h1 h2

theorem card_omega2_g9 : Nat.card {x : G9 p // x ^ (p ^ 2) = 1} = p ^ 4 := by
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv g9_pow_psq)]
  change Nat.card (Mod3 p × Multiplicative (ZMod p)) = p ^ 4
  rw [Nat.card_prod, Mod3.card_mod3]
  have hz : Nat.card (Multiplicative (ZMod p)) = p := by
    change Nat.card (ZMod p) = p
    rw [Nat.card_eq_fintype_card, ZMod.card p]
  rw [hz]
  ring

theorem ch7_pow_psq (a : CH7 p) : a ^ (p ^ 2) = 1 := by
  rw [CH7.pow_formula]
  ext
  · change ((p ^ 2 : ℕ) : ZMod p) * _ = 0
    have hp : ((p ^ 2 : ℕ) : ZMod p) = 0 := by simp [pow_two]
    simp [hp]
  · change ((p ^ 2 : ℕ) : ZMod p) * _ = 0
    have hp : ((p ^ 2 : ℕ) : ZMod p) = 0 := by simp [pow_two]
    simp [hp]
  · change ((p ^ 2 : ℕ) : ZMod (p ^ 2)) * _ + liftp p (tri p ((p ^ 2 : ℕ) : ZMod p) * _) = 0
    have hp : ((p ^ 2 : ℕ) : ZMod p) = 0 := by simp [pow_two]
    have htri : tri p (0 : ZMod p) = 0 := by unfold tri; ring
    simp [hp, htri, liftp_zero]

theorem card_omega2_ch7 : Nat.card {x : CH7 p // x ^ (p ^ 2) = 1} = p ^ 4 := by
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv ch7_pow_psq), CH7.card_ch7 p]

theorem m8_pow_psq (x : M8 p) : x ^ (p ^ 2) = 1 := by
  rw [M8.pow_formula]
  ext
  · change ((p ^ 2 : ℕ) : ZMod (p ^ 2)) * _ + liftp p (tri p ((p ^ 2 : ℕ) : ZMod p) * _) = 0
    have hp : ((p ^ 2 : ℕ) : ZMod p) = 0 := by simp [pow_two]
    have htri : tri p (0 : ZMod p) = 0 := by unfold tri; ring
    simp [hp, htri, liftp_zero]
  · change ((p ^ 2 : ℕ) : ZMod (p ^ 2)) * _ = 0
    have _hp : ((p ^ 2 : ℕ) : ZMod (p ^ 2)) = 0 := by simp
    simp

theorem card_omega2_m8 : Nat.card {x : M8 p // x ^ (p ^ 2) = 1} = p ^ 4 := by
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv m8_pow_psq), M8.card_m8 p]

theorem gid3_pow_psq (x : Gid3 p) : x ^ (p ^ 2) = 1 := by
  rw [Gid3.pow_formula]
  ext
  · change ((p ^ 2 : ℕ) : ZMod (p ^ 2)) * _ = 0
    have hp : ((p ^ 2 : ℕ) : ZMod (p ^ 2)) = 0 := by simp
    simp
  · change ((p ^ 2 : ℕ) : ZMod p) * _ + tri p ((p ^ 2 : ℕ) : ZMod p) * _ = 0
    have hp : ((p ^ 2 : ℕ) : ZMod p) = 0 := by simp [pow_two]
    have htri : tri p (0 : ZMod p) = 0 := by unfold tri; ring
    simp [hp, htri]
  · change ((p ^ 2 : ℕ) : ZMod p) * _ = 0
    have hp : ((p ^ 2 : ℕ) : ZMod p) = 0 := by simp [pow_two]
    simp [hp]

theorem card_omega2_gid3 : Nat.card {x : Gid3 p // x ^ (p ^ 2) = 1} = p ^ 4 := by
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv gid3_pow_psq), Gid3.card_gid3 p]

theorem gid8_pow_psq (hp5 : 5 ≤ p) (g : Gid8 p) : g ^ (p ^ 2) = 1 := by
  rw [show p ^ 2 = p * p by ring, pow_mul, Gid8.pow_p hp5, Gid8.pow_p hp5]
  rw [Gid8.one_def]
  ext
  · change (0 : ZMod p) = 0; rfl
  · change (0 : ZMod p) = 0; rfl
  · change (0 : ZMod p) = 0; rfl
  · change (0 : ZMod p) = 0; rfl

theorem card_omega2_gid8 (hp5 : 5 ≤ p) : Nat.card {x : Gid8 p // x ^ (p ^ 2) = 1} = p ^ 4 := by
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv (gid8_pow_psq hp5)), Gid8.card_gid8 p]

end LeanDring.P4
