/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Müller's Lemma 2.6.1: torsion units of a split ring

The abstract engine of Müller's torsion-unit theorem (Diss. Jena 2008,
§2.6): if a commutative ring splits additively as `R = I ⊕ S` with `I` an
ideal and `S` a unital subring, then every element `u` with `uⁿ = 1`
factors **uniquely** as `u = b(1 + a)` with `b ∈ S`, `bⁿ = 1`, `a ∈ I`,
`(1 + a)ⁿ = 1` — and conversely every such product is torsion
(`LeanDring.SplitRing.exists_factorization`, `factorization_unique`,
`mul_pow_eq_one`).

Applied to the `[K,λ]`-graded decomposition of `D(G)` (top part `ℤĜ`,
lower parts the proper-subgroup ideal), this is the inductive step of
Satz 2.6.3: `UT(D(G)) = ±Ĝ · ∏(1 + graded parts)`. The grading induction
and Higman's `UT(ℤH) = ±H` remain future work.
-/

namespace LeanDring

namespace SplitRing

variable {R : Type*} [CommRing R] (I : Ideal R) (S : Subring R)

/-- Binomial absorption: `(a + b)ⁿ ≡ bⁿ mod I` for `a ∈ I`. -/
theorem add_pow_sub_pow_mem {a : R} (ha : a ∈ I) (b : R) (n : ℕ) :
    (a + b) ^ n - b ^ n ∈ I := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : (a + b) ^ (n + 1) - b ^ (n + 1) =
        (a + b) * ((a + b) ^ n - b ^ n) + a * b ^ n := by ring
    rw [hstep]
    exact I.add_mem (I.mul_mem_left _ ih) (I.mul_mem_right _ ha)

variable (hdisj : ∀ x ∈ I, x ∈ S → x = 0)

include hdisj in
/-- Uniqueness of the additive decomposition along `I ⊕ S`. -/
theorem decomp_unique {a₁ a₂ b₁ b₂ : R} (ha₁ : a₁ ∈ I) (ha₂ : a₂ ∈ I)
    (hb₁ : b₁ ∈ S) (hb₂ : b₂ ∈ S) (h : a₁ + b₁ = a₂ + b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have hI : a₁ - a₂ ∈ I := I.sub_mem ha₁ ha₂
  have hS : a₁ - a₂ ∈ S := by
    have hd : a₁ - a₂ = b₂ - b₁ := by linear_combination h
    rw [hd]
    exact S.sub_mem hb₂ hb₁
  have h0 : a₁ = a₂ := sub_eq_zero.mp (hdisj _ hI hS)
  refine ⟨h0, ?_⟩
  rw [h0] at h
  exact add_left_cancel h

include hdisj in
/-- **Müller Lemma 2.6.1, existence**: if `uⁿ = 1` then `u = b(1 + a)` with
`b ∈ S`, `bⁿ = 1`, `a ∈ I`, `(1 + a)ⁿ = 1`. -/
theorem exists_factorization
    (hspan : ∀ r : R, ∃ a ∈ I, ∃ b ∈ S, r = a + b)
    {u : R} {n : ℕ} (hn : 0 < n) (hu : u ^ n = 1) :
    ∃ b a : R, b ∈ S ∧ a ∈ I ∧ b ^ n = 1 ∧ (1 + a) ^ n = 1 ∧ u = b * (1 + a) := by
  obtain ⟨a₀, ha₀, b₀, hb₀, hdecomp⟩ := hspan u
  -- the `S`-component is itself torsion: reduce `uⁿ` mod `I`
  have hbn : b₀ ^ n = 1 := by
    have hI' : 1 - b₀ ^ n ∈ I := by
      rw [← hu, hdecomp]
      exact add_pow_sub_pow_mem I ha₀ b₀ n
    have hS' : 1 - b₀ ^ n ∈ S := S.sub_mem S.one_mem (S.pow_mem hb₀ n)
    exact (sub_eq_zero.mp (hdisj _ hI' hS')).symm
  have hbpow : b₀ ^ (n - 1) * b₀ = 1 := by
    rw [← pow_succ]
    rw [show n - 1 + 1 = n by omega]
    exact hbn
  refine ⟨b₀, b₀ ^ (n - 1) * a₀, hb₀, I.mul_mem_left _ ha₀, hbn, ?_, ?_⟩
  · -- `1 + b₀ⁿ⁻¹a₀ = b₀ⁿ⁻¹ · u`, hence its `n`-th power is `1`
    have hkey : 1 + b₀ ^ (n - 1) * a₀ = b₀ ^ (n - 1) * u := by
      rw [hdecomp]
      linear_combination -hbpow
    rw [hkey, mul_pow, hu, mul_one, ← pow_mul, mul_comm (n - 1) n, pow_mul,
      hbn, one_pow]
  · -- `b₀(1 + b₀ⁿ⁻¹a₀) = b₀ + b₀ⁿ·a₀ = b₀ + a₀ = u`
    rw [hdecomp]
    have hcancel : b₀ * (b₀ ^ (n - 1) * a₀) = a₀ := by
      rw [← mul_assoc, mul_comm b₀, hbpow, one_mul]
    rw [mul_add, mul_one, hcancel, add_comm]

include hdisj in
/-- **Müller Lemma 2.6.1, uniqueness**: the factorization `u = b(1 + a)`
with `b ∈ S` invertible and `a ∈ I` is unique. -/
theorem factorization_unique {b b' a a' : R} (hb : b ∈ S) (hb' : b' ∈ S)
    (ha : a ∈ I) (ha' : a' ∈ I) (hbu : IsUnit b)
    (h : b * (1 + a) = b' * (1 + a')) : b = b' ∧ a = a' := by
  -- compare the `S`-components: `b(1+a) = ba + b` with `ba ∈ I`
  have hd : b * a + b = b' * a' + b' := by
    have h1 : b * (1 + a) = b * a + b := by ring
    have h2 : b' * (1 + a') = b' * a' + b' := by ring
    rw [h1, h2] at h
    exact h
  obtain ⟨-, hbb⟩ := decomp_unique I S hdisj (I.mul_mem_left b ha)
    (I.mul_mem_left b' ha') hb hb' hd
  refine ⟨hbb, ?_⟩
  rw [← hbb] at h
  have := hbu.mul_right_injective h
  exact add_left_cancel this

/-- Converse: products `b(1 + a)` of torsion elements are torsion
(commutativity). -/
theorem mul_pow_eq_one {M : Type*} [CommMonoid M] {x y : M} {m n : ℕ}
    (hx : x ^ m = 1) (hy : y ^ n = 1) : (x * y) ^ (m * n) = 1 := by
  rw [mul_pow, pow_mul, hx, one_pow, one_mul, mul_comm m n, pow_mul, hy, one_pow]

end SplitRing

end LeanDring
