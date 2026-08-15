/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Group.MinimalAxioms

/-!
# The groups (xii)/(xiii) of order `p⁴`, constructed (no presentations)

The concrete model of the critical pair (xii)/(xiii), generic in
an odd prime `p` and a parameter `d : ZMod p` (`d = 1` gives (xii); `d` a
quadratic non-residue gives (xiii)). Elements are normal forms
`a^α · s^u · b^v` with `α ∈ ZMod p²`, `u, v ∈ ZMod p`, where `s = c·a^d`
and `b` generate the maximal abelian subgroup `A`, and
the defining structure is:

* `A` abelian, `s^p = a^{dp}`, `a^p` central;
* conjugation by `a` acts by `τ(s) = a^{dp}·s·b`, `τ(b) = a^p·b`
  with closed form
  `τ^k(s^u b^v) = a^{p(dku + kv + T(k)u)} s^u b^{v+ku}`, `T(k) = k(k−1)/2`.

The group law is this multiplication of normal forms. The carry of the
non-split extension (`s^{u₁}s^{u₂} = a^{dp·carry}s^{u₁+u₂}`) is the
subtraction-free telescope `carryF x y = x.val + y.val − (x+y).val ∈ {0,p}`
whose 2-cocycle identity telescopes without division; `p` odd enters only
through `2⁻¹` in `T`.
-/

namespace LeanDring

namespace P4

variable (p : ℕ) [Fact p.Prime] [Fact (Odd p)]

/-- The carry telescope `x.val + y.val − (x+y).val ∈ {0, p}`, in `ZMod p²`. -/
def carryF (x y : ZMod p) : ZMod (p ^ 2) :=
  ((x.val + y.val - (x + y).val : ℕ) : ZMod (p ^ 2))

/-- The lift `ZMod p → ZMod p²`, `x ↦ p·x`. -/
def liftp (x : ZMod p) : ZMod (p ^ 2) :=
  (p : ZMod (p ^ 2)) * (x.val : ZMod (p ^ 2))

/-- Triangular numbers `T(k) = k(k−1)/2` in `ZMod p` (`p` odd). -/
noncomputable def tri (k : ZMod p) : ZMod p := k * (k - 1) * (2 : ZMod p)⁻¹

/-- Reduction `ZMod p² →+* ZMod p`. -/
def redp : ZMod (p ^ 2) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)

/-- The τ-cocycle polynomial `P(k; u, v) = dku + kv + T(k)u`. -/
noncomputable def tauP (d : ZMod p) (k u v : ZMod p) : ZMod p :=
  d * k * u + k * v + tri p k * u

variable {p}

omit [Fact (Nat.Prime p)] in
theorem two_isUnit' : IsUnit (2 : ZMod p) := by
  have hodd : Odd p := Fact.out
  have hco : Nat.Coprime 2 p := Nat.coprime_two_left.mpr hodd
  have := (ZMod.isUnit_iff_coprime 2 p).mpr hco
  exact_mod_cast this

theorem two_ne_zero' : (2 : ZMod p) ≠ 0 := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := Fact.out
  intro h
  have h2 : (p : ℕ) ∣ 2 := by
    have h0 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    exact (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h0
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
  rw [hp2, Nat.odd_iff] at hodd
  omega

/-- `T(k+l) = T(k) + T(l) + kl`. -/
theorem tri_add (k l : ZMod p) : tri p (k + l) = tri p k + tri p l + k * l := by
  have h2 := two_ne_zero' (p := p)
  unfold tri
  have hkey : (k + l) * (k + l - 1) = k * (k - 1) + l * (l - 1) + 2 * (k * l) := by
    ring
  calc (k + l) * (k + l - 1) * (2 : ZMod p)⁻¹
      = (k * (k - 1) + l * (l - 1) + 2 * (k * l)) * (2 : ZMod p)⁻¹ := by rw [hkey]
    _ = k * (k - 1) * (2 : ZMod p)⁻¹ + l * (l - 1) * (2 : ZMod p)⁻¹ +
        (2 * (2 : ZMod p)⁻¹) * (k * l) := by ring
    _ = _ := by
        have h : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 :=
          ZMod.mul_inv_of_unit _ two_isUnit'
        linear_combination (k * l) * h

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem pow_two_cast_zero : ((p : ZMod (p ^ 2))) * (p : ZMod (p ^ 2)) = 0 := by
  have : (((p ^ 2 : ℕ)) : ZMod (p ^ 2)) = 0 := ZMod.natCast_self _
  push_cast at this
  linear_combination this

omit [Fact (Odd p)] in
/-- Value facts for the carry. -/
theorem carry_val (x y : ZMod p) :
    (x + y).val ≤ x.val + y.val ∧
      (x.val + y.val - (x + y).val = 0 ∨ x.val + y.val - (x + y).val = p) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hx := ZMod.val_lt x
  have hy := ZMod.val_lt y
  have hadd := ZMod.val_add x y
  rcases Nat.lt_or_ge (x.val + y.val) p with h | h
  · rw [hadd, Nat.mod_eq_of_lt h]
    omega
  · have hlt : x.val + y.val - p < p := by omega
    have hmod : (x.val + y.val) % p = x.val + y.val - p := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt hlt]
    rw [hadd, hmod]
    omega

omit [Fact (Odd p)] in
/-- **The carry 2-cocycle identity** (pure telescope, no division). -/
theorem carryF_cocycle (x y z : ZMod p) :
    carryF p y z + carryF p x (y + z) = carryF p x y + carryF p (x + y) z := by
  unfold carryF
  rw [← Nat.cast_add, ← Nat.cast_add]
  congr 1
  have h1 := carry_val x y
  have h2 := carry_val y z
  have h3 := carry_val (x + y) z
  have h4 := carry_val x (y + z)
  have hassoc : (x + y + z).val = (x + (y + z)).val := by rw [add_assoc]
  omega

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem carryF_comm (x y : ZMod p) : carryF p x y = carryF p y x := by
  unfold carryF
  rw [Nat.add_comm x.val, add_comm x y]

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
@[simp] theorem carryF_zero (x : ZMod p) : carryF p x 0 = 0 := by
  unfold carryF
  simp

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
@[simp] theorem carryF_zero' (x : ZMod p) : carryF p 0 x = 0 := by
  rw [carryF_comm, carryF_zero]

omit [Fact (Odd p)] in
/-- `liftp` is additive (the discrepancy is `p·p ≡ 0`). -/
theorem liftp_add (x y : ZMod p) : liftp p (x + y) = liftp p x + liftp p y := by
  unfold liftp
  obtain ⟨hle, h0 | hp'⟩ := carry_val x y
  · have hval : (x + y).val = x.val + y.val := by omega
    rw [hval]
    push_cast
    ring
  · have hval : (x + y).val = x.val + y.val - p := by omega
    have hple : p ≤ x.val + y.val := by omega
    rw [hval, Nat.cast_sub hple]
    push_cast
    linear_combination -(pow_two_cast_zero (p := p))

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
@[simp] theorem liftp_zero : liftp p 0 = 0 := by
  unfold liftp
  simp

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
/-- `redp` kills lifts. -/
@[simp] theorem redp_liftp (x : ZMod p) : redp p (liftp p x) = 0 := by
  unfold liftp
  rw [map_mul]
  have : redp p (p : ZMod (p ^ 2)) = 0 := by
    have : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self _
    simp [redp]
  rw [this, zero_mul]

omit [Fact (Odd p)] in
/-- `redp` kills carries. -/
@[simp] theorem redp_carryF (x y : ZMod p) : redp p (carryF p x y) = 0 := by
  obtain ⟨-, h0 | hp'⟩ := carry_val x y
  · unfold carryF
    rw [h0]
    simp
  · unfold carryF
    rw [hp']
    have : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self _
    simp [redp]

/-! ## The group -/

variable (p) in
/-- The model of the order-`p⁴` group with parameter `d`: normal forms
`a^α s^u b^v`. -/
@[ext]
structure Model (d : ZMod p) where
  /-- exponent of `a` -/
  α : ZMod (p ^ 2)
  /-- exponent of `s = c·a^d` -/
  u : ZMod p
  /-- exponent of `b` -/
  v : ZMod p

namespace Model

variable {d : ZMod p}

/-- The image of `d` in `ZMod p²` (via `val`; used only against `p`-torsion
elements, where the choice of lift is irrelevant). -/
def dc (d : ZMod p) : ZMod (p ^ 2) := (d.val : ZMod (p ^ 2))

noncomputable instance : Mul (Model p d) where
  mul x y :=
    ⟨x.α + y.α + liftp p (tauP p d (redp p y.α) x.u x.v) + dc d * carryF p x.u y.u,
      x.u + y.u,
      x.v + y.v + redp p y.α * x.u⟩

noncomputable instance : One (Model p d) where
  one := ⟨0, 0, 0⟩

noncomputable instance : Inv (Model p d) where
  inv x :=
    ⟨-x.α - liftp p (tauP p d (redp p x.α) (-x.u) (redp p x.α * x.u - x.v)) -
        dc d * carryF p (-x.u) x.u,
      -x.u,
      redp p x.α * x.u - x.v⟩

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem mul_def (x y : Model p d) :
    x * y = ⟨x.α + y.α + liftp p (tauP p d (redp p y.α) x.u x.v) +
        dc d * carryF p x.u y.u,
      x.u + y.u, x.v + y.v + redp p y.α * x.u⟩ := rfl

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem one_def : (1 : Model p d) = ⟨0, 0, 0⟩ := rfl

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
/-- `P(0; u, v) = 0` and `P(k; 0, 0) = 0`. -/
theorem tauP_zero_left (u v : ZMod p) : tauP p d 0 u v = 0 := by
  unfold tauP tri
  ring

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem tauP_zero_right (k : ZMod p) : tauP p d k 0 0 = 0 := by
  unfold tauP
  ring

/-- **The τ-cocycle identity**: the `ZMod p` heart of associativity. -/
theorem tauP_assoc (k₂ k₃ u₁ u₂ v₁ v₂ : ZMod p) :
    tauP p d k₂ u₁ v₁ + tauP p d k₃ (u₁ + u₂) (v₁ + v₂ + k₂ * u₁) =
      tauP p d k₃ u₂ v₂ + tauP p d (k₂ + k₃) u₁ v₁ := by
  unfold tauP
  rw [tri_add]
  ring

noncomputable instance : Group (Model p d) :=
  Group.ofLeftAxioms
    (by
      -- associativity
      intro x y z
      rw [mul_def, mul_def, mul_def, mul_def]
      have hred : redp p (y.α + z.α + liftp p (tauP p d (redp p z.α) y.u y.v) +
          dc d * carryF p y.u z.u) = redp p y.α + redp p z.α := by
        rw [map_add, map_add, map_add, redp_liftp, map_mul, redp_carryF,
          mul_zero, add_zero, add_zero]
      ext
      · -- α-component
        change x.α + y.α + liftp p (tauP p d (redp p y.α) x.u x.v) +
            dc d * carryF p x.u y.u + z.α +
            liftp p (tauP p d (redp p z.α) (x.u + y.u)
              (x.v + y.v + redp p y.α * x.u)) +
            dc d * carryF p (x.u + y.u) z.u =
          x.α + (y.α + z.α + liftp p (tauP p d (redp p z.α) y.u y.v) +
            dc d * carryF p y.u z.u) +
            liftp p (tauP p d (redp p (y.α + z.α +
              liftp p (tauP p d (redp p z.α) y.u y.v) +
              dc d * carryF p y.u z.u)) x.u x.v) +
            dc d * carryF p x.u (y.u + z.u)
        rw [hred]
        have hP := tauP_assoc (d := d) (redp p y.α) (redp p z.α) x.u y.u x.v y.v
        have hC := carryF_cocycle x.u y.u z.u
        have hL : liftp p (tauP p d (redp p y.α) x.u x.v) +
            liftp p (tauP p d (redp p z.α) (x.u + y.u)
              (x.v + y.v + redp p y.α * x.u)) =
            liftp p (tauP p d (redp p z.α) y.u y.v) +
            liftp p (tauP p d (redp p y.α + redp p z.α) x.u x.v) := by
          rw [← liftp_add, ← liftp_add, hP]
        linear_combination hL - dc d * hC
      · -- u-component
        change x.u + y.u + z.u = x.u + (y.u + z.u)
        ring
      · -- v-component
        change x.v + y.v + redp p y.α * x.u + z.v + redp p z.α * (x.u + y.u) =
          x.v + (y.v + z.v + redp p z.α * y.u) +
            redp p (y.α + z.α + liftp p (tauP p d (redp p z.α) y.u y.v) +
              dc d * carryF p y.u z.u) * x.u
        rw [hred]
        ring)
    (by
      -- 1 * a = a
      intro x
      rw [one_def, mul_def]
      ext
      · change 0 + x.α + liftp p (tauP p d (redp p x.α) 0 0) +
            dc d * carryF p 0 x.u = x.α
        rw [tauP_zero_right, liftp_zero, carryF_zero']
        ring
      · change 0 + x.u = x.u
        ring
      · change 0 + x.v + redp p x.α * 0 = x.v
        ring)
    (by
      -- a⁻¹ * a = 1
      intro x
      change (⟨_, _, _⟩ : Model p d) * x = 1
      rw [mul_def, one_def]
      ext
      · change -x.α - liftp p (tauP p d (redp p x.α) (-x.u)
              (redp p x.α * x.u - x.v)) -
            dc d * carryF p (-x.u) x.u + x.α +
            liftp p (tauP p d (redp p x.α) (-x.u) (redp p x.α * x.u - x.v)) +
            dc d * carryF p (-x.u) x.u = 0
        ring
      · change -x.u + x.u = 0
        ring
      · change redp p x.α * x.u - x.v + x.v + redp p x.α * (-x.u) = 0
        ring)

/-- The model as a plain product (for counting). -/
def toProd : Model p d ≃ ZMod (p ^ 2) × ZMod p × ZMod p where
  toFun x := (x.α, x.u, x.v)
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Finite (Model p d) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  exact Finite.of_equiv _ toProd.symm

omit [Fact (Odd p)] in
/-- **The model has order `p⁴`.** -/
theorem card_model : Nat.card (Model p d) = p ^ 4 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  rw [Nat.card_congr toProd, Nat.card_prod, Nat.card_prod,
    Nat.card_zmod, Nat.card_zmod]
  ring

end Model

end P4

end LeanDring
