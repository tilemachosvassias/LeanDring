/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P4.ModelPow
import Mathlib.Algebra.BigOperators.Pi

/-!
# The exponent-`p` groups of order `p⁴`: models for (xiv) and (xv)

The two nonabelian groups of order `p⁴` and exponent `p` (for `p ≥ 5`):

* **(xiv)** `= Heis p × C_p` — the Heisenberg group `UT(3,p)` times `C_p`
  (SmallGroup `(p⁴, 12)`);
* **(xv)** `= MaxClass p = (C_p)³ ⋊ C_p` — the maximal-class exponent-`p`
  group, with the generator acting by a regular unipotent Jordan block
  (SmallGroup `(p⁴, 7)`).

Both are built with the `tri` machinery of `P4Model` — no carries needed.
Main results (sorry-free):

* group instances, `card = p³` / `p⁴`, closed power formulas;
* `Heis.pow_p` / `MaxClass.pow_p` : `gᵖ = 1` (`p ≥ 5` for (xv), via
  `T(jw) = w²T(j) + T(w)j` and `∑T ≡ 0`);
* `card_order_p_subgroups_of_exponent` (generic): an order-`p⁴` group of
  exponent `p` has exactly `p³ + p² + p + 1` subgroups of order `p`;
* the **(xiv)/(xv) table rows** `#{|H| = p} = p³ + p² + p + 1`, proven
  from the presentations.
-/

namespace LeanDring

namespace P4

open Finset Model

variable {p : ℕ} [Fact p.Prime] [Fact (Odd p)]

/-! ## Generic: subgroup count from exponent `p` -/

/-- An order-`p⁴` group of exponent `p` has `p³ + p² + p + 1` subgroups of
order `p`. -/
theorem card_order_p_subgroups_of_exponent (G : Type*) [Group G]
    [Finite G] (hcard : Nat.card G = p ^ 4) (hexp : ∀ g : G, g ^ p = 1) :
    Nat.card {H : Subgroup G // Nat.card H = p} = p ^ 3 + p ^ 2 + p + 1 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hp : p.Prime := Fact.out
  -- every non-identity element has order exactly `p`
  have hS2 : (univ.filter fun g : G => orderOf g = p) = univ.erase 1 := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true]
    constructor
    · intro ho h1
      rw [h1, orderOf_one] at ho
      have := hp.one_lt
      omega
    · intro h1
      have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (hexp g)
      rcases (Nat.dvd_prime hp).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) h1
      · exact h
  have hS2card : (univ.filter fun g : G => orderOf g = p).card =
      p ^ 4 - 1 := by
    rw [hS2, Finset.card_erase_of_mem (Finset.mem_univ 1),
      Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
  have hdouble := card_orderOf_eq_prime (G := G) hp
  rw [hS2card] at hdouble
  have hp1 := hp.one_lt
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have h4 : (q + 1) ^ 4 = q ^ 4 + 4 * q ^ 3 + 6 * q ^ 2 + 4 * q + 1 := by
    ring
  have hfact : (q + 1) ^ 4 - 1 =
      ((q + 1) ^ 3 + (q + 1) ^ 2 + (q + 1) + 1) * q := by
    have h3 : (q + 1) ^ 3 = q ^ 3 + 3 * q ^ 2 + 3 * q + 1 := by ring
    have h2 : (q + 1) ^ 2 = q ^ 2 + 2 * q + 1 := by ring
    have hexp2 : ((q + 1) ^ 3 + (q + 1) ^ 2 + (q + 1) + 1) * q =
        (q ^ 3 + 3 * q ^ 2 + 3 * q + 1 + (q ^ 2 + 2 * q + 1) + (q + 1) + 1)
          * q := by rw [h3, h2]
    have hexp3 : (q ^ 3 + 3 * q ^ 2 + 3 * q + 1 + (q ^ 2 + 2 * q + 1) +
        (q + 1) + 1) * q = q ^ 4 + 4 * q ^ 3 + 6 * q ^ 2 + 4 * q := by
      ring
    omega
  have hq1 : q + 1 - 1 = q := by omega
  rw [hfact, hq1] at hdouble
  have hqpos : 0 < q := by
    have := hp.one_lt
    omega
  have hN := Nat.eq_of_mul_eq_mul_right hqpos hdouble.symm
  omega

/-! ## The Heisenberg group `UT(3, p)` -/

variable (p) in
/-- The Heisenberg group: normal forms `(x, y, z)` with
`(x,y,z)·(x',y',z') = (x+x', y+y', z+z'+xy')`. -/
@[ext]
structure Heis where
  x : ZMod p
  y : ZMod p
  z : ZMod p

namespace Heis

instance : Mul (Heis p) :=
  ⟨fun a b => ⟨a.x + b.x, a.y + b.y, a.z + b.z + a.x * b.y⟩⟩

instance : One (Heis p) := ⟨⟨0, 0, 0⟩⟩

instance : Inv (Heis p) := ⟨fun a => ⟨-a.x, -a.y, -a.z + a.x * a.y⟩⟩

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem mul_def (a b : Heis p) :
    a * b = ⟨a.x + b.x, a.y + b.y, a.z + b.z + a.x * b.y⟩ := rfl

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem one_def : (1 : Heis p) = ⟨0, 0, 0⟩ := rfl

instance : Group (Heis p) :=
  Group.ofLeftAxioms
    (fun a b c => by
      simp only [mul_def]
      ext <;> ring)
    (fun a => by
      simp only [mul_def, one_def]
      ext <;> ring)
    (fun a => by
      change (⟨-a.x, -a.y, -a.z + a.x * a.y⟩ : Heis p) * a = 1
      simp only [mul_def, one_def]
      ext <;> ring)

variable (p) in
/-- `Heis p ≃ (ZMod p)³` as a type. -/
def toProd : Heis p ≃ ZMod p × ZMod p × ZMod p where
  toFun a := (a.x, a.y, a.z)
  invFun w := ⟨w.1, w.2.1, w.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable (p) in
omit [Fact (Odd p)] in
theorem card_heis : Nat.card (Heis p) = p ^ 3 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [Nat.card_congr (toProd p), Nat.card_prod, Nat.card_prod,
    Nat.card_zmod]
  ring

/-- Powers: `(x,y,z)ⁿ = (nx, ny, nz + T(n)xy)`. -/
theorem pow_formula (a : Heis p) (n : ℕ) :
    a ^ n = ⟨(n : ZMod p) * a.x, (n : ZMod p) * a.y,
      (n : ZMod p) * a.z + tri p ((n : ZMod p)) * a.x * a.y⟩ := by
  induction n with
  | zero =>
    change (1 : Heis p) = _
    rw [one_def]
    have htri : tri p ((0 : ℕ) : ZMod p) = 0 := by
      unfold tri
      push_cast
      ring
    ext
    · change (0 : ZMod p) = ((0 : ℕ) : ZMod p) * a.x
      push_cast
      ring
    · change (0 : ZMod p) = ((0 : ℕ) : ZMod p) * a.y
      push_cast
      ring
    · change (0 : ZMod p) = ((0 : ℕ) : ZMod p) * a.z +
        tri p ((0 : ℕ) : ZMod p) * a.x * a.y
      rw [htri]
      push_cast
      ring
  | succ n ih =>
    rw [pow_succ, ih, mul_def]
    have htri : tri p ((n + 1 : ℕ) : ZMod p) =
        tri p ((n : ZMod p)) + (n : ZMod p) := by
      push_cast
      rw [tri_add]
      have h1 : tri p (1 : ZMod p) = 0 := by
        unfold tri
        ring
      rw [h1]
      ring
    ext
    · change (n : ZMod p) * a.x + a.x = ((n + 1 : ℕ) : ZMod p) * a.x
      push_cast
      ring
    · change (n : ZMod p) * a.y + a.y = ((n + 1 : ℕ) : ZMod p) * a.y
      push_cast
      ring
    · change (n : ZMod p) * a.z + tri p ((n : ZMod p)) * a.x * a.y + a.z +
          (n : ZMod p) * a.x * a.y =
        ((n + 1 : ℕ) : ZMod p) * a.z +
          tri p ((n + 1 : ℕ) : ZMod p) * a.x * a.y
      rw [htri]
      push_cast
      ring

/-- `Heis p` has exponent `p`. -/
theorem pow_p (a : Heis p) : a ^ p = 1 := by
  rw [pow_formula, one_def]
  have hp0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  have htri : tri p (0 : ZMod p) = 0 := by
    unfold tri
    ring
  ext
  · change ((p : ℕ) : ZMod p) * a.x = 0
    rw [hp0, zero_mul]
  · change ((p : ℕ) : ZMod p) * a.y = 0
    rw [hp0, zero_mul]
  · change ((p : ℕ) : ZMod p) * a.z + tri p ((p : ℕ) : ZMod p) * a.x * a.y = 0
    rw [hp0, htri]
    ring

end Heis

/-! ## Group (xiv): `Heis p × C_p` -/

variable (p) in
/-- **Group (xiv)** `= UT(3,p) × C_p` (SmallGroup `(p⁴, 12)`). -/
abbrev G14 := Heis p × Multiplicative (ZMod p)

instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

noncomputable instance : Fintype (Heis p) := Fintype.ofEquiv _ (Heis.toProd p).symm

variable (p) in
omit [Fact (Odd p)] in
theorem card_g14 : Nat.card (G14 p) = p ^ 4 := by
  rw [Nat.card_prod, Heis.card_heis]
  have h1 : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  rw [h1]
  ring

theorem g14_pow_p (g : G14 p) : g ^ p = 1 := by
  refine Prod.ext ?_ ?_
  · exact Heis.pow_p g.1
  · change g.2 ^ p = 1
    have h2 : p • g.2.toAdd = (0 : ZMod p) := by
      rw [nsmul_eq_mul]
      have h0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
      rw [h0, zero_mul]
    calc g.2 ^ p = (Multiplicative.ofAdd g.2.toAdd) ^ p := rfl
      _ = Multiplicative.ofAdd (p • g.2.toAdd) := by rw [← ofAdd_nsmul]
      _ = 1 := by rw [h2]; rfl

variable (p) in
/-- **Table row (xiv), first column**: `Heis p × C_p` has exactly
`p³ + p² + p + 1` subgroups of order `p`. -/
theorem card_order_p_subgroups_g14 :
    Nat.card {H : Subgroup (G14 p) // Nat.card H = p} =
      p ^ 3 + p ^ 2 + p + 1 :=
  card_order_p_subgroups_of_exponent _ (card_g14 p) g14_pow_p

/-! ## Group (xv): the maximal-class exponent-`p` group `(C_p)³ ⋊ C_p` -/

variable (p) in
/-- The unipotent action `σᵏ(t, u, v) = (t, u + kt, v + ku + T(k)t)`
(regular Jordan block, exponentiated). -/
noncomputable def actMC (k : ZMod p) (a : ZMod p × ZMod p × ZMod p) :
    ZMod p × ZMod p × ZMod p :=
  (a.1, a.2.1 + k * a.1, a.2.2 + k * a.2.1 + tri p k * a.1)

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem actMC_zero (a : ZMod p × ZMod p × ZMod p) : actMC p 0 a = a := by
  unfold actMC
  have htri : tri p (0 : ZMod p) = 0 := by
    unfold tri
    ring
  rw [htri]
  ext <;> simp

theorem actMC_add (k l : ZMod p) (a : ZMod p × ZMod p × ZMod p) :
    actMC p (k + l) a = actMC p k (actMC p l a) := by
  unfold actMC
  rw [tri_add]
  ext
  · rfl
  · change a.2.1 + (k + l) * a.1 = a.2.1 + l * a.1 + k * a.1
    ring
  · change a.2.2 + (k + l) * a.2.1 + (tri p k + tri p l + k * l) * a.1 =
      a.2.2 + l * a.2.1 + tri p l * a.1 + k * (a.2.1 + l * a.1) +
        tri p k * a.1
    ring

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem actMC_addv (k : ZMod p) (a b : ZMod p × ZMod p × ZMod p) :
    actMC p k (a + b) = actMC p k a + actMC p k b := by
  unfold actMC
  ext
  · rfl
  · change a.2.1 + b.2.1 + k * (a.1 + b.1) =
      a.2.1 + k * a.1 + (b.2.1 + k * b.1)
    ring
  · change a.2.2 + b.2.2 + k * (a.2.1 + b.2.1) + tri p k * (a.1 + b.1) =
      a.2.2 + k * a.2.1 + tri p k * a.1 + (b.2.2 + k * b.2.1 + tri p k * b.1)
    ring

variable (p) in
/-- **Group (xv)**: normal forms `(a, w)` with
`(a, w)·(a', w') = (a + σʷ(a'), w + w')` (SmallGroup `(p⁴, 7)`). -/
@[ext]
structure MaxClass where
  vec : ZMod p × ZMod p × ZMod p
  w : ZMod p

namespace MaxClass

noncomputable instance : Mul (MaxClass p) :=
  ⟨fun g h => ⟨g.vec + actMC p g.w h.vec, g.w + h.w⟩⟩

instance : One (MaxClass p) := ⟨⟨0, 0⟩⟩

noncomputable instance : Inv (MaxClass p) :=
  ⟨fun g => ⟨-(actMC p (-g.w) g.vec), -g.w⟩⟩

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem mul_def (g h : MaxClass p) :
    g * h = ⟨g.vec + actMC p g.w h.vec, g.w + h.w⟩ := rfl

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem one_def : (1 : MaxClass p) = ⟨0, 0⟩ := rfl

theorem actMC_neg_cancel (k : ZMod p) (a : ZMod p × ZMod p × ZMod p) :
    actMC p k (actMC p (-k) a) = a := by
  rw [← actMC_add, add_neg_cancel, actMC_zero]

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem actMC_zero_vec (k : ZMod p) : actMC p k (0 : ZMod p × ZMod p × ZMod p) = 0 := by
  unfold actMC
  ext <;> simp

noncomputable instance : Group (MaxClass p) :=
  Group.ofLeftAxioms
    (fun g h k => by
      simp only [mul_def]
      ext
      · change (g.vec + actMC p g.w h.vec).1 + _ = _
        rw [actMC_add, actMC_addv]
        change g.vec.1 + (actMC p g.w h.vec).1 +
            (actMC p g.w (actMC p h.w k.vec)).1 = _
        change _ = g.vec.1 + ((actMC p g.w h.vec) +
          (actMC p g.w (actMC p h.w k.vec))).1
        rw [Prod.fst_add]
        ring
      · rw [actMC_add, actMC_addv]
        change (g.vec + actMC p g.w h.vec).2.1 +
            (actMC p g.w (actMC p h.w k.vec)).2.1 = _
        change _ = g.vec.2.1 + ((actMC p g.w h.vec) +
          (actMC p g.w (actMC p h.w k.vec))).2.1
        simp only [Prod.snd_add, Prod.fst_add]
        ring
      · rw [actMC_add, actMC_addv]
        change (g.vec + actMC p g.w h.vec).2.2 +
            (actMC p g.w (actMC p h.w k.vec)).2.2 = _
        change _ = g.vec.2.2 + ((actMC p g.w h.vec) +
          (actMC p g.w (actMC p h.w k.vec))).2.2
        simp only [Prod.snd_add]
        ring
      · change g.w + h.w + k.w = g.w + (h.w + k.w)
        ring)
    (fun g => by
      simp only [mul_def, one_def]
      ext
      · change ((0 : ZMod p × ZMod p × ZMod p) + actMC p 0 g.vec).1 = g.vec.1
        rw [actMC_zero, zero_add]
      · change ((0 : ZMod p × ZMod p × ZMod p) + actMC p 0 g.vec).2.1 = g.vec.2.1
        rw [actMC_zero, zero_add]
      · change ((0 : ZMod p × ZMod p × ZMod p) + actMC p 0 g.vec).2.2 = g.vec.2.2
        rw [actMC_zero, zero_add]
      · change (0 : ZMod p) + g.w = g.w
        ring)
    (fun g => by
      change (⟨-(actMC p (-g.w) g.vec), -g.w⟩ : MaxClass p) * g = 1
      simp only [mul_def, one_def]
      ext
      · change (-(actMC p (-g.w) g.vec) + actMC p (-g.w) g.vec).1 = (0 : ZMod p)
        rw [neg_add_cancel]
        rfl
      · change (-(actMC p (-g.w) g.vec) + actMC p (-g.w) g.vec).2.1 = (0 : ZMod p)
        rw [neg_add_cancel]
        rfl
      · change (-(actMC p (-g.w) g.vec) + actMC p (-g.w) g.vec).2.2 = (0 : ZMod p)
        rw [neg_add_cancel]
        rfl
      · change -g.w + g.w = 0
        ring)

variable (p) in
/-- `MaxClass p ≃ (ZMod p)⁴` as a type. -/
def toProd : MaxClass p ≃ (ZMod p × ZMod p × ZMod p) × ZMod p where
  toFun g := (g.vec, g.w)
  invFun w := ⟨w.1, w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable (p) in
omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem card_maxClass : Nat.card (MaxClass p) = p ^ 4 := by
  rw [Nat.card_congr (toProd p), Nat.card_prod, Nat.card_prod,
    Nat.card_prod, Nat.card_zmod]
  ring

/-- Powers: `(a, w)ⁿ = (∑_{j<n} σ^{jw}(a), nw)`. -/
theorem pow_formula (g : MaxClass p) (n : ℕ) :
    g ^ n = ⟨∑ j ∈ range n, actMC p ((j : ZMod p) * g.w) g.vec,
      (n : ZMod p) * g.w⟩ := by
  induction n with
  | zero =>
    change (1 : MaxClass p) = _
    rw [one_def, range_zero, Finset.sum_empty]
    ext
    · rfl
    · rfl
    · rfl
    · change (0 : ZMod p) = ((0 : ℕ) : ZMod p) * g.w
      push_cast
      ring
  | succ n ih =>
    rw [pow_succ, ih, mul_def]
    have hsum : (∑ j ∈ range n, actMC p ((j : ZMod p) * g.w) g.vec) +
        actMC p ((n : ZMod p) * g.w) g.vec =
        ∑ j ∈ range (n + 1), actMC p ((j : ZMod p) * g.w) g.vec := by
      rw [Finset.sum_range_succ]
    ext
    · change ((∑ j ∈ range n, actMC p ((j : ZMod p) * g.w) g.vec) +
        actMC p ((n : ZMod p) * g.w) g.vec).1 =
        (∑ j ∈ range (n + 1), actMC p ((j : ZMod p) * g.w) g.vec).1
      rw [hsum]
    · change ((∑ j ∈ range n, actMC p ((j : ZMod p) * g.w) g.vec) +
        actMC p ((n : ZMod p) * g.w) g.vec).2.1 =
        (∑ j ∈ range (n + 1), actMC p ((j : ZMod p) * g.w) g.vec).2.1
      rw [hsum]
    · change ((∑ j ∈ range n, actMC p ((j : ZMod p) * g.w) g.vec) +
        actMC p ((n : ZMod p) * g.w) g.vec).2.2 =
        (∑ j ∈ range (n + 1), actMC p ((j : ZMod p) * g.w) g.vec).2.2
      rw [hsum]
    · change (n : ZMod p) * g.w + g.w = ((n + 1 : ℕ) : ZMod p) * g.w
      push_cast
      ring

/-- `T(jw) = w²·T(j) + T(w)·j`: the twisted triangular identity. -/
theorem tri_mul (j w : ZMod p) :
    tri p (j * w) = w ^ 2 * tri p j + tri p w * j := by
  have h2 := two_ne_zero' (p := p)
  have hinv : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ two_isUnit'
  unfold tri
  have hkey : j * w * (j * w - 1) =
      w ^ 2 * (j * (j - 1)) + (w * (w - 1)) * j := by
    ring
  calc j * w * (j * w - 1) * (2 : ZMod p)⁻¹
      = (w ^ 2 * (j * (j - 1)) + (w * (w - 1)) * j) * (2 : ZMod p)⁻¹ := by
        rw [hkey]
    _ = w ^ 2 * (j * (j - 1) * (2 : ZMod p)⁻¹) +
        w * (w - 1) * (2 : ZMod p)⁻¹ * j := by ring

/-- `MaxClass p` has exponent `p` for `p ≥ 5`. -/
theorem pow_p (hp5 : 5 ≤ p) (g : MaxClass p) : g ^ p = 1 := by
  rw [pow_formula, one_def]
  have hp0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  have hlin : (∑ j ∈ range p, ((j : ZMod p))) = 0 := sum_range_cast_zero
  have htri : (∑ j ∈ range p, tri p ((j : ZMod p))) = 0 := sum_tri_zero hp5
  have hconst : ∀ c : ZMod p, (∑ _j ∈ range p, c) = 0 := by
    intro c
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hp0, zero_mul]
  ext
  · change (∑ j ∈ range p, actMC p ((j : ZMod p) * g.w) g.vec).1 = (0 : ZMod p)
    rw [Prod.fst_sum]
    calc (∑ j ∈ range p, (actMC p ((j : ZMod p) * g.w) g.vec).1)
        = ∑ _j ∈ range p, g.vec.1 := Finset.sum_congr rfl fun j _ => rfl
      _ = 0 := hconst _
  · change (∑ j ∈ range p, actMC p ((j : ZMod p) * g.w) g.vec).2.1 =
      (0 : ZMod p)
    rw [Prod.snd_sum, Prod.fst_sum]
    calc (∑ j ∈ range p, (actMC p ((j : ZMod p) * g.w) g.vec).2.1)
        = ∑ j ∈ range p,
            (g.vec.2.1 + (j : ZMod p) * (g.w * g.vec.1)) :=
          Finset.sum_congr rfl fun j _ => by
            change g.vec.2.1 + ((j : ZMod p) * g.w) * g.vec.1 = _
            ring
      _ = (∑ _j ∈ range p, g.vec.2.1) +
            (∑ j ∈ range p, ((j : ZMod p))) * (g.w * g.vec.1) := by
          rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ = 0 := by rw [hconst, hlin, zero_mul, add_zero]
  · change (∑ j ∈ range p, actMC p ((j : ZMod p) * g.w) g.vec).2.2 =
      (0 : ZMod p)
    rw [Prod.snd_sum, Prod.snd_sum]
    calc (∑ j ∈ range p, (actMC p ((j : ZMod p) * g.w) g.vec).2.2)
        = ∑ j ∈ range p,
            (g.vec.2.2 + ((j : ZMod p) * (g.w * g.vec.2.1) +
              (tri p ((j : ZMod p)) * (g.w ^ 2 * g.vec.1) +
                (j : ZMod p) * (tri p g.w * g.vec.1)))) :=
          Finset.sum_congr rfl fun j _ => by
            change g.vec.2.2 + ((j : ZMod p) * g.w) * g.vec.2.1 +
              tri p ((j : ZMod p) * g.w) * g.vec.1 = _
            rw [tri_mul]
            ring
      _ = (∑ _j ∈ range p, g.vec.2.2) +
            ((∑ j ∈ range p, ((j : ZMod p))) * (g.w * g.vec.2.1) +
              ((∑ j ∈ range p, tri p ((j : ZMod p))) *
                  (g.w ^ 2 * g.vec.1) +
                (∑ j ∈ range p, ((j : ZMod p))) *
                  (tri p g.w * g.vec.1))) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul,
            Finset.sum_mul]
      _ = 0 := by
          rw [hconst, hlin, htri, zero_mul, zero_mul, zero_mul, add_zero,
            add_zero, add_zero]
  · change ((p : ℕ) : ZMod p) * g.w = 0
    rw [hp0, zero_mul]

variable (p) in
/-- **Table row (xv), first column**: the maximal-class exponent-`p` group
has exactly `p³ + p² + p + 1` subgroups of order `p` (`p ≥ 5`). -/
theorem card_order_p_subgroups_maxClass (hp5 : 5 ≤ p) :
    Nat.card {H : Subgroup (MaxClass p) // Nat.card H = p} =
      p ^ 3 + p ^ 2 + p + 1 := by
  haveI : Fintype (MaxClass p) := Fintype.ofEquiv _ (toProd p).symm
  exact card_order_p_subgroups_of_exponent _ (card_maxClass p) (pow_p hp5)

end MaxClass

end P4

end LeanDring
