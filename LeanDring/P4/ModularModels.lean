/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P4.ModelPow

/-!
# The modular-type groups of order `p⁴`: models for (vi), (vii), (viii), (ix)

Four more nonabelian groups of order `p⁴`, all with **bilinear** (not
quadratic) commutator cocycles, so no `carryF` is needed anywhere:

* **(vi)** `M6 = C_{p³} ⋊ C_p` — the modular group of order `p⁴`
  (`b a b⁻¹ = a^{1+p²}`, SmallGroup `(p⁴, 6)`), built on a small
  `ZMod p³` lift toolkit (`liftpp = p²·-`, `red3`);
* **(ix)** `G9 = Mod3 × C_p` where `Mod3 = C_{p²} ⋊ C_p` is the modular
  group of order `p³` (`b a b⁻¹ = a^{1+p}`, SmallGroup `(p⁴, 13)`);
* **(vii)** `CH7 = C_{p²} ∘ Heis(p)` — the central product, Heisenberg
  with its center amalgamated into `C_{p²}` (SmallGroup `(p⁴, 14)`);
* **(viii)** `M8 = C_{p²} ⋊ C_{p²}` (`b a b⁻¹ = a^{1+p}`,
  SmallGroup `(p⁴, 4)`).

Main results (sorry-free): group instances, cards, `xᵖ` laws, `Ω₁`
counts, and the **first-column table rows**:

* generic `card_order_p_subgroups_of_omega`: `|Ω₁| = p^k` ⇒
  `#{|H| = p} = ∑_{i<k} pⁱ`;
* (vi): `Ω₁ = p²` ⇒ row `p + 1`;
* (vii): `Ω₁ = p³` ⇒ row `p² + p + 1`;
* (viii): `Ω₁ = p²` ⇒ row `p + 1`;
* (ix): `Ω₁ = p³` ⇒ row `p² + p + 1`.

All match the corrected [GJG10] table.
-/

namespace LeanDring

namespace P4

open Finset Model

variable {p : ℕ} [Fact p.Prime] [Fact (Odd p)]

/-! ## Generic: subgroup count from an `Ω₁` count -/

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
/-- `(∑_{i<k} pⁱ)·(p−1) = pᵏ − 1`. -/
theorem geom_sum_mul_pred (k : ℕ) (hp : 1 ≤ p) :
    (∑ i ∈ range k, p ^ i) * (p - 1) = p ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.add_mul, ih]
    have h1 : p ^ k * (p - 1) = p ^ (k + 1) - p ^ k := by
      rw [Nat.mul_sub, mul_one, ← pow_succ]
    have h2 : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp
    have h3 : p ^ k ≤ p ^ (k + 1) := Nat.pow_le_pow_right hp (by omega)
    omega

omit [Fact (Odd p)] in
/-- **The `Ω₁ →` subgroup-row brick**: if the `p`-torsion of a finite
group has exactly `pᵏ` elements, there are exactly `1 + p + ⋯ + p^{k−1}`
subgroups of order `p`. -/
theorem card_order_p_subgroups_of_omega (G : Type*) [Group G] [Finite G]
    (k : ℕ) (hΩ : Nat.card {x : G // x ^ p = 1} = p ^ k) :
    Nat.card {H : Subgroup G // Nat.card H = p} = ∑ i ∈ range k, p ^ i := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hp : p.Prime := Fact.out
  have hS1 : (univ.filter fun x : G => x ^ p = 1).card = p ^ k := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact hΩ
  have hS2 : (univ.filter fun g : G => orderOf g = p) =
      (univ.filter fun g : G => g ^ p = 1).erase 1 := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    constructor
    · intro ho
      constructor
      · intro h1
        rw [h1, orderOf_one] at ho
        have := hp.one_lt
        omega
      · have hpow := pow_orderOf_eq_one g
        rw [ho] at hpow
        exact hpow
    · rintro ⟨h1, hpow⟩
      have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hpow
      rcases (Nat.dvd_prime hp).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) h1
      · exact h
  have hone : (1 : G) ∈ univ.filter fun x : G => x ^ p = 1 := by simp
  have hS2card : (univ.filter fun g : G => orderOf g = p).card =
      p ^ k - 1 := by
    rw [hS2, Finset.card_erase_of_mem hone, hS1]
  have hdouble := card_orderOf_eq_prime (G := G) hp
  rw [hS2card, ← geom_sum_mul_pred k hp.one_lt.le] at hdouble
  have hqpos : 0 < p - 1 := by
    have := hp.one_lt
    omega
  exact Nat.eq_of_mul_eq_mul_right hqpos hdouble.symm

/-! ## Group (ix): the modular group `Mod3 = C_{p²} ⋊ C_p` times `C_p` -/

variable (p) in
/-- The modular group of order `p³`: normal forms `a^α b^u` with
`b a b⁻¹ = a^{1+p}`, i.e. `(α,u)·(β,u') = (α + β + p·u·(β mod p), u+u')`. -/
@[ext]
structure Mod3 where
  α : ZMod (p ^ 2)
  u : ZMod p

namespace Mod3

instance : Mul (Mod3 p) :=
  ⟨fun x y => ⟨x.α + y.α + liftp p (x.u * redp p y.α), x.u + y.u⟩⟩

instance : One (Mod3 p) := ⟨⟨0, 0⟩⟩

noncomputable instance : Inv (Mod3 p) :=
  ⟨fun x => ⟨-x.α + liftp p (x.u * redp p x.α), -x.u⟩⟩

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem mul_def (x y : Mod3 p) :
    x * y = ⟨x.α + y.α + liftp p (x.u * redp p y.α), x.u + y.u⟩ := rfl

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem one_def : (1 : Mod3 p) = ⟨0, 0⟩ := rfl

omit [Fact (Odd p)] in
theorem liftp_neg (z : ZMod p) : liftp p (-z) = -(liftp p z) := by
  have h := liftp_add (p := p) z (-z)
  rw [add_neg_cancel, liftp_zero] at h
  have h0 : liftp p (-z) + liftp p z = 0 := by
    rw [add_comm]
    exact h.symm
  exact eq_neg_of_add_eq_zero_left h0

noncomputable instance : Group (Mod3 p) :=
  Group.ofLeftAxioms
    (fun x y z => by
      simp only [mul_def]
      ext
      · change x.α + y.α + liftp p (x.u * redp p y.α) + z.α +
            liftp p ((x.u + y.u) * redp p z.α) =
          x.α + (y.α + z.α + liftp p (y.u * redp p z.α)) +
            liftp p (x.u * redp p (y.α + z.α + liftp p (y.u * redp p z.α)))
        rw [map_add, map_add, redp_liftp, add_zero, mul_add, liftp_add,
          add_mul, liftp_add]
        ring
      · change x.u + y.u + z.u = x.u + (y.u + z.u)
        ring)
    (fun x => by
      simp only [mul_def, one_def]
      ext
      · change (0 : ZMod (p ^ 2)) + x.α + liftp p (0 * redp p x.α) = x.α
        rw [zero_mul, liftp_zero]
        ring
      · change (0 : ZMod p) + x.u = x.u
        ring)
    (fun x => by
      change (⟨-x.α + liftp p (x.u * redp p x.α), -x.u⟩ : Mod3 p) * x = 1
      simp only [mul_def, one_def]
      ext
      · change -x.α + liftp p (x.u * redp p x.α) + x.α +
            liftp p (-x.u * redp p x.α) = 0
        have h : (-x.u) * redp p x.α = -(x.u * redp p x.α) := by ring
        rw [h, liftp_neg]
        ring
      · change -x.u + x.u = 0
        ring)

variable (p) in
def toProd : Mod3 p ≃ ZMod (p ^ 2) × ZMod p where
  toFun x := (x.α, x.u)
  invFun w := ⟨w.1, w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

noncomputable instance : Fintype (Mod3 p) :=
  Fintype.ofEquiv _ (toProd p).symm

variable (p) in
omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem card_mod3 : Nat.card (Mod3 p) = p ^ 3 := by
  rw [Nat.card_congr (toProd p), Nat.card_prod, Nat.card_zmod,
    Nat.card_zmod]
  ring

/-- Powers in `Mod3`: `xⁿ = ⟨nα + p·T(n)·u·(α mod p), nu⟩`. -/
theorem pow_formula (x : Mod3 p) (n : ℕ) :
    x ^ n = ⟨(n : ZMod (p ^ 2)) * x.α +
        liftp p (tri p ((n : ZMod p)) * (x.u * redp p x.α)),
      (n : ZMod p) * x.u⟩ := by
  induction n with
  | zero =>
    change (1 : Mod3 p) = _
    rw [one_def]
    have htri : tri p ((0 : ℕ) : ZMod p) = 0 := by
      unfold tri
      push_cast
      ring
    ext
    · change (0 : ZMod (p ^ 2)) = ((0 : ℕ) : ZMod (p ^ 2)) * x.α +
        liftp p (tri p ((0 : ℕ) : ZMod p) * (x.u * redp p x.α))
      rw [htri, zero_mul, liftp_zero]
      push_cast
      ring
    · change (0 : ZMod p) = ((0 : ℕ) : ZMod p) * x.u
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
    · change (n : ZMod (p ^ 2)) * x.α +
          liftp p (tri p ((n : ZMod p)) * (x.u * redp p x.α)) + x.α +
          liftp p (((n : ZMod p) * x.u) * redp p x.α) =
        ((n + 1 : ℕ) : ZMod (p ^ 2)) * x.α +
          liftp p (tri p ((n + 1 : ℕ) : ZMod p) * (x.u * redp p x.α))
      rw [htri]
      have hL : (tri p ((n : ZMod p)) + (n : ZMod p)) *
          (x.u * redp p x.α) =
          tri p ((n : ZMod p)) * (x.u * redp p x.α) +
            ((n : ZMod p) * x.u) * redp p x.α := by ring
      rw [hL, liftp_add]
      push_cast
      ring
    · change (n : ZMod p) * x.u + x.u = ((n + 1 : ℕ) : ZMod p) * x.u
      push_cast
      ring

/-- `xᵖ = aᵖᵅ` in `Mod3`; torsion criterion `xᵖ = 1 ⟺ α ≡ 0 (mod p)`. -/
theorem pow_p_eq_one_iff (x : Mod3 p) :
    x ^ p = 1 ↔ redp p x.α = 0 := by
  have hp0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  have htri : tri p (0 : ZMod p) = 0 := by
    unfold tri
    ring
  have hpow : x ^ p = ⟨liftp p (redp p x.α), 0⟩ := by
    rw [pow_formula]
    ext
    · change ((p : ℕ) : ZMod (p ^ 2)) * x.α +
          liftp p (tri p ((p : ℕ) : ZMod p) * (x.u * redp p x.α)) =
        liftp p (redp p x.α)
      rw [hp0, htri, zero_mul, liftp_zero, add_zero,
        p_mul_eq_liftp_redp]
    · change ((p : ℕ) : ZMod p) * x.u = 0
      rw [hp0, zero_mul]
  rw [hpow, one_def]
  constructor
  · intro h
    have hα : liftp p (redp p x.α) = (0 : ZMod (p ^ 2)) :=
      congrArg Mod3.α h
    exact liftp_eq_zero_iff.mp hα
  · intro h
    rw [h, liftp_zero]

variable (p) in
/-- `|Ω₁(Mod3)| = p²`. -/
theorem card_omega : Nat.card {x : Mod3 p // x ^ p = 1} = p ^ 2 := by
  have hp : p.Prime := Fact.out
  let f : ZMod p × ZMod p → {x : Mod3 p // x ^ p = 1} := fun w =>
    ⟨⟨liftp p w.1, w.2⟩, by
      rw [pow_p_eq_one_iff]
      exact redp_liftp w.1⟩
  let g : {x : Mod3 p // x ^ p = 1} → ZMod p × ZMod p := fun x =>
    (((x.1.α.val / p : ℕ) : ZMod p), x.1.u)
  have hbij : Function.Bijective f := by
    rw [Function.bijective_iff_has_inverse]
    refine ⟨g, fun w => ?_, fun x => ?_⟩
    · change ((((liftp p w.1).val / p : ℕ) : ZMod p), w.2) = w
      rw [liftp_val, Nat.mul_div_cancel_left _
        (Nat.pos_of_ne_zero hp.ne_zero), ZMod.natCast_val, ZMod.cast_id]
    · obtain ⟨x, hx⟩ := x
      have hred : redp p x.α = 0 := (pow_p_eq_one_iff x).mp hx
      refine Subtype.ext ?_
      change (⟨liftp p (((x.α.val / p : ℕ) : ZMod p)), x.u⟩ : Mod3 p) = x
      have hα := liftp_of_redp_zero hred
      ext
      · change liftp p (((x.α.val / p : ℕ) : ZMod p)) = x.α
        exact hα
      · rfl
  rw [← Nat.card_eq_of_bijective f hbij, Nat.card_prod, Nat.card_zmod]
  ring

end Mod3

/-! ## Group (ix) `= Mod3 × C_p` -/

variable (p) in
/-- **Group (ix)** `= M(p³) × C_p` (SmallGroup `(p⁴, 13)`). -/
abbrev G9 := Mod3 p × Multiplicative (ZMod p)

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem multZMod_pow_p (c : Multiplicative (ZMod p)) : c ^ p = 1 := by
  have h2 : p • c.toAdd = (0 : ZMod p) := by
    rw [nsmul_eq_mul]
    have h0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
    rw [h0, zero_mul]
  calc c ^ p = (Multiplicative.ofAdd c.toAdd) ^ p := rfl
    _ = Multiplicative.ofAdd (p • c.toAdd) := by rw [← ofAdd_nsmul]
    _ = 1 := by rw [h2]; rfl

variable (p) in
theorem card_omega_g9 : Nat.card {x : G9 p // x ^ p = 1} = p ^ 3 := by
  let f : {x : G9 p // x ^ p = 1} →
      {a : Mod3 p // a ^ p = 1} × Multiplicative (ZMod p) := fun x =>
    (⟨x.1.1, congrArg Prod.fst x.2⟩, x.1.2)
  have hbij : Function.Bijective f := by
    rw [Function.bijective_iff_has_inverse]
    refine ⟨fun w => ⟨(w.1.1, w.2), Prod.ext w.1.2 (multZMod_pow_p w.2)⟩,
      fun x => ?_, fun w => ?_⟩
    · refine Subtype.ext ?_
      rfl
    · refine Prod.ext (Subtype.ext rfl) rfl
  rw [Nat.card_eq_of_bijective f hbij, Nat.card_prod, Mod3.card_omega]
  have h1 : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  rw [h1]
  ring

variable (p) in
/-- **Table row (ix), first column**: `M(p³) × C_p` has exactly
`p² + p + 1` subgroups of order `p`. -/
theorem card_order_p_subgroups_g9 :
    Nat.card {H : Subgroup (G9 p) // Nat.card H = p} = p ^ 2 + p + 1 := by
  have h := card_order_p_subgroups_of_omega (G9 p) 3 (card_omega_g9 p)
  rw [h]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  ring

/-! ## The `ZMod p³` lift toolkit -/

variable (p) in
/-- The lift `ZMod p → ZMod p³`, `x ↦ p²·x`. -/
def liftpp (x : ZMod p) : ZMod (p ^ 3) :=
  (p : ZMod (p ^ 3)) ^ 2 * (x.val : ZMod (p ^ 3))

variable (p) in
/-- Reduction `ZMod p³ →+* ZMod p`. -/
def red3 : ZMod (p ^ 3) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by norm_num : (3 : ℕ) ≠ 0)) (ZMod p)

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem p3_cast_zero : (p : ZMod (p ^ 3)) ^ 2 * (p : ZMod (p ^ 3)) = 0 := by
  have h : (((p ^ 3 : ℕ)) : ZMod (p ^ 3)) = 0 := ZMod.natCast_self _
  push_cast at h
  linear_combination h

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
@[simp] theorem liftpp_zero : liftpp p 0 = 0 := by
  unfold liftpp
  simp

omit [Fact (Odd p)] in
theorem liftpp_add (x y : ZMod p) :
    liftpp p (x + y) = liftpp p x + liftpp p y := by
  unfold liftpp
  obtain ⟨hle, h0 | hp'⟩ := carry_val x y
  · have hval : (x + y).val = x.val + y.val := by omega
    rw [hval]
    push_cast
    ring
  · have hval : (x + y).val = x.val + y.val - p := by omega
    have hple : p ≤ x.val + y.val := by omega
    rw [hval, Nat.cast_sub hple]
    push_cast
    linear_combination -(p3_cast_zero (p := p))

omit [Fact (Odd p)] in
theorem liftpp_neg (z : ZMod p) : liftpp p (-z) = -(liftpp p z) := by
  have h := liftpp_add (p := p) z (-z)
  rw [add_neg_cancel, liftpp_zero] at h
  have h0 : liftpp p (-z) + liftpp p z = 0 := by
    rw [add_comm]
    exact h.symm
  exact eq_neg_of_add_eq_zero_left h0

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
@[simp] theorem red3_liftpp (x : ZMod p) : red3 p (liftpp p x) = 0 := by
  unfold liftpp
  rw [map_mul, map_pow]
  have h : red3 p ((p : ZMod (p ^ 3))) = 0 := by
    have h0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self _
    rw [map_natCast, h0]
  rw [h]
  ring

omit [Fact (Odd p)] in
theorem liftpp_val (t : ZMod p) : (liftpp p t).val = p ^ 2 * t.val := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp.ne_zero⟩
  have h1 : liftpp p t = ((p ^ 2 * t.val : ℕ) : ZMod (p ^ 3)) := by
    unfold liftpp
    push_cast
    ring
  rw [h1, ZMod.val_natCast, Nat.mod_eq_of_lt]
  have hlt := ZMod.val_lt t
  calc p ^ 2 * t.val < p ^ 2 * p :=
        mul_lt_mul_of_pos_left hlt
          (pow_pos (Nat.pos_of_ne_zero hp.ne_zero) 2)
    _ = p ^ 3 := by ring

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem p_mul_liftpp (t : ZMod p) :
    (p : ZMod (p ^ 3)) * liftpp p t = 0 := by
  unfold liftpp
  calc (p : ZMod (p ^ 3)) * ((p : ZMod (p ^ 3)) ^ 2 * (t.val : ZMod (p ^ 3)))
      = (p : ZMod (p ^ 3)) ^ 2 * (p : ZMod (p ^ 3)) *
        (t.val : ZMod (p ^ 3)) := by ring
    _ = 0 := by rw [p3_cast_zero, zero_mul]

omit [Fact (Odd p)] in
/-- Solutions of `p·α = 0` in `ZMod p³` are exactly the lifts. -/
theorem liftpp_of_p_mul_zero {α : ZMod (p ^ 3)}
    (h : (p : ZMod (p ^ 3)) * α = 0) :
    liftpp p (((α.val / p ^ 2 : ℕ) : ZMod p)) = α := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp.ne_zero⟩
  have hppos : 0 < p := Nat.pos_of_ne_zero hp.ne_zero
  have hα : ((α.val : ℕ) : ZMod (p ^ 3)) = α := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  have hcast : ((p * α.val : ℕ) : ZMod (p ^ 3)) = 0 := by
    push_cast
    rw [hα]
    exact h
  have hdvd3 : p ^ 3 ∣ p * α.val :=
    (CharP.cast_eq_zero_iff (ZMod (p ^ 3)) (p ^ 3) _).mp hcast
  have hdvd2 : p ^ 2 ∣ α.val := by
    rcases hdvd3 with ⟨c, hc⟩
    have hc2 : p * α.val = p * (p ^ 2 * c) := by
      rw [hc]
      ring
    exact ⟨c, Nat.eq_of_mul_eq_mul_left hppos hc2⟩
  have hdiv : α.val = p ^ 2 * (α.val / p ^ 2) :=
    (Nat.mul_div_cancel' hdvd2).symm
  have hlt : α.val / p ^ 2 < p := by
    have hv : α.val < p ^ 3 := ZMod.val_lt α
    refine Nat.div_lt_of_lt_mul ?_
    calc α.val < p ^ 3 := hv
      _ = p ^ 2 * p := by ring
  have hvalcast : ((((α.val / p ^ 2 : ℕ) : ZMod p)).val) = α.val / p ^ 2 := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  unfold liftpp
  rw [hvalcast]
  calc (p : ZMod (p ^ 3)) ^ 2 * ((α.val / p ^ 2 : ℕ) : ZMod (p ^ 3))
      = ((p ^ 2 * (α.val / p ^ 2) : ℕ) : ZMod (p ^ 3)) := by
        push_cast
        ring
    _ = ((α.val : ℕ) : ZMod (p ^ 3)) := by rw [← hdiv]
    _ = α := hα

/-! ## Group (vi): the modular group `M6 = C_{p³} ⋊ C_p` -/

variable (p) in
/-- **Group (vi)**: normal forms `a^α b^u` with `b a b⁻¹ = a^{1+p²}`
(SmallGroup `(p⁴, 6)`). -/
@[ext]
structure M6 where
  α : ZMod (p ^ 3)
  u : ZMod p

namespace M6

instance : Mul (M6 p) :=
  ⟨fun x y => ⟨x.α + y.α + liftpp p (x.u * red3 p y.α), x.u + y.u⟩⟩

instance : One (M6 p) := ⟨⟨0, 0⟩⟩

instance : Inv (M6 p) :=
  ⟨fun x => ⟨-x.α + liftpp p (x.u * red3 p x.α), -x.u⟩⟩

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem mul_def (x y : M6 p) :
    x * y = ⟨x.α + y.α + liftpp p (x.u * red3 p y.α), x.u + y.u⟩ := rfl

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem one_def : (1 : M6 p) = ⟨0, 0⟩ := rfl

instance : Group (M6 p) :=
  Group.ofLeftAxioms
    (fun x y z => by
      simp only [mul_def]
      ext
      · change x.α + y.α + liftpp p (x.u * red3 p y.α) + z.α +
            liftpp p ((x.u + y.u) * red3 p z.α) =
          x.α + (y.α + z.α + liftpp p (y.u * red3 p z.α)) +
            liftpp p (x.u * red3 p (y.α + z.α + liftpp p (y.u * red3 p z.α)))
        rw [map_add, map_add, red3_liftpp, add_zero, mul_add, liftpp_add,
          add_mul, liftpp_add]
        ring
      · change x.u + y.u + z.u = x.u + (y.u + z.u)
        ring)
    (fun x => by
      simp only [mul_def, one_def]
      ext
      · change (0 : ZMod (p ^ 3)) + x.α + liftpp p (0 * red3 p x.α) = x.α
        rw [zero_mul, liftpp_zero]
        ring
      · change (0 : ZMod p) + x.u = x.u
        ring)
    (fun x => by
      change (⟨-x.α + liftpp p (x.u * red3 p x.α), -x.u⟩ : M6 p) * x = 1
      simp only [mul_def, one_def]
      ext
      · change -x.α + liftpp p (x.u * red3 p x.α) + x.α +
            liftpp p (-x.u * red3 p x.α) = 0
        have h : (-x.u) * red3 p x.α = -(x.u * red3 p x.α) := by ring
        rw [h, liftpp_neg]
        ring
      · change -x.u + x.u = 0
        ring)

variable (p) in
def toProd : M6 p ≃ ZMod (p ^ 3) × ZMod p where
  toFun x := (x.α, x.u)
  invFun w := ⟨w.1, w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : Fintype (M6 p) :=
  Fintype.ofEquiv _ (toProd p).symm

variable (p) in
omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem card_m6 : Nat.card (M6 p) = p ^ 4 := by
  rw [Nat.card_congr (toProd p), Nat.card_prod, Nat.card_zmod,
    Nat.card_zmod]
  ring

/-- Powers in `M6`: `xⁿ = ⟨nα + p²·T(n)·u·(α mod p), nu⟩`. -/
theorem pow_formula (x : M6 p) (n : ℕ) :
    x ^ n = ⟨(n : ZMod (p ^ 3)) * x.α +
        liftpp p (tri p ((n : ZMod p)) * (x.u * red3 p x.α)),
      (n : ZMod p) * x.u⟩ := by
  induction n with
  | zero =>
    change (1 : M6 p) = _
    rw [one_def]
    have htri : tri p ((0 : ℕ) : ZMod p) = 0 := by
      unfold tri
      push_cast
      ring
    ext
    · change (0 : ZMod (p ^ 3)) = ((0 : ℕ) : ZMod (p ^ 3)) * x.α +
        liftpp p (tri p ((0 : ℕ) : ZMod p) * (x.u * red3 p x.α))
      rw [htri, zero_mul, liftpp_zero]
      push_cast
      ring
    · change (0 : ZMod p) = ((0 : ℕ) : ZMod p) * x.u
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
    · change (n : ZMod (p ^ 3)) * x.α +
          liftpp p (tri p ((n : ZMod p)) * (x.u * red3 p x.α)) + x.α +
          liftpp p (((n : ZMod p) * x.u) * red3 p x.α) =
        ((n + 1 : ℕ) : ZMod (p ^ 3)) * x.α +
          liftpp p (tri p ((n + 1 : ℕ) : ZMod p) * (x.u * red3 p x.α))
      rw [htri]
      have hL : (tri p ((n : ZMod p)) + (n : ZMod p)) *
          (x.u * red3 p x.α) =
          tri p ((n : ZMod p)) * (x.u * red3 p x.α) +
            ((n : ZMod p) * x.u) * red3 p x.α := by ring
      rw [hL, liftpp_add]
      push_cast
      ring
    · change (n : ZMod p) * x.u + x.u = ((n + 1 : ℕ) : ZMod p) * x.u
      push_cast
      ring

/-- Torsion criterion in `M6`: `xᵖ = 1 ⟺ p·α = 0` (i.e. `α ∈ p²·C_{p³}`). -/
theorem pow_p_eq_one_iff (x : M6 p) :
    x ^ p = 1 ↔ (p : ZMod (p ^ 3)) * x.α = 0 := by
  have hp0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  have htri : tri p (0 : ZMod p) = 0 := by
    unfold tri
    ring
  have hpow : x ^ p = ⟨(p : ZMod (p ^ 3)) * x.α, 0⟩ := by
    rw [pow_formula]
    ext
    · change ((p : ℕ) : ZMod (p ^ 3)) * x.α +
          liftpp p (tri p ((p : ℕ) : ZMod p) * (x.u * red3 p x.α)) =
        (p : ZMod (p ^ 3)) * x.α
      rw [hp0, htri, zero_mul, liftpp_zero, add_zero]
    · change ((p : ℕ) : ZMod p) * x.u = 0
      rw [hp0, zero_mul]
  rw [hpow, one_def]
  constructor
  · intro h
    exact congrArg M6.α h
  · intro h
    rw [h]

variable (p) in
/-- `|Ω₁(M6)| = p²`. -/
theorem card_omega : Nat.card {x : M6 p // x ^ p = 1} = p ^ 2 := by
  have hp : p.Prime := Fact.out
  let f : ZMod p × ZMod p → {x : M6 p // x ^ p = 1} := fun w =>
    ⟨⟨liftpp p w.1, w.2⟩, by
      rw [pow_p_eq_one_iff]
      exact p_mul_liftpp w.1⟩
  let g : {x : M6 p // x ^ p = 1} → ZMod p × ZMod p := fun x =>
    (((x.1.α.val / p ^ 2 : ℕ) : ZMod p), x.1.u)
  have hbij : Function.Bijective f := by
    rw [Function.bijective_iff_has_inverse]
    refine ⟨g, fun w => ?_, fun x => ?_⟩
    · change ((((liftpp p w.1).val / p ^ 2 : ℕ) : ZMod p), w.2) = w
      rw [liftpp_val, Nat.mul_div_cancel_left _
        (pow_pos (Nat.pos_of_ne_zero hp.ne_zero) 2), ZMod.natCast_val,
        ZMod.cast_id]
    · obtain ⟨x, hx⟩ := x
      have hred : (p : ZMod (p ^ 3)) * x.α = 0 :=
        (pow_p_eq_one_iff x).mp hx
      refine Subtype.ext ?_
      change (⟨liftpp p (((x.α.val / p ^ 2 : ℕ) : ZMod p)), x.u⟩ : M6 p) = x
      ext
      · change liftpp p (((x.α.val / p ^ 2 : ℕ) : ZMod p)) = x.α
        exact liftpp_of_p_mul_zero hred
      · rfl
  rw [← Nat.card_eq_of_bijective f hbij, Nat.card_prod, Nat.card_zmod]
  ring

variable (p) in
/-- **Table row (vi), first column**: the modular group of order `p⁴` has
exactly `p + 1` subgroups of order `p`. -/
theorem card_order_p_subgroups_m6 :
    Nat.card {H : Subgroup (M6 p) // Nat.card H = p} = p + 1 := by
  have h := card_order_p_subgroups_of_omega (M6 p) 2 (card_omega p)
  rw [h, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  ring

end M6

/-! ## Group (viii): `M8 = C_{p²} ⋊ C_{p²}` -/

variable (p) in
/-- **Group (viii)**: normal forms `a^α b^γ`, both exponents mod `p²`,
with `b a b⁻¹ = a^{1+p}` (SmallGroup `(p⁴, 4)`). -/
@[ext]
structure M8 where
  α : ZMod (p ^ 2)
  γ : ZMod (p ^ 2)

namespace M8

noncomputable instance : Mul (M8 p) :=
  ⟨fun x y => ⟨x.α + y.α + liftp p (redp p x.γ * redp p y.α), x.γ + y.γ⟩⟩

instance : One (M8 p) := ⟨⟨0, 0⟩⟩

noncomputable instance : Inv (M8 p) :=
  ⟨fun x => ⟨-x.α + liftp p (redp p x.γ * redp p x.α), -x.γ⟩⟩

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem mul_def (x y : M8 p) :
    x * y = ⟨x.α + y.α + liftp p (redp p x.γ * redp p y.α), x.γ + y.γ⟩ := rfl

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem one_def : (1 : M8 p) = ⟨0, 0⟩ := rfl

noncomputable instance : Group (M8 p) :=
  Group.ofLeftAxioms
    (fun x y z => by
      simp only [mul_def]
      ext
      · change x.α + y.α + liftp p (redp p x.γ * redp p y.α) + z.α +
            liftp p (redp p (x.γ + y.γ) * redp p z.α) =
          x.α + (y.α + z.α + liftp p (redp p y.γ * redp p z.α)) +
            liftp p (redp p x.γ *
              redp p (y.α + z.α + liftp p (redp p y.γ * redp p z.α)))
        rw [map_add, map_add, map_add, redp_liftp, add_zero, mul_add,
          liftp_add, add_mul, liftp_add]
        ring
      · change x.γ + y.γ + z.γ = x.γ + (y.γ + z.γ)
        ring)
    (fun x => by
      simp only [mul_def, one_def]
      ext
      · change (0 : ZMod (p ^ 2)) + x.α +
            liftp p (redp p (0 : ZMod (p ^ 2)) * redp p x.α) = x.α
        rw [map_zero, zero_mul, liftp_zero]
        ring
      · change (0 : ZMod (p ^ 2)) + x.γ = x.γ
        ring)
    (fun x => by
      change (⟨-x.α + liftp p (redp p x.γ * redp p x.α), -x.γ⟩ : M8 p) * x = 1
      simp only [mul_def, one_def]
      ext
      · change -x.α + liftp p (redp p x.γ * redp p x.α) + x.α +
            liftp p (redp p (-x.γ) * redp p x.α) = 0
        have h : redp p (-x.γ) * redp p x.α =
            -(redp p x.γ * redp p x.α) := by
          rw [map_neg]
          ring
        rw [h, Mod3.liftp_neg]
        ring
      · change -x.γ + x.γ = 0
        ring)

variable (p) in
def toProd : M8 p ≃ ZMod (p ^ 2) × ZMod (p ^ 2) where
  toFun x := (x.α, x.γ)
  invFun w := ⟨w.1, w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : Fintype (M8 p) :=
  Fintype.ofEquiv _ (toProd p).symm

variable (p) in
omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem card_m8 : Nat.card (M8 p) = p ^ 4 := by
  rw [Nat.card_congr (toProd p), Nat.card_prod, Nat.card_zmod]
  ring

/-- Powers in `M8`: `xⁿ = ⟨nα + p·T(n)·(γ mod p)(α mod p), nγ⟩`. -/
theorem pow_formula (x : M8 p) (n : ℕ) :
    x ^ n = ⟨(n : ZMod (p ^ 2)) * x.α +
        liftp p (tri p ((n : ZMod p)) * (redp p x.γ * redp p x.α)),
      (n : ZMod (p ^ 2)) * x.γ⟩ := by
  induction n with
  | zero =>
    change (1 : M8 p) = _
    rw [one_def]
    have htri : tri p ((0 : ℕ) : ZMod p) = 0 := by
      unfold tri
      push_cast
      ring
    ext
    · change (0 : ZMod (p ^ 2)) = ((0 : ℕ) : ZMod (p ^ 2)) * x.α +
        liftp p (tri p ((0 : ℕ) : ZMod p) * (redp p x.γ * redp p x.α))
      rw [htri, zero_mul, liftp_zero]
      push_cast
      ring
    · change (0 : ZMod (p ^ 2)) = ((0 : ℕ) : ZMod (p ^ 2)) * x.γ
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
    have hredn : redp p ((n : ZMod (p ^ 2)) * x.γ) =
        (n : ZMod p) * redp p x.γ := by
      rw [map_mul, map_natCast]
    ext
    · change (n : ZMod (p ^ 2)) * x.α +
          liftp p (tri p ((n : ZMod p)) * (redp p x.γ * redp p x.α)) + x.α +
          liftp p (redp p ((n : ZMod (p ^ 2)) * x.γ) * redp p x.α) =
        ((n + 1 : ℕ) : ZMod (p ^ 2)) * x.α +
          liftp p (tri p ((n + 1 : ℕ) : ZMod p) *
            (redp p x.γ * redp p x.α))
      rw [hredn, htri]
      have hL : (tri p ((n : ZMod p)) + (n : ZMod p)) *
          (redp p x.γ * redp p x.α) =
          tri p ((n : ZMod p)) * (redp p x.γ * redp p x.α) +
            ((n : ZMod p) * redp p x.γ) * redp p x.α := by ring
      rw [hL, liftp_add]
      push_cast
      ring
    · change (n : ZMod (p ^ 2)) * x.γ + x.γ = ((n + 1 : ℕ) : ZMod (p ^ 2)) * x.γ
      push_cast
      ring

/-- Torsion criterion in `M8`: `xᵖ = 1 ⟺ α ≡ 0 ∧ γ ≡ 0 (mod p)`. -/
theorem pow_p_eq_one_iff (x : M8 p) :
    x ^ p = 1 ↔ redp p x.α = 0 ∧ redp p x.γ = 0 := by
  have hp0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  have htri : tri p (0 : ZMod p) = 0 := by
    unfold tri
    ring
  have hpow : x ^ p = ⟨liftp p (redp p x.α), liftp p (redp p x.γ)⟩ := by
    rw [pow_formula]
    ext
    · change ((p : ℕ) : ZMod (p ^ 2)) * x.α +
          liftp p (tri p ((p : ℕ) : ZMod p) * (redp p x.γ * redp p x.α)) =
        liftp p (redp p x.α)
      rw [hp0, htri, zero_mul, liftp_zero, add_zero, p_mul_eq_liftp_redp]
    · change ((p : ℕ) : ZMod (p ^ 2)) * x.γ = liftp p (redp p x.γ)
      exact p_mul_eq_liftp_redp x.γ
  rw [hpow, one_def]
  constructor
  · intro h
    exact ⟨liftp_eq_zero_iff.mp (congrArg M8.α h),
      liftp_eq_zero_iff.mp (congrArg M8.γ h)⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2, liftp_zero]

variable (p) in
/-- `|Ω₁(M8)| = p²`. -/
theorem card_omega : Nat.card {x : M8 p // x ^ p = 1} = p ^ 2 := by
  have hp : p.Prime := Fact.out
  let f : ZMod p × ZMod p → {x : M8 p // x ^ p = 1} := fun w =>
    ⟨⟨liftp p w.1, liftp p w.2⟩, by
      rw [pow_p_eq_one_iff]
      exact ⟨redp_liftp w.1, redp_liftp w.2⟩⟩
  let g : {x : M8 p // x ^ p = 1} → ZMod p × ZMod p := fun x =>
    (((x.1.α.val / p : ℕ) : ZMod p), ((x.1.γ.val / p : ℕ) : ZMod p))
  have hbij : Function.Bijective f := by
    rw [Function.bijective_iff_has_inverse]
    refine ⟨g, fun w => ?_, fun x => ?_⟩
    · change ((((liftp p w.1).val / p : ℕ) : ZMod p),
        (((liftp p w.2).val / p : ℕ) : ZMod p)) = w
      rw [liftp_val, liftp_val, Nat.mul_div_cancel_left _
        (Nat.pos_of_ne_zero hp.ne_zero), Nat.mul_div_cancel_left _
        (Nat.pos_of_ne_zero hp.ne_zero), ZMod.natCast_val, ZMod.cast_id,
        ZMod.natCast_val, ZMod.cast_id]
    · obtain ⟨x, hx⟩ := x
      obtain ⟨h1, h2⟩ := (pow_p_eq_one_iff x).mp hx
      refine Subtype.ext ?_
      change (⟨liftp p (((x.α.val / p : ℕ) : ZMod p)),
        liftp p (((x.γ.val / p : ℕ) : ZMod p))⟩ : M8 p) = x
      ext
      · exact liftp_of_redp_zero h1
      · exact liftp_of_redp_zero h2
  rw [← Nat.card_eq_of_bijective f hbij, Nat.card_prod, Nat.card_zmod]
  ring

variable (p) in
/-- **Table row (viii), first column**: `C_{p²} ⋊ C_{p²}` has exactly
`p + 1` subgroups of order `p`. -/
theorem card_order_p_subgroups_m8 :
    Nat.card {H : Subgroup (M8 p) // Nat.card H = p} = p + 1 := by
  have h := card_order_p_subgroups_of_omega (M8 p) 2 (card_omega p)
  rw [h, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  ring

end M8

/-! ## Group (vii): the central product `CH7 = C_{p²} ∘ Heis(p)` -/

variable (p) in
/-- **Group (vii)**: Heisenberg with its center amalgamated into `C_{p²}`
— normal forms `(x, y, z)`, `z ∈ C_{p²}`, commutator landing in `p·C_{p²}`
(SmallGroup `(p⁴, 14)`). -/
@[ext]
structure CH7 where
  x : ZMod p
  y : ZMod p
  z : ZMod (p ^ 2)

namespace CH7

instance : Mul (CH7 p) :=
  ⟨fun a b => ⟨a.x + b.x, a.y + b.y, a.z + b.z + liftp p (a.x * b.y)⟩⟩

instance : One (CH7 p) := ⟨⟨0, 0, 0⟩⟩

instance : Inv (CH7 p) :=
  ⟨fun a => ⟨-a.x, -a.y, -a.z + liftp p (a.x * a.y)⟩⟩

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem mul_def (a b : CH7 p) :
    a * b = ⟨a.x + b.x, a.y + b.y, a.z + b.z + liftp p (a.x * b.y)⟩ := rfl

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem one_def : (1 : CH7 p) = ⟨0, 0, 0⟩ := rfl

instance : Group (CH7 p) :=
  Group.ofLeftAxioms
    (fun a b c => by
      simp only [mul_def]
      ext
      · change a.x + b.x + c.x = a.x + (b.x + c.x)
        ring
      · change a.y + b.y + c.y = a.y + (b.y + c.y)
        ring
      · change a.z + b.z + liftp p (a.x * b.y) + c.z +
            liftp p ((a.x + b.x) * c.y) =
          a.z + (b.z + c.z + liftp p (b.x * c.y)) +
            liftp p (a.x * (b.y + c.y))
        rw [add_mul, liftp_add, mul_add, liftp_add]
        ring
      )
    (fun a => by
      simp only [mul_def, one_def]
      ext
      · change (0 : ZMod p) + a.x = a.x
        ring
      · change (0 : ZMod p) + a.y = a.y
        ring
      · change (0 : ZMod (p ^ 2)) + a.z + liftp p (0 * a.y) = a.z
        rw [zero_mul, liftp_zero]
        ring)
    (fun a => by
      change (⟨-a.x, -a.y, -a.z + liftp p (a.x * a.y)⟩ : CH7 p) * a = 1
      simp only [mul_def, one_def]
      ext
      · change -a.x + a.x = 0
        ring
      · change -a.y + a.y = 0
        ring
      · change -a.z + liftp p (a.x * a.y) + a.z + liftp p (-a.x * a.y) = 0
        have h : (-a.x) * a.y = -(a.x * a.y) := by ring
        rw [h, Mod3.liftp_neg]
        ring)

variable (p) in
def toProd : CH7 p ≃ ZMod p × ZMod p × ZMod (p ^ 2) where
  toFun a := (a.x, a.y, a.z)
  invFun w := ⟨w.1, w.2.1, w.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : Fintype (CH7 p) :=
  Fintype.ofEquiv _ (toProd p).symm

variable (p) in
omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem card_ch7 : Nat.card (CH7 p) = p ^ 4 := by
  rw [Nat.card_congr (toProd p), Nat.card_prod, Nat.card_prod,
    Nat.card_zmod, Nat.card_zmod]
  ring

/-- Powers in `CH7`: `(x,y,z)ⁿ = (nx, ny, nz + p·T(n)xy)`. -/
theorem pow_formula (a : CH7 p) (n : ℕ) :
    a ^ n = ⟨(n : ZMod p) * a.x, (n : ZMod p) * a.y,
      (n : ZMod (p ^ 2)) * a.z + liftp p (tri p ((n : ZMod p)) * (a.x * a.y))⟩ := by
  induction n with
  | zero =>
    change (1 : CH7 p) = _
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
    · change (0 : ZMod (p ^ 2)) = ((0 : ℕ) : ZMod (p ^ 2)) * a.z +
        liftp p (tri p ((0 : ℕ) : ZMod p) * (a.x * a.y))
      rw [htri, zero_mul, liftp_zero]
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
    · change (n : ZMod (p ^ 2)) * a.z +
          liftp p (tri p ((n : ZMod p)) * (a.x * a.y)) + a.z +
          liftp p (((n : ZMod p) * a.x) * a.y) =
        ((n + 1 : ℕ) : ZMod (p ^ 2)) * a.z +
          liftp p (tri p ((n + 1 : ℕ) : ZMod p) * (a.x * a.y))
      rw [htri]
      have hL : (tri p ((n : ZMod p)) + (n : ZMod p)) * (a.x * a.y) =
          tri p ((n : ZMod p)) * (a.x * a.y) +
            ((n : ZMod p) * a.x) * a.y := by ring
      rw [hL, liftp_add]
      push_cast
      ring

/-- Torsion criterion in `CH7`: `aᵖ = 1 ⟺ z ≡ 0 (mod p)`. -/
theorem pow_p_eq_one_iff (a : CH7 p) :
    a ^ p = 1 ↔ redp p a.z = 0 := by
  have hp0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  have htri : tri p (0 : ZMod p) = 0 := by
    unfold tri
    ring
  have hpow : a ^ p = ⟨0, 0, liftp p (redp p a.z)⟩ := by
    rw [pow_formula]
    ext
    · change ((p : ℕ) : ZMod p) * a.x = 0
      rw [hp0, zero_mul]
    · change ((p : ℕ) : ZMod p) * a.y = 0
      rw [hp0, zero_mul]
    · change ((p : ℕ) : ZMod (p ^ 2)) * a.z +
          liftp p (tri p ((p : ℕ) : ZMod p) * (a.x * a.y)) =
        liftp p (redp p a.z)
      rw [hp0, htri, zero_mul, liftp_zero, add_zero, p_mul_eq_liftp_redp]
  rw [hpow, one_def]
  constructor
  · intro h
    exact liftp_eq_zero_iff.mp (congrArg CH7.z h)
  · intro h
    rw [h, liftp_zero]

variable (p) in
/-- `|Ω₁(CH7)| = p³`. -/
theorem card_omega : Nat.card {a : CH7 p // a ^ p = 1} = p ^ 3 := by
  have hp : p.Prime := Fact.out
  let f : ZMod p × ZMod p × ZMod p → {a : CH7 p // a ^ p = 1} := fun w =>
    ⟨⟨w.1, w.2.1, liftp p w.2.2⟩, by
      rw [pow_p_eq_one_iff]
      exact redp_liftp w.2.2⟩
  let g : {a : CH7 p // a ^ p = 1} → ZMod p × ZMod p × ZMod p := fun a =>
    (a.1.x, a.1.y, ((a.1.z.val / p : ℕ) : ZMod p))
  have hbij : Function.Bijective f := by
    rw [Function.bijective_iff_has_inverse]
    refine ⟨g, fun w => ?_, fun a => ?_⟩
    · change (w.1, w.2.1, (((liftp p w.2.2).val / p : ℕ) : ZMod p)) = w
      rw [liftp_val, Nat.mul_div_cancel_left _
        (Nat.pos_of_ne_zero hp.ne_zero), ZMod.natCast_val, ZMod.cast_id]
    · obtain ⟨a, ha⟩ := a
      have hred : redp p a.z = 0 := (pow_p_eq_one_iff a).mp ha
      refine Subtype.ext ?_
      change (⟨a.x, a.y, liftp p (((a.z.val / p : ℕ) : ZMod p))⟩ : CH7 p) = a
      ext
      · rfl
      · rfl
      · exact liftp_of_redp_zero hred
  rw [← Nat.card_eq_of_bijective f hbij, Nat.card_prod, Nat.card_prod,
    Nat.card_zmod]
  ring

variable (p) in
/-- **Table row (vii), first column**: `C_{p²} ∘ Heis(p)` has exactly
`p² + p + 1` subgroups of order `p`. -/
theorem card_order_p_subgroups_ch7 :
    Nat.card {H : Subgroup (CH7 p) // Nat.card H = p} = p ^ 2 + p + 1 := by
  have h := card_order_p_subgroups_of_omega (CH7 p) 3 (card_omega p)
  rw [h, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  ring

end CH7

end P4

end LeanDring
