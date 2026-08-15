/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P4.Model
import LeanDring.Theory.DRing.SubgroupCount
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Powers in the (xii)/(xiii) model: the `xᵖ` law

The closed form for powers in `P4.Model p d`, leading to
`x ^ p = a^{p(k + d·u)}` where `k = redp x.α` — hence the `p`-torsion
criterion **`xᵖ = 1 ⟺ k + d·u = 0`** (`pow_p_eq_one_iff`), which counts
`Ω₁ = p³` and yields the subgroup-count row `p² + p + 1` of the table
(`card_order_p_subgroups`).

Requires `p ≥ 5`: the vanishing `∑_{j<p} T(j) ≡ 0 (mod p)` is
`p ∣ C(p,3)`, needing `p` coprime to `6`.
-/

namespace LeanDring

namespace P4

namespace Model

open Finset

variable {p : ℕ} [Fact p.Prime] [Fact (Odd p)] {d : ZMod p}

/-- The `n`-th power in the model, closed form. -/
theorem pow_formula (x : Model p d) (n : ℕ) :
    x ^ n =
      ⟨n • x.α +
          liftp p (∑ j ∈ range n,
            tauP p d (redp p x.α) ((j : ZMod p) * x.u)
              ((j : ZMod p) * x.v + tri p (j : ZMod p) * redp p x.α * x.u)) +
          dc d * ∑ j ∈ range n, carryF p ((j : ZMod p) * x.u) x.u,
        (n : ZMod p) * x.u,
        (n : ZMod p) * x.v + tri p (n : ZMod p) * redp p x.α * x.u⟩ := by
  induction n with
  | zero =>
    change (1 : Model p d) = _
    rw [one_def]
    ext
    · change (0 : ZMod (p ^ 2)) = 0 • x.α + liftp p _ + dc d * _
      rw [range_zero, Finset.sum_empty, Finset.sum_empty, zero_smul,
        liftp_zero]
      ring
    · change (0 : ZMod p) = (0 : ℕ) * x.u
      push_cast
      ring
    · change (0 : ZMod p) = (0 : ℕ) * x.v + tri p (0 : ℕ) * redp p x.α * x.u
      have h0 : tri p ((0 : ℕ) : ZMod p) = 0 := by
        unfold tri
        push_cast
        ring
      rw [h0]
      push_cast
      ring
  | succ n ih =>
    rw [pow_succ, ih, mul_def]
    have htri : tri p ((n + 1 : ℕ) : ZMod p) =
        tri p (n : ZMod p) + (n : ZMod p) := by
      push_cast
      rw [tri_add]
      have h1 : tri p (1 : ZMod p) = 0 := by
        unfold tri
        ring
      rw [h1]
      ring
    ext
    · change n • x.α + liftp p _ + dc d * _ + x.α +
          liftp p (tauP p d (redp p x.α) ((n : ZMod p) * x.u)
            ((n : ZMod p) * x.v + tri p (n : ZMod p) * redp p x.α * x.u)) +
          dc d * carryF p ((n : ZMod p) * x.u) x.u = (n + 1) • x.α +
          liftp p _ + dc d * _
      rw [Finset.sum_range_succ, Finset.sum_range_succ (f := fun j =>
        carryF p ((j : ZMod p) * x.u) x.u), liftp_add, succ_nsmul]
      ring
    · change (n : ZMod p) * x.u + x.u = ((n + 1 : ℕ) : ZMod p) * x.u
      push_cast
      ring
    · change (n : ZMod p) * x.v + tri p (n : ZMod p) * redp p x.α * x.u + x.v +
          redp p x.α * ((n : ZMod p) * x.u) =
        ((n + 1 : ℕ) : ZMod p) * x.v +
          tri p ((n + 1 : ℕ) : ZMod p) * redp p x.α * x.u
      rw [htri]
      push_cast
      ring

/-- `∑_{j<p} j ≡ 0 (mod p)` for odd `p`. -/
theorem sum_range_cast_zero :
    (∑ j ∈ range p, ((j : ZMod p))) = 0 := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := Fact.out
  have h2 : (∑ j ∈ range p, j) * 2 = p * (p - 1) := Finset.sum_range_id_mul_two p
  have hdvd : p ∣ ∑ j ∈ range p, j := by
    have hpd2 : p ∣ (∑ j ∈ range p, j) * 2 := h2 ▸ Dvd.intro _ rfl
    have hco : Nat.Coprime p 2 := Nat.coprime_two_right.mpr hodd
    exact hco.dvd_of_dvd_mul_right hpd2
  calc (∑ j ∈ range p, ((j : ZMod p)))
      = ((∑ j ∈ range p, j : ℕ) : ZMod p) := (map_sum (Nat.castRingHom (ZMod p)) id (range p)).symm
    _ = 0 := (CharP.cast_eq_zero_iff (ZMod p) p _).mpr hdvd

/-- `6·∑_{j<n} j² = n(n−1)(2n−1)`. -/
theorem six_mul_sum_range_sq (n : ℕ) :
    6 * ∑ j ∈ range n, j ^ 2 = n * (n - 1) * (2 * n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    rcases n with - | m
    · simp
    · have h1 : m + 1 - 1 = m := rfl
      have h2 : m + 1 + 1 - 1 = m + 1 := rfl
      have h3 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
      have h4 : 2 * (m + 1 + 1) - 1 = 2 * m + 3 := by omega
      rw [h1, h2, h3, h4]
      ring

/-- `∑_{j<p} T(j) ≡ 0 (mod p)` for `p ≥ 5` (this is `p ∣ C(p,3)`). -/
theorem sum_tri_zero (hp5 : 5 ≤ p) :
    (∑ j ∈ range p, tri p ((j : ZMod p))) = 0 := by
  have hp : p.Prime := Fact.out
  have h2u := two_isUnit' (p := p)
  have hinv : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := ZMod.mul_inv_of_unit _ h2u
  have hco : Nat.Coprime p 6 := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    have hle := Nat.le_of_dvd (by norm_num) h
    have hcase : p = 5 ∨ p = 6 := by omega
    rcases hcase with rfl | rfl
    · exact absurd h (by decide)
    · exact absurd hp (by decide)
  have hsq : ((∑ j ∈ range p, j ^ 2 : ℕ) : ZMod p) = 0 := by
    refine (CharP.cast_eq_zero_iff (ZMod p) p _).mpr ?_
    have h6 := six_mul_sum_range_sq p
    have hpd : p ∣ 6 * ∑ j ∈ range p, j ^ 2 := by
      rw [h6]
      exact (dvd_mul_right p (p - 1)).mul_right _
    exact hco.dvd_of_dvd_mul_left hpd
  have hlin : ((∑ j ∈ range p, j : ℕ) : ZMod p) = 0 := by
    have h0 := sum_range_cast_zero (p := p)
    rwa [show (∑ j ∈ range p, ((j : ZMod p))) =
      ((∑ j ∈ range p, j : ℕ) : ZMod p) from
      (map_sum (Nat.castRingHom (ZMod p)) id (range p)).symm] at h0
  have hcastsq : ((∑ j ∈ range p, j ^ 2 : ℕ) : ZMod p) =
      ∑ j ∈ range p, ((j : ZMod p)) ^ 2 :=
    calc ((∑ j ∈ range p, j ^ 2 : ℕ) : ZMod p)
        = ∑ j ∈ range p, ((j ^ 2 : ℕ) : ZMod p) :=
          map_sum (Nat.castRingHom (ZMod p)) (fun j => j ^ 2) (range p)
      _ = ∑ j ∈ range p, ((j : ZMod p)) ^ 2 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          push_cast
          rfl
  have hcastlin : ((∑ j ∈ range p, j : ℕ) : ZMod p) =
      ∑ j ∈ range p, ((j : ZMod p)) :=
    map_sum (Nat.castRingHom (ZMod p)) id (range p)
  have hkey : (2 : ZMod p) * ∑ j ∈ range p, tri p ((j : ZMod p)) =
      ((∑ j ∈ range p, j ^ 2 : ℕ) : ZMod p) -
        ((∑ j ∈ range p, j : ℕ) : ZMod p) := by
    rw [Finset.mul_sum, hcastsq, hcastlin, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold tri
    calc (2 : ZMod p) * ((j : ZMod p) * ((j : ZMod p) - 1) * (2 : ZMod p)⁻¹)
        = ((j : ZMod p) * ((j : ZMod p) - 1)) *
            ((2 : ZMod p) * (2 : ZMod p)⁻¹) := by ring
      _ = (j : ZMod p) ^ 2 - (j : ZMod p) := by rw [hinv]; ring
  have h0 : (2 : ZMod p) * ∑ j ∈ range p, tri p ((j : ZMod p)) = 0 := by
    rw [hkey, hsq, hlin, sub_zero]
  calc (∑ j ∈ range p, tri p ((j : ZMod p)))
      = ((2 : ZMod p)⁻¹ * 2) * ∑ j ∈ range p, tri p ((j : ZMod p)) := by
        rw [mul_comm ((2 : ZMod p)⁻¹) 2, hinv, one_mul]
    _ = (2 : ZMod p)⁻¹ * ((2 : ZMod p) * ∑ j ∈ range p, tri p ((j : ZMod p))) := by
        ring
    _ = 0 := by rw [h0, mul_zero]

omit [Fact (Odd p)] in
/-- The carry telescope over a full period:
`∑_{j<p} carryF(j·u, u) = liftp u` (i.e. `p·val u` in `ZMod p²`). -/
theorem sum_carryF (u : ZMod p) :
    ∑ j ∈ range p, carryF p ((j : ZMod p) * u) u = liftp p u := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  -- the natural-number telescope, in addition form (avoids nonlinear guards)
  have haux : ∀ n : ℕ,
      (∑ j ∈ range n, (((j : ZMod p) * u).val + u.val -
          (((j : ZMod p) * u) + u).val)) +
        (((n : ZMod p)) * u).val = n * u.val := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hstep : ((n : ZMod p) * u) + u = (((n + 1 : ℕ) : ZMod p)) * u := by
        push_cast
        ring
      obtain ⟨hle, -⟩ := carry_val ((n : ZMod p) * u) u
      rw [hstep] at hle
      rw [Finset.sum_range_succ, hstep, Nat.succ_mul]
      omega
  -- evaluate at `n = p`: `(p : ZMod p) = 0`
  have hp0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  have hzero : (((p : ZMod p)) * u).val = 0 := by
    rw [hp0, zero_mul, ZMod.val_zero]
  have hsum := haux p
  rw [hzero, Nat.add_zero] at hsum
  -- cast the telescope into `ZMod p²`
  have hcast : ∑ j ∈ range p, carryF p ((j : ZMod p) * u) u =
      ((∑ j ∈ range p, (((j : ZMod p) * u).val + u.val -
        (((j : ZMod p) * u) + u).val) : ℕ) : ZMod (p ^ 2)) :=
    calc ∑ j ∈ range p, carryF p ((j : ZMod p) * u) u
        = ∑ j ∈ range p, (((((j : ZMod p) * u).val + u.val -
            (((j : ZMod p) * u) + u).val : ℕ)) : ZMod (p ^ 2)) := rfl
      _ = ((∑ j ∈ range p, (((j : ZMod p) * u).val + u.val -
            (((j : ZMod p) * u) + u).val) : ℕ) : ZMod (p ^ 2)) :=
        (map_sum (Nat.castRingHom (ZMod (p ^ 2)))
          (fun j : ℕ => (((j : ZMod p) * u).val + u.val -
            (((j : ZMod p) * u) + u).val)) (range p)).symm
  rw [hcast, hsum]
  unfold liftp
  push_cast
  ring

omit [Fact (Odd p)] in
/-- `dc d · liftp x = liftp (d·x)`: the constant `d` passes through the lift. -/
theorem dc_mul_liftp (e x : ZMod p) :
    dc e * liftp p x = liftp p (e * x) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  unfold dc liftp
  have hval : (e * x).val = (e.val * x.val) % p := ZMod.val_mul e x
  have hdiv : e.val * x.val = p * (e.val * x.val / p) + (e * x).val := by
    rw [hval]
    exact (Nat.div_add_mod (e.val * x.val) p).symm
  have hcast : ((e.val * x.val : ℕ) : ZMod (p ^ 2)) =
      (p : ZMod (p ^ 2)) * ((e.val * x.val / p : ℕ) : ZMod (p ^ 2)) +
        (((e * x).val : ℕ) : ZMod (p ^ 2)) := by
    conv_lhs => rw [hdiv]
    push_cast
    ring
  calc (e.val : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) * (x.val : ZMod (p ^ 2)))
      = (p : ZMod (p ^ 2)) * ((e.val * x.val : ℕ) : ZMod (p ^ 2)) := by
        push_cast
        ring
    _ = (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
          ((e.val * x.val / p : ℕ) : ZMod (p ^ 2)) +
        (p : ZMod (p ^ 2)) * (((e * x).val : ℕ) : ZMod (p ^ 2)) := by
        rw [hcast]
        ring
    _ = (p : ZMod (p ^ 2)) * (((e * x).val : ℕ) : ZMod (p ^ 2)) := by
        rw [pow_two_cast_zero, zero_mul, zero_add]

omit [Fact (Odd p)] in
/-- `p·α = liftp (redp α)` in `ZMod p²`. -/
theorem p_mul_eq_liftp_redp (α : ZMod (p ^ 2)) :
    (p : ZMod (p ^ 2)) * α = liftp p (redp p α) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hred : redp p α = ((α.val : ℕ) : ZMod p) := by
    unfold redp
    rw [ZMod.castHom_apply, ← ZMod.natCast_val]
  have hval : (redp p α).val = α.val % p := by
    rw [hred, ZMod.val_natCast]
  have hα : ((α.val : ℕ) : ZMod (p ^ 2)) = α := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  have hdiv : α.val = p * (α.val / p) + α.val % p := (Nat.div_add_mod α.val p).symm
  calc (p : ZMod (p ^ 2)) * α
      = (p : ZMod (p ^ 2)) * ((α.val : ℕ) : ZMod (p ^ 2)) := by rw [hα]
    _ = (p : ZMod (p ^ 2)) * ((p * (α.val / p) + α.val % p : ℕ) : ZMod (p ^ 2)) := by
        rw [← hdiv]
    _ = (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) * ((α.val / p : ℕ) : ZMod (p ^ 2)) +
        (p : ZMod (p ^ 2)) * ((α.val % p : ℕ) : ZMod (p ^ 2)) := by
        push_cast
        ring
    _ = (p : ZMod (p ^ 2)) * ((α.val % p : ℕ) : ZMod (p ^ 2)) := by
        rw [pow_two_cast_zero, zero_mul, zero_add]
    _ = liftp p (redp p α) := by
        unfold liftp
        rw [hval]

omit [Fact (Odd p)] in
/-- `liftp` is injective: `liftp z = 0 ↔ z = 0`. -/
theorem liftp_eq_zero_iff {z : ZMod p} : liftp p z = 0 ↔ z = 0 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  constructor
  · intro h
    unfold liftp at h
    have hcast : ((p * z.val : ℕ) : ZMod (p ^ 2)) = 0 := by
      push_cast
      exact h
    have hdvd : p ^ 2 ∣ p * z.val :=
      (CharP.cast_eq_zero_iff (ZMod (p ^ 2)) (p ^ 2) _).mp hcast
    have hdvd2 : p ∣ z.val := by
      rcases hdvd with ⟨c, hc⟩
      have hpne := hp.ne_zero
      have : z.val = p * c := by
        have h2 : p * z.val = p * (p * c) := by rw [hc]; ring
        exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpne) h2
      exact ⟨c, this⟩
    have hlt : z.val < p := ZMod.val_lt z
    have hzero : z.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd2 hlt
    exact (ZMod.val_eq_zero z).mp hzero
  · rintro rfl
    exact liftp_zero

/-- **The `xᵖ` law** (`p ≥ 5`): in the model,
`(a^α s^u b^v)^p = a^{p·(k + d·u)}` where `k = redp α`. All three sums
vanish or telescope: `∑j ≡ 0`, `∑T(j) ≡ 0` (`p ∣ C(p,3)`), and the carry
telescope contributes exactly `liftp (d·u)`. -/
theorem pow_p (hp5 : 5 ≤ p) (x : Model p d) :
    x ^ p = ⟨liftp p (redp p x.α + d * x.u), 0, 0⟩ := by
  have hp0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  rw [pow_formula]
  set k := redp p x.α with hk
  have htri0 : tri p (0 : ZMod p) = 0 := by
    unfold tri
    ring
  have hsum1 : (∑ j ∈ range p,
      tauP p d k ((j : ZMod p) * x.u)
        ((j : ZMod p) * x.v + tri p (j : ZMod p) * k * x.u)) = 0 := by
    have hcong : ∀ j ∈ range p,
        tauP p d k ((j : ZMod p) * x.u)
          ((j : ZMod p) * x.v + tri p (j : ZMod p) * k * x.u) =
        (j : ZMod p) * (d * k * x.u + k * x.v + tri p k * x.u) +
          tri p (j : ZMod p) * (k * k * x.u) := by
      intro j _
      unfold tauP
      ring
    rw [Finset.sum_congr rfl hcong, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, sum_range_cast_zero,
      sum_tri_zero hp5, zero_mul, zero_mul, add_zero]
  ext
  · change (p : ℕ) • x.α + liftp p _ + dc d * _ = liftp p (k + d * x.u)
    rw [hsum1, liftp_zero, add_zero, sum_carryF, dc_mul_liftp,
      nsmul_eq_mul, p_mul_eq_liftp_redp, ← hk, ← liftp_add]
  · change ((p : ℕ) : ZMod p) * x.u = 0
    rw [hp0, zero_mul]
  · change ((p : ℕ) : ZMod p) * x.v + tri p ((p : ℕ) : ZMod p) * k * x.u = 0
    rw [hp0, htri0]
    ring

/-- **The `p`-torsion criterion**: `xᵖ = 1 ⟺ redp α + d·u = 0`.
This is the linear equation cutting out `Ω₁(G) ≅ (C_p)³`. -/
theorem pow_p_eq_one_iff (hp5 : 5 ≤ p) (x : Model p d) :
    x ^ p = 1 ↔ redp p x.α + d * x.u = 0 := by
  rw [pow_p hp5, one_def]
  constructor
  · intro h
    have hα : liftp p (redp p x.α + d * x.u) = (0 : ZMod (p ^ 2)) :=
      congrArg Model.α h
    exact liftp_eq_zero_iff.mp hα
  · intro h
    rw [h, liftp_zero]

/-! ## Counting `Ω₁`: the solutions of `xᵖ = 1` -/

omit [Fact (Odd p)] in
theorem redp_dc (e : ZMod p) : redp p (dc e) = e := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  unfold dc
  rw [map_natCast, ZMod.natCast_val, ZMod.cast_id]

omit [Fact (Odd p)] in
theorem liftp_val (t : ZMod p) : (liftp p t).val = p * t.val := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have h1 : liftp p t = ((p * t.val : ℕ) : ZMod (p ^ 2)) := by
    unfold liftp
    push_cast
    ring
  rw [h1, ZMod.val_natCast, Nat.mod_eq_of_lt]
  have hlt := ZMod.val_lt t
  calc p * t.val < p * p :=
        mul_lt_mul_of_pos_left hlt (Nat.pos_of_ne_zero hp.ne_zero)
    _ = p ^ 2 := (sq p).symm

omit [Fact (Odd p)] in
/-- Every element of `ker redp` is a lift: explicit division-free witness. -/
theorem liftp_of_redp_zero {γ : ZMod (p ^ 2)} (h : redp p γ = 0) :
    liftp p ((γ.val / p : ℕ) : ZMod p) = γ := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hppos : 0 < p := Nat.pos_of_ne_zero hp.ne_zero
  have hred : redp p γ = ((γ.val : ℕ) : ZMod p) := by
    unfold redp
    rw [ZMod.castHom_apply, ← ZMod.natCast_val]
  have hmod : γ.val % p = 0 := by
    have h0 : ((γ.val : ℕ) : ZMod p) = 0 := hred ▸ h
    have := (CharP.cast_eq_zero_iff (ZMod p) p _).mp h0
    omega
  have hdvd : γ.val = p * (γ.val / p) :=
    (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)).symm
  have hlt : γ.val / p < p :=
    Nat.div_lt_of_lt_mul (calc γ.val < p ^ 2 := ZMod.val_lt γ
      _ = p * p := sq p)
  have hvalcast : (((γ.val / p : ℕ) : ZMod p)).val = γ.val / p := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  have hγcast : ((γ.val : ℕ) : ZMod (p ^ 2)) = γ := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  unfold liftp
  rw [hvalcast]
  calc (p : ZMod (p ^ 2)) * ((γ.val / p : ℕ) : ZMod (p ^ 2))
      = ((p * (γ.val / p) : ℕ) : ZMod (p ^ 2)) := by push_cast; ring
    _ = ((γ.val : ℕ) : ZMod (p ^ 2)) := by rw [← hdvd]
    _ = γ := hγcast

/-- **`|Ω₁| = p³`**: the `p`-torsion of the model has exactly `p³` elements —
the solution set of the linear equation `redp α + d·u = 0`, parametrized
freely by `(t, u, v)`. -/
theorem card_omega1 (hp5 : 5 ≤ p) :
    Nat.card {x : Model p d // x ^ p = 1} = p ^ 3 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  -- the parametrization
  have hconstraint : ∀ w : ZMod p × ZMod p × ZMod p,
      ((⟨dc (-(d * w.2.1)) + liftp p w.1, w.2.1, w.2.2⟩ : Model p d)) ^ p = 1 := by
    intro w
    rw [pow_p_eq_one_iff hp5]
    change redp p (dc (-(d * w.2.1)) + liftp p w.1) + d * w.2.1 = 0
    rw [map_add, redp_dc, redp_liftp, add_zero]
    ring
  let f : ZMod p × ZMod p × ZMod p → {x : Model p d // x ^ p = 1} :=
    fun w => ⟨⟨dc (-(d * w.2.1)) + liftp p w.1, w.2.1, w.2.2⟩, hconstraint w⟩
  let g : {x : Model p d // x ^ p = 1} → ZMod p × ZMod p × ZMod p :=
    fun x => ((((x.1.α - dc (-(d * x.1.u))).val / p : ℕ) : ZMod p), x.1.u, x.1.v)
  have hbij : Function.Bijective f := by
    rw [Function.bijective_iff_has_inverse]
    refine ⟨g, fun w => ?_, fun x => ?_⟩
    · -- g (f w) = w
      change ((((dc (-(d * w.2.1)) + liftp p w.1 - dc (-(d * w.2.1))).val / p : ℕ) :
        ZMod p), w.2.1, w.2.2) = w
      have hγ : dc (-(d * w.2.1)) + liftp p w.1 - dc (-(d * w.2.1)) =
          liftp p w.1 := by ring
      rw [hγ, liftp_val, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp.ne_zero)]
      rw [ZMod.natCast_val, ZMod.cast_id]
    · -- f (g x) = x
      obtain ⟨x, hx⟩ := x
      have hlin : redp p x.α + d * x.u = 0 := (pow_p_eq_one_iff hp5 x).mp hx
      have hker : redp p (x.α - dc (-(d * x.u))) = 0 := by
        rw [map_sub, redp_dc]
        linear_combination hlin
      have hα : liftp p (((x.α - dc (-(d * x.u))).val / p : ℕ) : ZMod p) =
          x.α - dc (-(d * x.u)) := liftp_of_redp_zero hker
      refine Subtype.ext ?_
      change (⟨dc (-(d * x.u)) + liftp p _, x.u, x.v⟩ : Model p d) = x
      ext
      · change dc (-(d * x.u)) + liftp p (((x.α - dc (-(d * x.u))).val / p : ℕ) :
          ZMod p) = x.α
        rw [hα]
        ring
      · rfl
      · rfl
  have hcard := Nat.card_eq_of_bijective f hbij
  rw [← hcard, Nat.card_prod, Nat.card_prod, Nat.card_zmod]
  ring

/-- **The table row**: the model has exactly `p² + p + 1` subgroups of
order `p` — row (xii)/(xiii) of the corrected [GJG10] table, as a theorem
for every prime `p ≥ 5` and every parameter `d`. -/
theorem card_order_p_subgroups (hp5 : 5 ≤ p) :
    Nat.card {H : Subgroup (Model p d) // Nat.card H = p} = p ^ 2 + p + 1 := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fintype (Model p d) := Fintype.ofEquiv _ (toProd (p := p) (d := d)).symm
  -- #{x : xᵖ = 1} = p³ as a Finset count
  have hS1 : (univ.filter fun x : Model p d => x ^ p = 1).card = p ^ 3 := by
    have h1 := card_omega1 (d := d) hp5
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h1
    exact h1
  -- order-p elements = p-torsion minus identity
  have hS2 : (univ.filter fun x : Model p d => orderOf x = p) =
      (univ.filter fun x : Model p d => x ^ p = 1).erase 1 := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · intro ho
      constructor
      · intro h1
        rw [h1, orderOf_one] at ho
        omega
      · have hpow := pow_orderOf_eq_one x
        rw [ho] at hpow
        exact hpow
    · rintro ⟨h1, hpow⟩
      have hdvd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hpow
      rcases (Nat.dvd_prime hp).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) h1
      · exact h
  have hone : (1 : Model p d) ∈ univ.filter fun x : Model p d => x ^ p = 1 := by
    simp
  have hS2card : (univ.filter fun x : Model p d => orderOf x = p).card =
      p ^ 3 - 1 := by
    rw [hS2, Finset.card_erase_of_mem hone, hS1]
  -- double counting
  have hdouble := card_orderOf_eq_prime (G := Model p d) hp
  rw [hS2card] at hdouble
  -- arithmetic: p³ − 1 = (p² + p + 1)(p − 1), cancel p − 1
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have h3 : (q + 1) ^ 3 = q ^ 3 + 3 * q ^ 2 + 3 * q + 1 := by ring
  have h2 : (q + 1) ^ 2 = q ^ 2 + 2 * q + 1 := by ring
  have hfact : (q + 1) ^ 3 - 1 = (q ^ 2 + 3 * q + 3) * q := by
    have hexp : (q ^ 2 + 3 * q + 3) * q = q ^ 3 + 3 * q ^ 2 + 3 * q := by ring
    omega
  have hq1 : q + 1 - 1 = q := by omega
  rw [hfact, hq1] at hdouble
  have hqpos : 0 < q := by omega
  have hN := Nat.eq_of_mul_eq_mul_right hqpos hdouble.symm
  omega

end Model

end P4

end LeanDring
