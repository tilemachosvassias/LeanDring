/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P4.ColTwo
import LeanDring.Theory.DRing.BridgeCounts

/-!
# The abelian quintet: subgroup counts for the five abelian `p⁴` groups

Models `A4 = C_{p⁴}`, `A31 = C_{p³}×C_p`, `A22 = C_{p²}×C_{p²}`,
`A211 = C_{p²}×C_p×C_p`, `A1111 = (C_p)⁴` as `Multiplicative` groups of
`ZMod`-products.

Column 1 (order-`p` subgroups) from `Ω₁` counts via the generic brick:
`1`, `p+1`, `p+1`, `p²+p+1`, `p³+p²+p+1`. The single tie —
`A31` vs `A22` — is separated by column 2 (`p+1` vs `p²+p+1`), computed
by the `M6`/`M8` pattern (`card_p2_subgroups`, `card_orderOf_eq_prime_sq`).
-/

namespace LeanDring

namespace P4

open Finset

variable {p : ℕ} [Fact p.Prime] [Fact (Odd p)]

/-! ## `p`-torsion of `ZMod pᵏ` -/

variable (p) in
/-- The top-level lift `ZMod p → ZMod pᵏ`, `x ↦ p^{k-1}·x`. -/
def liftTop (k : ℕ) (x : ZMod p) : ZMod (p ^ k) :=
  (p : ZMod (p ^ k)) ^ (k - 1) * (x.val : ZMod (p ^ k))

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem liftTop_p_torsion {k : ℕ} (hk : 1 ≤ k) (x : ZMod p) :
    (p : ZMod (p ^ k)) * liftTop p k x = 0 := by
  unfold liftTop
  have h1 : (p : ZMod (p ^ k)) * ((p : ZMod (p ^ k)) ^ (k - 1) *
      (x.val : ZMod (p ^ k))) =
      (p : ZMod (p ^ k)) ^ k * (x.val : ZMod (p ^ k)) := by
    calc (p : ZMod (p ^ k)) * ((p : ZMod (p ^ k)) ^ (k - 1) *
        (x.val : ZMod (p ^ k)))
        = ((p : ZMod (p ^ k)) ^ (k - 1) * (p : ZMod (p ^ k))) *
          (x.val : ZMod (p ^ k)) := by ring
      _ = (p : ZMod (p ^ k)) ^ (k - 1 + 1) * (x.val : ZMod (p ^ k)) := by
          rw [← pow_succ]
      _ = (p : ZMod (p ^ k)) ^ k * (x.val : ZMod (p ^ k)) := by
          congr 2
          omega
  rw [h1]
  have h2 : ((p ^ k : ℕ) : ZMod (p ^ k)) = 0 := ZMod.natCast_self _
  have h3 : (p : ZMod (p ^ k)) ^ k = 0 := by
    exact_mod_cast h2
  rw [h3, zero_mul]

omit [Fact (Odd p)] in
theorem liftTop_val {k : ℕ} (hk : 1 ≤ k) (x : ZMod p) :
    (liftTop p k x).val = p ^ (k - 1) * x.val := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  have h1 : liftTop p k x = ((p ^ (k - 1) * x.val : ℕ) : ZMod (p ^ k)) := by
    unfold liftTop
    push_cast
    ring
  rw [h1, ZMod.val_natCast, Nat.mod_eq_of_lt]
  have hlt := ZMod.val_lt x
  calc p ^ (k - 1) * x.val < p ^ (k - 1) * p :=
        mul_lt_mul_of_pos_left hlt (pow_pos hp.pos _)
    _ = p ^ k := by
      rw [← pow_succ]
      congr 1
      omega

omit [Fact (Odd p)] in
/-- Solutions of `p·a = 0` in `ZMod pᵏ` are exactly the lifts. -/
theorem liftTop_of_p_mul_zero {k : ℕ} (hk : 1 ≤ k) {a : ZMod (p ^ k)}
    (h : (p : ZMod (p ^ k)) * a = 0) :
    liftTop p k (((a.val / p ^ (k - 1) : ℕ) : ZMod p)) = a := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  have hppos : 0 < p := hp.pos
  have ha : ((a.val : ℕ) : ZMod (p ^ k)) = a := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  have hcast : ((p * a.val : ℕ) : ZMod (p ^ k)) = 0 := by
    push_cast
    rw [ha]
    exact h
  have hdvdk : p ^ k ∣ p * a.val :=
    (CharP.cast_eq_zero_iff (ZMod (p ^ k)) (p ^ k) _).mp hcast
  have hdvd : p ^ (k - 1) ∣ a.val := by
    rcases hdvdk with ⟨c, hc⟩
    have hc2 : p * a.val = p * (p ^ (k - 1) * c) := by
      rw [hc]
      have : p ^ k = p * p ^ (k - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [this]
      ring
    exact ⟨c, Nat.eq_of_mul_eq_mul_left hppos hc2⟩
  have hdiv : a.val = p ^ (k - 1) * (a.val / p ^ (k - 1)) :=
    (Nat.mul_div_cancel' hdvd).symm
  have hlt : a.val / p ^ (k - 1) < p := by
    have hv : a.val < p ^ k := ZMod.val_lt a
    refine Nat.div_lt_of_lt_mul ?_
    calc a.val < p ^ k := hv
      _ = p ^ (k - 1) * p := by
        rw [← pow_succ]
        congr 1
        omega
  have hvalcast : ((((a.val / p ^ (k - 1) : ℕ) : ZMod p)).val) =
      a.val / p ^ (k - 1) := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  unfold liftTop
  rw [hvalcast]
  calc (p : ZMod (p ^ k)) ^ (k - 1) *
      ((a.val / p ^ (k - 1) : ℕ) : ZMod (p ^ k))
      = ((p ^ (k - 1) * (a.val / p ^ (k - 1)) : ℕ) : ZMod (p ^ k)) := by
        push_cast
        ring
    _ = ((a.val : ℕ) : ZMod (p ^ k)) := by rw [← hdiv]
    _ = a := ha

omit [Fact (Odd p)] in
/-- `#{a : ZMod pᵏ | p·a = 0} = p`. -/
theorem card_p_torsion_zmod {k : ℕ} (hk : 1 ≤ k) :
    Nat.card {a : ZMod (p ^ k) // (p : ZMod (p ^ k)) * a = 0} = p := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let f : ZMod p → {a : ZMod (p ^ k) // (p : ZMod (p ^ k)) * a = 0} :=
    fun x => ⟨liftTop p k x, liftTop_p_torsion hk x⟩
  have hbij : Function.Bijective f := by
    rw [Function.bijective_iff_has_inverse]
    refine ⟨fun a => (((a.1.val / p ^ (k - 1) : ℕ) : ZMod p)),
      fun x => ?_, fun a => ?_⟩
    · change ((((liftTop p k x).val / p ^ (k - 1) : ℕ)) : ZMod p) = x
      rw [liftTop_val hk, Nat.mul_div_cancel_left _ (pow_pos hp.pos _),
        ZMod.natCast_val, ZMod.cast_id]
    · exact Subtype.ext (liftTop_of_p_mul_zero hk a.2)
  rw [← Nat.card_eq_of_bijective f hbij, Nat.card_zmod]

/-! ## Torsion counting helpers -/

theorem mult_pow_eq_one_iff {γ : Type*} [AddGroup γ]
    (x : Multiplicative γ) (n : ℕ) :
    x ^ n = 1 ↔ n • x.toAdd = 0 := by
  have h : x ^ n = Multiplicative.ofAdd (n • x.toAdd) := by
    calc x ^ n = (Multiplicative.ofAdd x.toAdd) ^ n := rfl
      _ = Multiplicative.ofAdd (n • x.toAdd) := by rw [← ofAdd_nsmul]
  rw [h]
  constructor
  · intro h1
    simpa using congrArg Multiplicative.toAdd h1
  · intro h1
    rw [h1]
    rfl

theorem card_pow_torsion_mult {γ : Type*} [AddCommGroup γ] (n : ℕ) :
    Nat.card {x : Multiplicative γ // x ^ n = 1} =
      Nat.card {c : γ // n • c = 0} :=
  Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd
    (fun x => mult_pow_eq_one_iff x n))

theorem card_smul_torsion_prod {α β : Type*} [AddMonoid α] [AddMonoid β]
    (n : ℕ) :
    Nat.card {c : α × β // n • c = 0} =
      Nat.card {a : α // n • a = 0} * Nat.card {b : β // n • b = 0} := by
  have hsplit : ∀ c : α × β, n • c = 0 ↔ (n • c.1 = 0 ∧ n • c.2 = 0) := by
    intro c
    rw [Prod.ext_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight hsplit),
    Nat.card_congr (Equiv.subtypeProdEquivProd
      (p := fun a : α => n • a = 0) (q := fun b : β => n • b = 0)),
    Nat.card_prod]

omit [Fact (Odd p)] in
/-- `n·-` torsion in `ZMod pᵏ` with `n = p`, `smul` form. -/
theorem card_p_smul_torsion_zmod {k : ℕ} (hk : 1 ≤ k) :
    Nat.card {a : ZMod (p ^ k) // p • a = 0} = p := by
  refine Eq.trans (Nat.card_congr
    (Equiv.subtypeEquivRight fun a => ?_)) (card_p_torsion_zmod hk)
  rw [nsmul_eq_mul]

omit [Fact (Odd p)] in
/-- Everything in `ZMod p` is `p`-torsion. -/
theorem card_p_smul_torsion_zmodp :
    Nat.card {a : ZMod p // p • a = 0} = p := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hall : ∀ a : ZMod p, p • a = 0 := by
    intro a
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), Nat.card_zmod]

/-! ## The five abelian groups and their `Ω₁` -/

variable (p) in
/-- `C_{p⁴}`. -/
abbrev A4 := Multiplicative (ZMod (p ^ 4))

variable (p) in
/-- `C_{p³} × C_p`. -/
abbrev A31 := Multiplicative (ZMod (p ^ 3) × ZMod p)

variable (p) in
/-- `C_{p²} × C_{p²}`. -/
abbrev A22 := Multiplicative (ZMod (p ^ 2) × ZMod (p ^ 2))

variable (p) in
/-- `C_{p²} × C_p × C_p`. -/
abbrev A211 := Multiplicative (ZMod (p ^ 2) × ZMod p × ZMod p)

variable (p) in
/-- `(C_p)⁴`. -/
abbrev A1111 := Multiplicative (ZMod p × ZMod p × ZMod p × ZMod p)

variable (p) in
omit [Fact (Odd p)] in
theorem card_omega1_a4 : Nat.card {x : A4 p // x ^ p = 1} = p := by
  rw [card_pow_torsion_mult, card_p_smul_torsion_zmod (by norm_num : 1 ≤ 4)]

variable (p) in
omit [Fact (Odd p)] in
theorem card_omega1_a31 : Nat.card {x : A31 p // x ^ p = 1} = p ^ 2 := by
  rw [card_pow_torsion_mult, card_smul_torsion_prod,
    card_p_smul_torsion_zmod (by norm_num : 1 ≤ 3),
    card_p_smul_torsion_zmodp]
  ring

variable (p) in
omit [Fact (Odd p)] in
theorem card_omega1_a22 : Nat.card {x : A22 p // x ^ p = 1} = p ^ 2 := by
  rw [card_pow_torsion_mult, card_smul_torsion_prod,
    card_p_smul_torsion_zmod (by norm_num : 1 ≤ 2)]
  ring

variable (p) in
omit [Fact (Odd p)] in
theorem card_omega1_a211 : Nat.card {x : A211 p // x ^ p = 1} = p ^ 3 := by
  rw [card_pow_torsion_mult, card_smul_torsion_prod,
    card_smul_torsion_prod, card_p_smul_torsion_zmod (by norm_num : 1 ≤ 2),
    card_p_smul_torsion_zmodp]
  ring

variable (p) in
omit [Fact (Odd p)] in
theorem card_omega1_a1111 :
    Nat.card {x : A1111 p // x ^ p = 1} = p ^ 4 := by
  rw [card_pow_torsion_mult, card_smul_torsion_prod,
    card_smul_torsion_prod, card_smul_torsion_prod,
    card_p_smul_torsion_zmodp]
  ring

/-! ## Column 1 for the quintet -/

variable (p) in
omit [Fact (Odd p)] in
theorem card_order_p_subgroups_a4 :
    Nat.card {H : Subgroup (A4 p) // Nat.card H = p} = 1 := by
  have h := card_order_p_subgroups_of_omega (A4 p) 1
    (by rw [card_omega1_a4, pow_one])
  rw [h, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

variable (p) in
omit [Fact (Odd p)] in
theorem card_order_p_subgroups_a31 :
    Nat.card {H : Subgroup (A31 p) // Nat.card H = p} = p + 1 := by
  have h := card_order_p_subgroups_of_omega (A31 p) 2 (card_omega1_a31 p)
  rw [h, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  ring

variable (p) in
omit [Fact (Odd p)] in
theorem card_order_p_subgroups_a22 :
    Nat.card {H : Subgroup (A22 p) // Nat.card H = p} = p + 1 := by
  have h := card_order_p_subgroups_of_omega (A22 p) 2 (card_omega1_a22 p)
  rw [h, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  ring

variable (p) in
omit [Fact (Odd p)] in
theorem card_order_p_subgroups_a211 :
    Nat.card {H : Subgroup (A211 p) // Nat.card H = p} =
      p ^ 2 + p + 1 := by
  have h := card_order_p_subgroups_of_omega (A211 p) 3 (card_omega1_a211 p)
  rw [h, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  ring

variable (p) in
omit [Fact (Odd p)] in
theorem card_order_p_subgroups_a1111 :
    Nat.card {H : Subgroup (A1111 p) // Nat.card H = p} =
      p ^ 3 + p ^ 2 + p + 1 := by
  have h := card_order_p_subgroups_of_omega (A1111 p) 4
    (card_omega1_a1111 p)
  rw [h, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-! ## Column 2 for the tie `A31` vs `A22` -/

omit [Fact (Odd p)] in
/-- `p²`-torsion of `ZMod p³` has `p²` elements (the `lift23`-image). -/
theorem card_p2_smul_torsion_zmod3 :
    Nat.card {a : ZMod (p ^ 3) // p ^ 2 • a = 0} = p ^ 2 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hiff : ∀ a : ZMod (p ^ 3), p ^ 2 • a = 0 ↔
      (p : ZMod (p ^ 3)) ^ 2 * a = 0 := by
    intro a
    rw [nsmul_eq_mul]
    push_cast
    rfl
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
  let f : ZMod (p ^ 2) → {a : ZMod (p ^ 3) //
      (p : ZMod (p ^ 3)) ^ 2 * a = 0} :=
    fun t => ⟨lift23 p t, sq_mul_lift23 t⟩
  have hbij : Function.Bijective f := by
    rw [Function.bijective_iff_has_inverse]
    refine ⟨fun a => (((a.1.val / p : ℕ) : ZMod (p ^ 2))),
      fun t => ?_, fun a => ?_⟩
    · change ((((lift23 p t).val / p : ℕ)) : ZMod (p ^ 2)) = t
      rw [lift23_val, Nat.mul_div_cancel_left _ hp.pos,
        ZMod.natCast_val, ZMod.cast_id]
    · exact Subtype.ext (lift23_of_sq_mul_zero a.2)
  rw [← Nat.card_eq_of_bijective f hbij, Nat.card_zmod]

omit [Fact (Odd p)] in
/-- Everything in `ZMod p²` is `p²`-torsion. -/
theorem card_p2_smul_torsion_zmod2 :
    Nat.card {a : ZMod (p ^ 2) // p ^ 2 • a = 0} = p ^ 2 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hall : ∀ a : ZMod (p ^ 2), p ^ 2 • a = 0 := by
    intro a
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), Nat.card_zmod]

omit [Fact (Odd p)] in
/-- Everything in `ZMod p` is `p²`-torsion. -/
theorem card_p2_smul_torsion_zmodp :
    Nat.card {a : ZMod p // p ^ 2 • a = 0} = p := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hall : ∀ a : ZMod p, p ^ 2 • a = 0 := by
    intro a
    rw [nsmul_eq_mul]
    have h0 : ((p ^ 2 : ℕ) : ZMod p) = 0 := by
      rw [CharP.cast_eq_zero_iff (ZMod p) p]
      exact dvd_pow_self p two_ne_zero
    rw [h0, zero_mul]
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), Nat.card_zmod]

variable (p) in
omit [Fact (Odd p)] in
theorem card_omega2_a31 :
    Nat.card {x : A31 p // x ^ p ^ 2 = 1} = p ^ 3 := by
  rw [card_pow_torsion_mult, card_smul_torsion_prod,
    card_p2_smul_torsion_zmod3, card_p2_smul_torsion_zmodp]
  ring

variable (p) in
omit [Fact (Odd p)] in
theorem card_omega2_a22 :
    Nat.card {x : A22 p // x ^ p ^ 2 = 1} = p ^ 4 := by
  rw [card_pow_torsion_mult, card_smul_torsion_prod,
    card_p2_smul_torsion_zmod2]
  ring

variable (p) in
omit [Fact (Odd p)] in
theorem card_omega2_a1111 :
    Nat.card {x : A1111 p // x ^ (p ^ 2) = 1} = p ^ 4 := by
  rw [card_pow_torsion_mult, card_smul_torsion_prod,
    card_smul_torsion_prod, card_smul_torsion_prod]
  repeat rw [card_p2_smul_torsion_zmodp]
  ring

variable (p) in
def lift24 (x : ZMod (p ^ 2)) : ZMod (p ^ 4) :=
  (p : ZMod (p ^ 4)) ^ 2 * (x.val : ZMod (p ^ 4))

omit [Fact (Odd p)] in
theorem lift24_val (t : ZMod (p ^ 2)) : (lift24 p t).val = p ^ 2 * t.val := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  haveI : NeZero (p ^ 4) := ⟨pow_ne_zero 4 hp.ne_zero⟩
  have h1 : lift24 p t = ((p ^ 2 * t.val : ℕ) : ZMod (p ^ 4)) := by
    unfold lift24
    push_cast
    ring
  rw [h1, ZMod.val_natCast, Nat.mod_eq_of_lt]
  have hlt := ZMod.val_lt t
  calc p ^ 2 * t.val < p ^ 2 * p ^ 2 :=
        mul_lt_mul_of_pos_left hlt (pow_pos (Nat.pos_of_ne_zero hp.ne_zero) 2)
    _ = p ^ 4 := by ring

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem sq_mul_lift24 (t : ZMod (p ^ 2)) :
    (p : ZMod (p ^ 4)) ^ 2 * lift24 p t = 0 := by
  unfold lift24
  calc (p : ZMod (p ^ 4)) ^ 2 * ((p : ZMod (p ^ 4)) ^ 2 * (t.val : ZMod (p ^ 4)))
      = (p : ZMod (p ^ 4)) ^ 4 * (t.val : ZMod (p ^ 4)) := by ring
    _ = 0 := by
      have h : (p : ZMod (p ^ 4)) ^ 4 = 0 := by
        calc (p : ZMod (p ^ 4)) ^ 4 = ((p ^ 4 : ℕ) : ZMod (p ^ 4)) := by push_cast; rfl
          _ = 0 := ZMod.natCast_self _
      rw [h, zero_mul]

omit [Fact (Odd p)] in
theorem lift24_of_sq_mul_zero {α : ZMod (p ^ 4)}
    (h : (p : ZMod (p ^ 4)) ^ 2 * α = 0) :
    lift24 p (((α.val / p ^ 2 : ℕ) : ZMod (p ^ 2))) = α := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  haveI : NeZero (p ^ 4) := ⟨pow_ne_zero 4 hp.ne_zero⟩
  have hppos : 0 < p := Nat.pos_of_ne_zero hp.ne_zero
  have hpos2 : 0 < p ^ 2 := pow_pos hppos 2
  have hα : ((α.val : ℕ) : ZMod (p ^ 4)) = α := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  have hcast : ((p ^ 2 * α.val : ℕ) : ZMod (p ^ 4)) = 0 := by
    push_cast
    rw [hα]
    exact h
  have hdvd4 : p ^ 4 ∣ p ^ 2 * α.val :=
    (CharP.cast_eq_zero_iff (ZMod (p ^ 4)) (p ^ 4) _).mp hcast
  have hdvd2 : p ^ 2 ∣ α.val := by
    rcases hdvd4 with ⟨c, hc⟩
    have hc2 : p ^ 2 * α.val = p ^ 2 * (p ^ 2 * c) := by
      rw [hc]
      ring
    exact ⟨c, Nat.eq_of_mul_eq_mul_left hpos2 hc2⟩
  have hdiv : α.val = p ^ 2 * (α.val / p ^ 2) := (Nat.mul_div_cancel' hdvd2).symm
  have hlt : α.val / p ^ 2 < p ^ 2 := by
    have hv : α.val < p ^ 4 := ZMod.val_lt α
    refine Nat.div_lt_of_lt_mul ?_
    calc α.val < p ^ 4 := hv
      _ = p ^ 2 * p ^ 2 := by ring
  have hvalcast : ((((α.val / p ^ 2 : ℕ) : ZMod (p ^ 2))).val) = α.val / p ^ 2 := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  unfold lift24
  rw [hvalcast]
  calc (p : ZMod (p ^ 4)) ^ 2 * ((α.val / p ^ 2 : ℕ) : ZMod (p ^ 4))
      = ((p ^ 2 * (α.val / p ^ 2) : ℕ) : ZMod (p ^ 4)) := by
        push_cast
        ring
    _ = ((α.val : ℕ) : ZMod (p ^ 4)) := by rw [← hdiv]
    _ = α := hα

omit [Fact (Odd p)] in
theorem card_p2_smul_torsion_zmod4 :
    Nat.card {a : ZMod (p ^ 4) // p ^ 2 • a = 0} = p ^ 2 := by
  have hp : p.Prime := Fact.out
  have hiff : ∀ a : ZMod (p ^ 4), p ^ 2 • a = 0 ↔
      (p : ZMod (p ^ 4)) ^ 2 * a = 0 := by
    intro a
    rw [nsmul_eq_mul]
    push_cast
    rfl
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
  let f : ZMod (p ^ 2) → {a : ZMod (p ^ 4) //
      (p : ZMod (p ^ 4)) ^ 2 * a = 0} :=
    fun t => ⟨lift24 p t, sq_mul_lift24 t⟩
  have hbij : Function.Bijective f := by
    rw [Function.bijective_iff_has_inverse]
    refine ⟨fun a => (((a.1.val / p ^ 2 : ℕ) : ZMod (p ^ 2))),
      fun t => ?_, fun a => ?_⟩
    · change ((((lift24 p t).val / p ^ 2 : ℕ)) : ZMod (p ^ 2)) = t
      have hppos : 0 < p := Nat.pos_of_ne_zero hp.ne_zero
      have hpos2 : 0 < p ^ 2 := pow_pos hppos 2
      rw [lift24_val, Nat.mul_div_cancel_left _ hpos2,
        ZMod.natCast_val, ZMod.cast_id]
    · exact Subtype.ext (lift24_of_sq_mul_zero a.2)
  rw [← Nat.card_eq_of_bijective f hbij, Nat.card_zmod]

variable (p) in
omit [Fact (Odd p)] in
theorem card_omega2_a4 :
    Nat.card {x : A4 p // x ^ (p ^ 2) = 1} = p ^ 2 := by
  rw [card_pow_torsion_mult, card_p2_smul_torsion_zmod4]

/-- The `n`-torsion subgroup of a commutative group. -/
def pTorsion (G : Type*) [CommGroup G] (n : ℕ) : Subgroup G where
  carrier := {x | x ^ n = 1}
  one_mem' := one_pow n
  mul_mem' := by
    intro a b ha hb
    rw [Set.mem_setOf_eq] at ha hb ⊢
    rw [mul_pow, ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    rw [Set.mem_setOf_eq] at ha ⊢
    rw [inv_pow, ha, inv_one]

theorem mem_pTorsion {G : Type*} [CommGroup G] {n : ℕ} {x : G} :
    x ∈ pTorsion G n ↔ x ^ n = 1 := Iff.rfl

variable (p) in
omit [Fact (Odd p)] in
theorem card_order_p2_subgroups_a31 :
    Nat.card {H : Subgroup (A31 p) // Nat.card H = p ^ 2} = p + 1 := by
  classical
  have hp : p.Prime := Fact.out
  have hΩ1 : (univ.filter fun x : A31 p => x ^ p = 1).card = p ^ 2 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact card_omega1_a31 p
  have hΩ2 : (univ.filter fun x : A31 p => x ^ p ^ 2 = 1).card = p ^ 3 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact card_omega2_a31 p
  have hcount : (univ.filter fun x : A31 p => orderOf x = p ^ 2).card =
      p ^ 3 - p ^ 2 := by
    rw [card_orderOf_sq_sub, hΩ1, hΩ2]
  have hcyc := card_orderOf_eq_prime_sq (G := A31 p) (p := p)
  rw [hcount] at hcyc
  have harith : p ^ 3 - p ^ 2 = p * (p ^ 2 - p) := by
    rw [Nat.mul_sub]
    ring_nf
  rw [harith] at hcyc
  have hpos : 0 < p ^ 2 - p := by
    have h1 := hp.one_lt
    have h2 : p < p ^ 2 := by nlinarith
    omega
  have hN : Nat.card {H : Subgroup (A31 p) //
      Nat.card H = p ^ 2 ∧ IsCyclic H} = p :=
    (Nat.eq_of_mul_eq_mul_right hpos hcyc).symm
  have hW : Nat.card (pTorsion (A31 p) p) = p ^ 2 :=
    (Nat.card_congr (Equiv.subtypeEquivRight fun x =>
      mem_pTorsion)).trans (card_omega1_a31 p)
  rw [card_p2_subgroups (pTorsion (A31 p) p) hW
    (fun x => mem_pTorsion.symm), hN]

variable (p) in
theorem card_order_p2_subgroups_a22 :
    Nat.card {H : Subgroup (A22 p) // Nat.card H = p ^ 2} =
      p ^ 2 + p + 1 := by
  classical
  have hp : p.Prime := Fact.out
  have hΩ1 : (univ.filter fun x : A22 p => x ^ p = 1).card = p ^ 2 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact card_omega1_a22 p
  have hΩ2 : (univ.filter fun x : A22 p => x ^ p ^ 2 = 1).card = p ^ 4 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact card_omega2_a22 p
  have hcount : (univ.filter fun x : A22 p => orderOf x = p ^ 2).card =
      p ^ 4 - p ^ 2 := by
    rw [card_orderOf_sq_sub, hΩ1, hΩ2]
  have hcyc := card_orderOf_eq_prime_sq (G := A22 p) (p := p)
  rw [hcount] at hcyc
  have harith : p ^ 4 - p ^ 2 = (p ^ 2 + p) * (p ^ 2 - p) := by
    have h1 := hp.one_lt
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    have h4 : (q + 1) ^ 4 = q ^ 4 + 4 * q ^ 3 + 6 * q ^ 2 + 4 * q + 1 := by
      ring
    have h2 : (q + 1) ^ 2 = q ^ 2 + 2 * q + 1 := by ring
    have hrhs : ((q + 1) ^ 2 + (q + 1)) * ((q + 1) ^ 2 - (q + 1)) =
        ((q + 1) ^ 2 + (q + 1)) * (q ^ 2 + q) := by
      congr 1
      omega
    rw [hrhs]
    have hexp : ((q + 1) ^ 2 + (q + 1)) * (q ^ 2 + q) =
        q ^ 4 + 4 * q ^ 3 + 5 * q ^ 2 + 2 * q := by
      ring
    omega
  rw [harith] at hcyc
  have hpos : 0 < p ^ 2 - p := by
    have h1 := hp.one_lt
    have h2 : p < p ^ 2 := by nlinarith
    omega
  have hN : Nat.card {H : Subgroup (A22 p) //
      Nat.card H = p ^ 2 ∧ IsCyclic H} = p ^ 2 + p :=
    (Nat.eq_of_mul_eq_mul_right hpos hcyc).symm
  have hW : Nat.card (pTorsion (A22 p) p) = p ^ 2 :=
    (Nat.card_congr (Equiv.subtypeEquivRight fun x =>
      mem_pTorsion)).trans (card_omega1_a22 p)
  rw [card_p2_subgroups (pTorsion (A22 p) p) hW
    (fun x => mem_pTorsion.symm), hN]

/-! ## The quintet is pairwise species-table non-isomorphic -/

open DRing

variable (p) in
/-- **The tie-breaker**: `C_{p³}×C_p` and `C_{p²}×C_{p²}` have
non-isomorphic species tables. -/
theorem isEmpty_tableIso_a31_a22 :
    IsEmpty (SpeciesTableIso (A31 p) (A22 p)) := by
  constructor
  intro T
  have h := T.card_subgroups_eq (p ^ 2)
  rw [card_order_p2_subgroups_a31, card_order_p2_subgroups_a22] at h
  have hpos : 0 < p ^ 2 := pow_pos (Fact.out : p.Prime).pos 2
  omega

end P4

end LeanDring
