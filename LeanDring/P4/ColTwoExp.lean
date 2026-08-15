/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P4.PairCount
import LeanDring.P4.ExpModels

/-!
# Column 2 for the exponent-`p` groups (xiv) and (xv)

Centralizer counting feeding the commuting-pair brick
(`card_p2_subgroups_mul_eq_pairs`):

* **(xiv)** `G14 = Heis × C_p`: commuting is the single linear condition
  `a·Y = X·b`, so `|C(g)| = p⁴` (central, `p²` many) or `p³`;
  `∑_{g≠1}(|C(g)|−p) = (p²−1)(p⁴−p) + (p⁴−p²)(p³−p)`
  ⇒ **column 2 = p³ + 2p² + p + 1**.

* **(xv)** `MaxClass`: three strata — the centre (`|C| = p⁴`, `p−1`
  non-identity elements), `V ∖ Z` with `V = {w = 0}` (`|C| = p³`,
  `p³−p` elements) and `w ≠ 0` (`|C| = p²`, `p⁴−p³` elements);
  `∑_{g≠1}(|C(g)|−p) = (p−1)(p⁴−p) + (p³−p)² + (p⁴−p³)(p²−p)`
  ⇒ **column 2 = 2p² + p + 1** (for `p ≥ 5`).

This file: the linear-kernel count, the `G14` and `MaxClass` centralizer
counts, and both rows.
-/

namespace LeanDring

namespace P4

open Finset

variable {p : ℕ} [Fact p.Prime] [Fact (Odd p)]

open scoped Classical in
omit [Fact (Odd p)] in
/-- Units of `ZMod p` from nonvanishing (`p` prime). -/
theorem zmod_isUnit_of_ne_zero {b : ZMod p} (hb : b ≠ 0) : IsUnit b := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hlt := ZMod.val_lt b
  have hpos : 0 < b.val := by
    rcases Nat.eq_zero_or_pos b.val with h0 | h
    · exact absurd ((ZMod.val_eq_zero b).mp h0) hb
    · exact h
  have hco : Nat.Coprime b.val p :=
    (hp.coprime_iff_not_dvd.mpr (fun hdvd =>
      Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt
        (Nat.le_of_dvd hpos hdvd)))).symm
  have hu' := (ZMod.isUnit_iff_coprime b.val p).mpr hco
  have hbeq : ((b.val : ℕ) : ZMod p) = b := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  rwa [hbeq] at hu'

open scoped Classical in
omit [Fact (Odd p)] in
/-- The kernel of a nonzero linear form on `(ZMod p)²` has `p` points. -/
theorem card_linear_kernel {c₁ c₂ : ZMod p} (h : ¬(c₁ = 0 ∧ c₂ = 0)) :
    Nat.card {w : ZMod p × ZMod p // c₁ * w.1 + c₂ * w.2 = 0} = p := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  by_cases h1 : c₁ = 0
  · have h2 : c₂ ≠ 0 := fun h2 => h ⟨h1, h2⟩
    let f : ZMod p → {w : ZMod p × ZMod p // c₁ * w.1 + c₂ * w.2 = 0} :=
      fun a => ⟨(a, 0), by rw [h1, mul_zero]; ring⟩
    have hbij : Function.Bijective f := by
      rw [Function.bijective_iff_has_inverse]
      refine ⟨fun w => w.1.1, fun a => rfl, fun w => ?_⟩
      obtain ⟨⟨a, b⟩, hw⟩ := w
      rw [h1, zero_mul, zero_add] at hw
      have hu2 := zmod_isUnit_of_ne_zero h2
      have hinv2 : c₂ * c₂⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu2
      have hb : b = 0 := by
        calc b = (c₂ * c₂⁻¹) * b := by rw [hinv2, one_mul]
          _ = c₂⁻¹ * (c₂ * b) := by ring
          _ = 0 := by rw [hw, mul_zero]
      exact Subtype.ext (Prod.ext rfl hb.symm)
    rw [← Nat.card_eq_of_bijective f hbij, Nat.card_zmod]
  · have hu := zmod_isUnit_of_ne_zero h1
    have hinv : c₁ * c₁⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu
    let f : ZMod p → {w : ZMod p × ZMod p // c₁ * w.1 + c₂ * w.2 = 0} :=
      fun b => ⟨(-(c₁⁻¹ * c₂ * b), b), by
        have : c₁ * -(c₁⁻¹ * c₂ * b) + c₂ * b =
            -((c₁ * c₁⁻¹) * (c₂ * b)) + c₂ * b := by ring
        rw [this, hinv]
        ring⟩
    have hbij : Function.Bijective f := by
      rw [Function.bijective_iff_has_inverse]
      refine ⟨fun w => w.1.2, fun b => rfl, fun w => ?_⟩
      obtain ⟨⟨a, b⟩, hw⟩ := w
      refine Subtype.ext (Prod.ext ?_ rfl)
      change -(c₁⁻¹ * c₂ * b) = a
      have h2 : c₁ * a = -(c₂ * b) := by linear_combination hw
      calc -(c₁⁻¹ * c₂ * b) = c₁⁻¹ * -(c₂ * b) := by ring
        _ = c₁⁻¹ * (c₁ * a) := by rw [h2]
        _ = (c₁ * c₁⁻¹) * a := by ring
        _ = a := by rw [hinv, one_mul]
    rw [← Nat.card_eq_of_bijective f hbij, Nat.card_zmod]

/-! ## Centralizers in `G14 = Heis × C_p` -/

namespace G14C

open scoped Classical in
omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
/-- Commuting in `G14` is the linear condition `a·Y = X·b`. -/
theorem commute_iff (g y : G14 p) :
    y * g = g * y ↔ y.1.x * g.1.y = g.1.x * y.1.y := by
  constructor
  · intro h
    have hz := congrArg (fun w : G14 p => w.1.z) h
    have hz' : y.1.z + g.1.z + y.1.x * g.1.y =
        g.1.z + y.1.z + g.1.x * y.1.y := hz
    linear_combination hz' - (add_comm y.1.z g.1.z ▸ rfl : y.1.z + g.1.z = y.1.z + g.1.z)
  · intro h
    refine Prod.ext ?_ (mul_comm y.2 g.2)
    change y.1 * g.1 = g.1 * y.1
    rw [Heis.mul_def, Heis.mul_def]
    ext
    · change y.1.x + g.1.x = g.1.x + y.1.x
      ring
    · change y.1.y + g.1.y = g.1.y + y.1.y
      ring
    · change y.1.z + g.1.z + y.1.x * g.1.y = g.1.z + y.1.z + g.1.x * y.1.y
      rw [h]
      ring

variable (p) in
open scoped Classical in
omit [Fact (Odd p)] in
/-- `|Z(G14)| = p²`. -/
theorem card_center :
    (univ.filter fun g : G14 p => g.1.x = 0 ∧ g.1.y = 0).card = p ^ 2 := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [← Fintype.card_subtype]
  let f : ZMod p × Multiplicative (ZMod p) →
      {g : G14 p // g.1.x = 0 ∧ g.1.y = 0} :=
    fun w => ⟨((⟨0, 0, w.1⟩ : Heis p), w.2), ⟨rfl, rfl⟩⟩
  have hbij : Function.Bijective f := by
    rw [Function.bijective_iff_has_inverse]
    refine ⟨fun g => (g.1.1.z, g.1.2), fun w => rfl, fun g => ?_⟩
    obtain ⟨⟨h, c⟩, hx, hy⟩ := g
    refine Subtype.ext (Prod.ext ?_ rfl)
    change (⟨0, 0, h.z⟩ : Heis p) = h
    ext
    · exact hx.symm
    · exact hy.symm
    · rfl
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_of_bijective f hbij,
    Nat.card_prod, Nat.card_zmod]
  have h1 : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  rw [h1]
  ring

open scoped Classical in
omit [Fact (Odd p)] in
/-- Central elements have full centralizer. -/
theorem card_commute_central {g : G14 p} (hc : g.1.x = 0 ∧ g.1.y = 0) :
    (univ.filter fun y : G14 p => y * g = g * y).card = p ^ 4 := by
  classical
  have hall : (univ.filter fun y : G14 p => y * g = g * y) = univ := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    rw [commute_iff]
    rw [hc.1, hc.2, mul_zero, zero_mul]
  rw [hall, Finset.card_univ, ← Nat.card_eq_fintype_card, card_g14]

open scoped Classical in
omit [Fact (Odd p)] in
/-- Non-central elements have centralizer of order `p³`. -/
theorem card_commute_noncentral {g : G14 p} (hc : ¬(g.1.x = 0 ∧ g.1.y = 0)) :
    (univ.filter fun y : G14 p => y * g = g * y).card = p ^ 3 := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [← Fintype.card_subtype]
  -- the centralizer splits as (linear kernel) × (z, c)
  have hlin : ¬(g.1.y = 0 ∧ -g.1.x = 0) := by
    intro ⟨h1, h2⟩
    exact hc ⟨neg_eq_zero.mp h2, h1⟩
  let f : {w : ZMod p × ZMod p // g.1.y * w.1 + (-g.1.x) * w.2 = 0} ×
      ZMod p × Multiplicative (ZMod p) →
      {y : G14 p // y * g = g * y} :=
    fun w => ⟨((⟨w.1.1.1, w.1.1.2, w.2.1⟩ : Heis p), w.2.2), by
      rw [commute_iff]
      change w.1.1.1 * g.1.y = g.1.x * w.1.1.2
      have := w.1.2
      linear_combination this⟩
  have hbij : Function.Bijective f := by
    rw [Function.bijective_iff_has_inverse]
    refine ⟨fun y => (⟨(y.1.1.x, y.1.1.y), by
        have := (commute_iff g y.1).mp y.2
        change g.1.y * y.1.1.x + -g.1.x * y.1.1.y = 0
        linear_combination this⟩, y.1.1.z, y.1.2),
      fun w => ?_, fun y => ?_⟩
    · refine Prod.ext (Subtype.ext rfl) rfl
    · obtain ⟨⟨h, c⟩, hy⟩ := y
      exact Subtype.ext rfl
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_of_bijective f hbij,
    Nat.card_prod, Nat.card_prod, card_linear_kernel hlin, Nat.card_zmod]
  have h1 : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  rw [h1]
  ring

end G14C

variable (p) in
open scoped Classical in
/-- **Table row (xiv), second column**: `Heis × C_p` has exactly
`p³ + 2p² + p + 1` subgroups of order `p²`. -/
theorem card_order_p2_subgroups_g14 :
    Nat.card {H : Subgroup (G14 p) // Nat.card H = p ^ 2} =
      p ^ 3 + 2 * p ^ 2 + p + 1 := by
  classical
  have hp : p.Prime := Fact.out
  have hkey := card_p2_subgroups_mul_eq_pairs (G := G14 p) g14_pow_p
  -- evaluate the centralizer sum by splitting central / non-central
  have hsplit : ∑ x ∈ univ.filter (fun x : G14 p => x ≠ 1),
      ((univ.filter (fun y : G14 p => y * x = x * y)).card - p) =
      (p ^ 2 - 1) * (p ^ 4 - p) + (p ^ 4 - p ^ 2) * (p ^ 3 - p) := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (univ.filter (fun x : G14 p => x ≠ 1))
      (fun x => x.1.x = 0 ∧ x.1.y = 0)]
    have hc1 : ∀ x ∈ (univ.filter (fun x : G14 p => x ≠ 1)).filter
        (fun x => x.1.x = 0 ∧ x.1.y = 0),
        ((univ.filter (fun y : G14 p => y * x = x * y)).card - p) =
          p ^ 4 - p := by
      intro x hx
      rw [G14C.card_commute_central (Finset.mem_filter.mp hx).2]
    have hc2 : ∀ x ∈ (univ.filter (fun x : G14 p => x ≠ 1)).filter
        (fun x => ¬(x.1.x = 0 ∧ x.1.y = 0)),
        ((univ.filter (fun y : G14 p => y * x = x * y)).card - p) =
          p ^ 3 - p := by
      intro x hx
      rw [G14C.card_commute_noncentral (Finset.mem_filter.mp hx).2]
    rw [Finset.sum_congr rfl hc1, Finset.sum_congr rfl hc2,
      Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
    -- cardinalities of the two index sets
    have hcen : ((univ.filter (fun x : G14 p => x ≠ 1)).filter
        (fun x => x.1.x = 0 ∧ x.1.y = 0)).card = p ^ 2 - 1 := by
      have hswap : ((univ.filter (fun x : G14 p => x ≠ 1)).filter
          (fun x => x.1.x = 0 ∧ x.1.y = 0)) =
          (univ.filter (fun x : G14 p => x.1.x = 0 ∧ x.1.y = 0)).erase 1 := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_erase]
      rw [hswap, Finset.card_erase_of_mem (by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨rfl, rfl⟩),
        G14C.card_center]
    have htot : (univ.filter (fun x : G14 p => x ≠ 1)).card = p ^ 4 - 1 := by
      have h1 : (univ.filter (fun x : G14 p => x ≠ 1)) = univ.erase 1 := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_erase, and_true]
      rw [h1, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, ← Nat.card_eq_fintype_card, card_g14]
    have hnc : ((univ.filter (fun x : G14 p => x ≠ 1)).filter
        (fun x => ¬(x.1.x = 0 ∧ x.1.y = 0))).card = p ^ 4 - p ^ 2 := by
      have hadd := Finset.card_filter_add_card_filter_not
        (s := univ.filter (fun x : G14 p => x ≠ 1))
        (fun x => x.1.x = 0 ∧ x.1.y = 0)
      rw [hcen, htot] at hadd
      have hple : p ^ 2 ≤ p ^ 4 := Nat.pow_le_pow_right hp.pos (by norm_num)
      have h2 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
      omega
    rw [hcen, hnc]
  rw [hsplit] at hkey
  -- arithmetic: cancel `(p²−1)(p²−p)`
  have hp1 := hp.one_lt
  obtain ⟨q, hq, rfl⟩ : ∃ q, 1 ≤ q ∧ p = q + 1 :=
    ⟨p - 1, by omega, by omega⟩
  have e1 : (q + 1) ^ 2 - 1 = q ^ 2 + 2 * q := by
    have h : (q + 1) ^ 2 = q ^ 2 + 2 * q + 1 := by ring
    omega
  have e2 : (q + 1) ^ 2 - (q + 1) = q ^ 2 + q := by
    have h : (q + 1) ^ 2 = q ^ 2 + 2 * q + 1 := by ring
    omega
  have e3 : (q + 1) ^ 4 - (q + 1) = q ^ 4 + 4 * q ^ 3 + 6 * q ^ 2 + 3 * q := by
    have h : (q + 1) ^ 4 = q ^ 4 + 4 * q ^ 3 + 6 * q ^ 2 + 4 * q + 1 := by
      ring
    omega
  have e4 : (q + 1) ^ 4 - (q + 1) ^ 2 =
      q ^ 4 + 4 * q ^ 3 + 5 * q ^ 2 + 2 * q := by
    have h : (q + 1) ^ 4 = q ^ 4 + 4 * q ^ 3 + 6 * q ^ 2 + 4 * q + 1 := by
      ring
    have h2 : (q + 1) ^ 2 = q ^ 2 + 2 * q + 1 := by ring
    omega
  have e5 : (q + 1) ^ 3 - (q + 1) = q ^ 3 + 3 * q ^ 2 + 2 * q := by
    have h : (q + 1) ^ 3 = q ^ 3 + 3 * q ^ 2 + 3 * q + 1 := by ring
    omega
  rw [e1, e2, e3, e4, e5] at hkey
  have hfact : (q ^ 2 + 2 * q) * (q ^ 4 + 4 * q ^ 3 + 6 * q ^ 2 + 3 * q) +
      (q ^ 4 + 4 * q ^ 3 + 5 * q ^ 2 + 2 * q) *
        (q ^ 3 + 3 * q ^ 2 + 2 * q) =
      ((q + 1) ^ 3 + 2 * (q + 1) ^ 2 + (q + 1) + 1) *
        ((q ^ 2 + 2 * q) * (q ^ 2 + q)) := by
    ring
  rw [hfact] at hkey
  have hpos : 0 < (q ^ 2 + 2 * q) * (q ^ 2 + q) := by positivity
  exact Nat.eq_of_mul_eq_mul_right hpos hkey

/-! ## Centralizers in `MaxClass` -/

namespace MCC

open MaxClass

open scoped Classical in
noncomputable instance : Fintype (MaxClass p) :=
  Fintype.ofEquiv _ (MaxClass.toProd p).symm

open scoped Classical in
omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
/-- Commuting in `MaxClass` is the pair of conditions
`yw·gt = gw·yt` and `yw·gu + T(yw)·gt = gw·yu + T(gw)·yt`. -/
theorem commute_iff (g y : MaxClass p) :
    y * g = g * y ↔
      (y.w * g.vec.1 = g.w * y.vec.1 ∧
        y.w * g.vec.2.1 + tri p y.w * g.vec.1 =
          g.w * y.vec.2.1 + tri p g.w * y.vec.1) := by
  constructor
  · intro h
    have hu : y.vec.2.1 + (g.vec.2.1 + y.w * g.vec.1) =
        g.vec.2.1 + (y.vec.2.1 + g.w * y.vec.1) :=
      congrArg (fun z : MaxClass p => z.vec.2.1) h
    have hv : y.vec.2.2 + (g.vec.2.2 + y.w * g.vec.2.1 +
          tri p y.w * g.vec.1) =
        g.vec.2.2 + (y.vec.2.2 + g.w * y.vec.2.1 + tri p g.w * y.vec.1) :=
      congrArg (fun z : MaxClass p => z.vec.2.2) h
    constructor
    · linear_combination hu
    · linear_combination hv
  · rintro ⟨h1, h2⟩
    refine MaxClass.ext ?_ (by change y.w + g.w = g.w + y.w; ring)
    change y.vec + actMC p y.w g.vec = g.vec + actMC p g.w y.vec
    unfold actMC
    ext
    · change y.vec.1 + g.vec.1 = g.vec.1 + y.vec.1
      ring
    · change y.vec.2.1 + (g.vec.2.1 + y.w * g.vec.1) =
        g.vec.2.1 + (y.vec.2.1 + g.w * y.vec.1)
      linear_combination h1
    · change y.vec.2.2 + (g.vec.2.2 + y.w * g.vec.2.1 +
          tri p y.w * g.vec.1) =
        g.vec.2.2 + (y.vec.2.2 + g.w * y.vec.2.1 + tri p g.w * y.vec.1)
      linear_combination h2

variable (p) in
open scoped Classical in
omit [Fact (Odd p)] in
/-- `|Z| = p` (the `v`-axis). -/
theorem card_center :
    (univ.filter fun g : MaxClass p =>
      g.w = 0 ∧ g.vec.1 = 0 ∧ g.vec.2.1 = 0).card = p := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [← Fintype.card_subtype]
  let f : ZMod p → {g : MaxClass p //
      g.w = 0 ∧ g.vec.1 = 0 ∧ g.vec.2.1 = 0} :=
    fun c => ⟨⟨(0, 0, c), 0⟩, ⟨rfl, rfl, rfl⟩⟩
  have hbij : Function.Bijective f := by
    rw [Function.bijective_iff_has_inverse]
    refine ⟨fun g => g.1.vec.2.2, fun c => rfl, fun g => ?_⟩
    obtain ⟨⟨v, w⟩, hw, ht, hu⟩ := g
    refine Subtype.ext (MaxClass.ext ?_ hw.symm)
    change ((0 : ZMod p), (0 : ZMod p), v.2.2) = v
    ext
    · exact ht.symm
    · exact hu.symm
    · rfl
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_of_bijective f hbij,
    Nat.card_zmod]

variable (p) in
open scoped Classical in
omit [Fact (Odd p)] in
/-- `|V| = p³` (the `w = 0` hyperplane). -/
theorem card_w_zero :
    (univ.filter fun g : MaxClass p => g.w = 0).card = p ^ 3 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [← Fintype.card_subtype]
  let f : ZMod p × ZMod p × ZMod p → {g : MaxClass p // g.w = 0} :=
    fun v => ⟨⟨v, 0⟩, rfl⟩
  have hbij : Function.Bijective f := by
    rw [Function.bijective_iff_has_inverse]
    refine ⟨fun g => g.1.vec, fun v => rfl, fun g => ?_⟩
    obtain ⟨⟨v, w⟩, hw⟩ := g
    exact Subtype.ext (MaxClass.ext rfl hw.symm)
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_of_bijective f hbij,
    Nat.card_prod, Nat.card_prod, Nat.card_zmod]
  ring

open scoped Classical in
omit [Fact (Odd p)] in
/-- Central elements have full centralizer. -/
theorem card_commute_central {g : MaxClass p}
    (hc : g.w = 0 ∧ g.vec.1 = 0 ∧ g.vec.2.1 = 0) :
    (univ.filter fun y : MaxClass p => y * g = g * y).card = p ^ 4 := by
  have hall : (univ.filter fun y : MaxClass p => y * g = g * y) = univ := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    rw [commute_iff]
    obtain ⟨hw, ht, hu⟩ := hc
    have htri : tri p (0 : ZMod p) = 0 := by
      unfold tri
      ring
    rw [hw, ht, hu, htri]
    constructor
    · ring
    · ring
  rw [hall, Finset.card_univ, ← Nat.card_eq_fintype_card, card_maxClass]

open scoped Classical in
omit [Fact (Odd p)] in
/-- Elements of `V ∖ Z` have centralizer `V` of order `p³`. -/
theorem card_commute_vnz {g : MaxClass p} (hw : g.w = 0)
    (hnz : ¬(g.vec.1 = 0 ∧ g.vec.2.1 = 0)) :
    (univ.filter fun y : MaxClass p => y * g = g * y).card = p ^ 3 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [← Fintype.card_subtype]
  let f : ZMod p × ZMod p × ZMod p →
      {y : MaxClass p // y * g = g * y} :=
    fun v => ⟨⟨v, 0⟩, by
      rw [commute_iff]
      change (0 : ZMod p) * g.vec.1 = g.w * v.1 ∧
        (0 : ZMod p) * g.vec.2.1 + tri p 0 * g.vec.1 =
          g.w * v.2.1 + tri p g.w * v.1
      have htri : tri p (0 : ZMod p) = 0 := by
        unfold tri
        ring
      rw [hw, htri]
      constructor
      · ring
      · ring⟩
  have hbij : Function.Bijective f := by
    rw [Function.bijective_iff_has_inverse]
    refine ⟨fun y => y.1.vec, fun v => rfl, fun y => ?_⟩
    obtain ⟨y, hy⟩ := y
    rw [commute_iff, hw] at hy
    obtain ⟨h1, h2⟩ := hy
    have htri0 : tri p (0 : ZMod p) = 0 := by
      unfold tri
      ring
    rw [htri0] at h2
    -- from the two conditions and `(gt, gu) ≠ 0`, get `y.w = 0`
    have hyw : y.w = 0 := by
      by_contra hne
      have hu := zmod_isUnit_of_ne_zero hne
      have hinv : y.w * (y.w)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu
      have hgt : g.vec.1 = 0 := by
        have h1' : y.w * g.vec.1 = 0 := by linear_combination h1
        calc g.vec.1 = (y.w * (y.w)⁻¹) * g.vec.1 := by rw [hinv, one_mul]
          _ = (y.w)⁻¹ * (y.w * g.vec.1) := by ring
          _ = 0 := by rw [h1', mul_zero]
      have hgu : g.vec.2.1 = 0 := by
        have h2' : y.w * g.vec.2.1 = 0 := by
          rw [hgt] at h2
          linear_combination h2
        calc g.vec.2.1 = (y.w * (y.w)⁻¹) * g.vec.2.1 := by
              rw [hinv, one_mul]
          _ = (y.w)⁻¹ * (y.w * g.vec.2.1) := by ring
          _ = 0 := by rw [h2', mul_zero]
      exact hnz ⟨hgt, hgu⟩
    exact Subtype.ext (MaxClass.ext rfl hyw.symm)
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_of_bijective f hbij,
    Nat.card_prod, Nat.card_prod, Nat.card_zmod]
  ring

open scoped Classical in
omit [Fact (Odd p)] in
/-- Elements with `w ≠ 0` have centralizer of order `p²`. -/
theorem card_commute_wne {g : MaxClass p} (hgw : g.w ≠ 0) :
    (univ.filter fun y : MaxClass p => y * g = g * y).card = p ^ 2 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hu := zmod_isUnit_of_ne_zero hgw
  have hinv : g.w * (g.w)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu
  rw [← Fintype.card_subtype]
  -- parametrize by `(y.w, y.vec.2.2)`
  let yt : ZMod p → ZMod p := fun w' => (g.w)⁻¹ * (w' * g.vec.1)
  let yu : ZMod p → ZMod p := fun w' =>
    (g.w)⁻¹ * (w' * g.vec.2.1 + tri p w' * g.vec.1 -
      tri p g.w * yt w')
  let f : ZMod p × ZMod p → {y : MaxClass p // y * g = g * y} :=
    fun w => ⟨⟨(yt w.1, yu w.1, w.2), w.1⟩, by
      rw [commute_iff]
      constructor
      · change w.1 * g.vec.1 = g.w * ((g.w)⁻¹ * (w.1 * g.vec.1))
        calc w.1 * g.vec.1 = (g.w * (g.w)⁻¹) * (w.1 * g.vec.1) := by
              rw [hinv, one_mul]
          _ = g.w * ((g.w)⁻¹ * (w.1 * g.vec.1)) := by ring
      · change w.1 * g.vec.2.1 + tri p w.1 * g.vec.1 =
          g.w * yu w.1 + tri p g.w * yt w.1
        change w.1 * g.vec.2.1 + tri p w.1 * g.vec.1 =
          g.w * ((g.w)⁻¹ * (w.1 * g.vec.2.1 + tri p w.1 * g.vec.1 -
            tri p g.w * yt w.1)) + tri p g.w * yt w.1
        calc w.1 * g.vec.2.1 + tri p w.1 * g.vec.1
            = (g.w * (g.w)⁻¹) * (w.1 * g.vec.2.1 + tri p w.1 * g.vec.1 -
                tri p g.w * yt w.1) + tri p g.w * yt w.1 := by
              rw [hinv]
              ring
          _ = _ := by ring⟩
  have hbij : Function.Bijective f := by
    rw [Function.bijective_iff_has_inverse]
    refine ⟨fun y => (y.1.w, y.1.vec.2.2), fun w => rfl, fun y => ?_⟩
    obtain ⟨y, hy⟩ := y
    rw [commute_iff] at hy
    obtain ⟨h1, h2⟩ := hy
    have hyt : yt y.w = y.vec.1 := by
      change (g.w)⁻¹ * (y.w * g.vec.1) = y.vec.1
      calc (g.w)⁻¹ * (y.w * g.vec.1) = (g.w)⁻¹ * (g.w * y.vec.1) := by
            rw [h1]
        _ = (g.w * (g.w)⁻¹) * y.vec.1 := by ring
        _ = y.vec.1 := by rw [hinv, one_mul]
    have hyu : yu y.w = y.vec.2.1 := by
      change (g.w)⁻¹ * (y.w * g.vec.2.1 + tri p y.w * g.vec.1 -
        tri p g.w * yt y.w) = y.vec.2.1
      rw [hyt]
      have h2' : y.w * g.vec.2.1 + tri p y.w * g.vec.1 -
          tri p g.w * y.vec.1 = g.w * y.vec.2.1 := by
        linear_combination h2
      rw [h2']
      calc (g.w)⁻¹ * (g.w * y.vec.2.1) = (g.w * (g.w)⁻¹) * y.vec.2.1 := by
            ring
        _ = y.vec.2.1 := by rw [hinv, one_mul]
    refine Subtype.ext (MaxClass.ext ?_ rfl)
    change (yt y.w, yu y.w, y.vec.2.2) = y.vec
    ext
    · exact hyt
    · exact hyu
    · rfl
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_of_bijective f hbij,
    Nat.card_prod, Nat.card_zmod]
  ring

end MCC

variable (p) in
open scoped Classical in
/-- **Table row (xv), second column**: the maximal-class exponent-`p`
group has exactly `2p² + p + 1` subgroups of order `p²` (`p ≥ 5`). -/
theorem card_order_p2_subgroups_maxClass (hp5 : 5 ≤ p) :
    Nat.card {H : Subgroup (MaxClass p) // Nat.card H = p ^ 2} =
      2 * p ^ 2 + p + 1 := by
  classical
  have hp : p.Prime := Fact.out
  have hkey := card_p2_subgroups_mul_eq_pairs (G := MaxClass p)
    (MaxClass.pow_p hp5)
  -- split the centralizer sum into the three strata
  have hsplit : ∑ x ∈ univ.filter (fun x : MaxClass p => x ≠ 1),
      ((univ.filter (fun y : MaxClass p => y * x = x * y)).card - p) =
      (p - 1) * (p ^ 4 - p) + (p ^ 3 - p) * (p ^ 3 - p) +
        (p ^ 4 - p ^ 3) * (p ^ 2 - p) := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (univ.filter (fun x : MaxClass p => x ≠ 1)) (fun x => x.w = 0)]
    -- the `w = 0` part splits again by centrality
    rw [← Finset.sum_filter_add_sum_filter_not
      ((univ.filter (fun x : MaxClass p => x ≠ 1)).filter
        (fun x => x.w = 0))
      (fun x => x.vec.1 = 0 ∧ x.vec.2.1 = 0)]
    have hc1 : ∀ x ∈ (((univ.filter (fun x : MaxClass p => x ≠ 1)).filter
        (fun x => x.w = 0)).filter
          (fun x => x.vec.1 = 0 ∧ x.vec.2.1 = 0)),
        ((univ.filter (fun y : MaxClass p => y * x = x * y)).card - p) =
          p ^ 4 - p := by
      intro x hx
      rw [Finset.mem_filter, Finset.mem_filter] at hx
      rw [MCC.card_commute_central ⟨hx.1.2, hx.2⟩]
    have hc2 : ∀ x ∈ (((univ.filter (fun x : MaxClass p => x ≠ 1)).filter
        (fun x => x.w = 0)).filter
          (fun x => ¬(x.vec.1 = 0 ∧ x.vec.2.1 = 0))),
        ((univ.filter (fun y : MaxClass p => y * x = x * y)).card - p) =
          p ^ 3 - p := by
      intro x hx
      rw [Finset.mem_filter, Finset.mem_filter] at hx
      rw [MCC.card_commute_vnz hx.1.2 hx.2]
    have hc3 : ∀ x ∈ ((univ.filter (fun x : MaxClass p => x ≠ 1)).filter
        (fun x => ¬ x.w = 0)),
        ((univ.filter (fun y : MaxClass p => y * x = x * y)).card - p) =
          p ^ 2 - p := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [MCC.card_commute_wne hx.2]
    rw [Finset.sum_congr rfl hc1, Finset.sum_congr rfl hc2,
      Finset.sum_congr rfl hc3, Finset.sum_const, Finset.sum_const,
      Finset.sum_const, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    -- the three index-set cardinalities
    have hZ : (((univ.filter (fun x : MaxClass p => x ≠ 1)).filter
        (fun x => x.w = 0)).filter
          (fun x => x.vec.1 = 0 ∧ x.vec.2.1 = 0)).card = p - 1 := by
      have hswap : (((univ.filter (fun x : MaxClass p => x ≠ 1)).filter
          (fun x => x.w = 0)).filter
            (fun x => x.vec.1 = 0 ∧ x.vec.2.1 = 0)) =
          (univ.filter (fun x : MaxClass p =>
            x.w = 0 ∧ x.vec.1 = 0 ∧ x.vec.2.1 = 0)).erase 1 := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_erase]
        tauto
      rw [hswap, Finset.card_erase_of_mem (by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨rfl, rfl, rfl⟩), MCC.card_center]
    have hV : ((univ.filter (fun x : MaxClass p => x ≠ 1)).filter
        (fun x => x.w = 0)).card = p ^ 3 - 1 := by
      have hswap : ((univ.filter (fun x : MaxClass p => x ≠ 1)).filter
          (fun x => x.w = 0)) =
          (univ.filter (fun x : MaxClass p => x.w = 0)).erase 1 := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_erase]
      rw [hswap, Finset.card_erase_of_mem (by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rfl), MCC.card_w_zero]
    have hVnZ : (((univ.filter (fun x : MaxClass p => x ≠ 1)).filter
        (fun x => x.w = 0)).filter
          (fun x => ¬(x.vec.1 = 0 ∧ x.vec.2.1 = 0))).card =
        p ^ 3 - p := by
      have hadd := Finset.card_filter_add_card_filter_not
        (s := (univ.filter (fun x : MaxClass p => x ≠ 1)).filter
          (fun x => x.w = 0))
        (fun x => x.vec.1 = 0 ∧ x.vec.2.1 = 0)
      rw [hZ, hV] at hadd
      have h1 : 1 ≤ p := hp.pos
      have h3 : p ≤ p ^ 3 := Nat.le_self_pow (by norm_num) p
      omega
    have hW : ((univ.filter (fun x : MaxClass p => x ≠ 1)).filter
        (fun x => ¬ x.w = 0)).card = p ^ 4 - p ^ 3 := by
      have hadd := Finset.card_filter_add_card_filter_not
        (s := univ.filter (fun x : MaxClass p => x ≠ 1))
        (fun x => x.w = 0)
      have htot : (univ.filter (fun x : MaxClass p => x ≠ 1)).card =
          p ^ 4 - 1 := by
        have h1 : (univ.filter (fun x : MaxClass p => x ≠ 1)) =
            univ.erase 1 := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_erase, and_true]
        rw [h1, Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ, ← Nat.card_eq_fintype_card,
          MaxClass.card_maxClass]
      rw [hV, htot] at hadd
      have h1 : 1 ≤ p ^ 3 := Nat.one_le_pow _ _ hp.pos
      have h3 : p ^ 3 ≤ p ^ 4 := Nat.pow_le_pow_right hp.pos (by norm_num)
      omega
    rw [hZ, hVnZ, hW]
  rw [hsplit] at hkey
  -- arithmetic: cancel `(p²−1)(p²−p)`
  have hp1 := hp.one_lt
  obtain ⟨q, hq, rfl⟩ : ∃ q, 1 ≤ q ∧ p = q + 1 :=
    ⟨p - 1, by omega, by omega⟩
  have e1 : (q + 1) ^ 2 - 1 = q ^ 2 + 2 * q := by
    have h : (q + 1) ^ 2 = q ^ 2 + 2 * q + 1 := by ring
    omega
  have e2 : (q + 1) ^ 2 - (q + 1) = q ^ 2 + q := by
    have h : (q + 1) ^ 2 = q ^ 2 + 2 * q + 1 := by ring
    omega
  have e3 : (q + 1) ^ 4 - (q + 1) = q ^ 4 + 4 * q ^ 3 + 6 * q ^ 2 + 3 * q := by
    have h : (q + 1) ^ 4 = q ^ 4 + 4 * q ^ 3 + 6 * q ^ 2 + 4 * q + 1 := by
      ring
    omega
  have e5 : (q + 1) ^ 3 - (q + 1) = q ^ 3 + 3 * q ^ 2 + 2 * q := by
    have h : (q + 1) ^ 3 = q ^ 3 + 3 * q ^ 2 + 3 * q + 1 := by ring
    omega
  have e6 : (q + 1) ^ 4 - (q + 1) ^ 3 =
      q ^ 4 + 3 * q ^ 3 + 3 * q ^ 2 + q := by
    have h : (q + 1) ^ 4 = q ^ 4 + 4 * q ^ 3 + 6 * q ^ 2 + 4 * q + 1 := by
      ring
    have h3 : (q + 1) ^ 3 = q ^ 3 + 3 * q ^ 2 + 3 * q + 1 := by ring
    omega
  have e7 : q + 1 - 1 = q := by omega
  rw [e1, e2, e3, e5, e6, e7] at hkey
  have hfact : q * (q ^ 4 + 4 * q ^ 3 + 6 * q ^ 2 + 3 * q) +
      (q ^ 3 + 3 * q ^ 2 + 2 * q) * (q ^ 3 + 3 * q ^ 2 + 2 * q) +
      (q ^ 4 + 3 * q ^ 3 + 3 * q ^ 2 + q) * (q ^ 2 + q) =
      (2 * (q + 1) ^ 2 + (q + 1) + 1) *
        ((q ^ 2 + 2 * q) * (q ^ 2 + q)) := by
    ring
  rw [hfact] at hkey
  have hpos : 0 < (q ^ 2 + 2 * q) * (q ^ 2 + q) := by positivity
  exact Nat.eq_of_mul_eq_mul_right hpos hkey

end P4

end LeanDring
