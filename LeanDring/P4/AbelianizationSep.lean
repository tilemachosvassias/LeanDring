/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P4.NoTableIso
import LeanDring.Theory.DRing.GabCount
import LeanDring.P4.Abelian
import LeanDring.P4.ExpModels
import LeanDring.P4.LastModels

/-!
# Species-table separations via the abelianization-order invariant

Some order-`p⁴` model pairs share their entire subgroup-count vector and are
separated only by `|G^ab|` — the abelianization order, which a species-table
isomorphism preserves (`card_abelianization_eq_of_speciesTableIso_of_pgroup`).
The clean case is **abelian vs nonabelian**: the abelian model has
`|G^ab| = |G| = p⁴`, the nonabelian one has `|G^ab| < p⁴`.
-/

namespace LeanDring.P4

open DRing
open scoped commutatorElement

section AbInfra

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- `|G^ab| · |[G,G]| = |G|`. -/
theorem card_abelianization_mul_commutator :
    Nat.card (Abelianization G) * Nat.card (commutator G) = Nat.card G := by
  have h := Subgroup.card_mul_index (commutator G)
  rw [Subgroup.index_eq_card, mul_comm] at h
  exact h

/-- For a finite commutative group, `|G^ab| = |G|`. -/
theorem card_abelianization_of_comm {G : Type*} [CommGroup G] [Finite G] :
    Nat.card (Abelianization G) = Nat.card G := by
  have h := card_abelianization_mul_commutator (G := G)
  rw [commutator_eq_bot] at h
  simpa using h

/-- A finite noncommutative group has `|G^ab| < |G|`. -/
theorem card_abelianization_lt_of_not_comm
    (hab : ∃ a b : G, a * b ≠ b * a) :
    Nat.card (Abelianization G) < Nat.card G := by
  have hne : commutator G ≠ ⊥ := by
    intro hc
    obtain ⟨a, b, hab⟩ := hab
    exact hab (((commutator_eq_bot_iff (G := G)).mp hc).is_comm.comm a b)
  have h2 : 1 < Nat.card (commutator G) :=
    (Subgroup.one_lt_card_iff_ne_bot (H := commutator G)).mpr hne
  have hmul := card_abelianization_mul_commutator (G := G)
  have hposG : 0 < Nat.card G := Nat.card_pos
  nlinarith [hmul, h2, hposG]

end AbInfra

variable {p : ℕ} [Fact p.Prime] [Fact (Odd p)]

/-- `3 ≤ p` for an odd prime. -/
theorem three_le_p_of_odd : 3 ≤ p := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := Fact.out
  rcases hp.two_le.lt_or_eq with h | h
  · omega
  · exact absurd (h ▸ hodd) (by decide)

omit [Fact (Odd p)] in
/-- `liftpp p 1 ≠ 0` — the `p²`-scaled lift of `1` is nonzero in `ZMod p³`. -/
theorem liftpp_one_ne_zero : liftpp p (1 : ZMod p) ≠ 0 := by
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  intro h0
  have hv := liftpp_val (1 : ZMod p)
  rw [h0, ZMod.val_zero, ZMod.val_one, mul_one] at hv
  exact absurd hv.symm (pow_ne_zero 2 (Fact.out : p.Prime).ne_zero)

/-- **A31 vs M6**: identical subgroup-count vectors, but `A31` is abelian
(`|G^ab| = p⁴`) and `M6` is not (`|G^ab| < p⁴`). -/
theorem isEmpty_tableIso_a31_m6 :
    IsEmpty (SpeciesTableIso (A31 p) (M6 p)) := by
  constructor
  intro T
  have hA : Nat.card (A31 p) = p ^ 4 := by
    rw [Nat.card_eq_fintype_card]
    change Fintype.card (Multiplicative (ZMod (p ^ 3) × ZMod p)) = p ^ 4
    rw [Fintype.card_multiplicative, Fintype.card_prod, ZMod.card, ZMod.card]
    ring
  have hM : Nat.card (M6 p) = p ^ 4 := M6.card_m6 p
  have hEq := card_abelianization_eq_of_speciesTableIso_of_pgroup three_le_p_of_odd hA hM T
  rw [card_abelianization_of_comm] at hEq
  have hM6nc : ∃ a b : M6 p, a * b ≠ b * a := by
    refine ⟨⟨1, 0⟩, ⟨0, 1⟩, ?_⟩
    rw [Ne, M6.ext_iff, not_and_or]
    left
    rw [M6.mul_def, M6.mul_def]
    change (1 : ZMod (p ^ 3)) + 0 + liftpp p ((0 : ZMod p) * red3 p 0)
        ≠ 0 + 1 + liftpp p ((1 : ZMod p) * red3 p 1)
    rw [zero_mul, liftpp_zero, map_one, mul_one]
    intro heq
    exact liftpp_one_ne_zero (by linear_combination -heq)
  have hlt := card_abelianization_lt_of_not_comm hM6nc
  rw [hA] at hEq
  rw [hM] at hlt
  omega

omit [Fact (Odd p)] in
/-- `liftp p 1 ≠ 0` — the `p`-scaled lift of `1` is nonzero in `ZMod p²`. -/
theorem liftp_one_ne_zero : liftp p (1 : ZMod p) ≠ 0 := by
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  intro h0
  have hv := Model.liftp_val (1 : ZMod p)
  rw [h0, ZMod.val_zero, ZMod.val_one, mul_one] at hv
  exact absurd hv.symm (Fact.out : p.Prime).ne_zero

/-- **A22 vs M8**: identical subgroup-count vectors, but `A22` is abelian
(`|G^ab| = p⁴`) and `M8` is not (`|G^ab| < p⁴`). -/
theorem isEmpty_tableIso_a22_m8 :
    IsEmpty (SpeciesTableIso (A22 p) (M8 p)) := by
  constructor
  intro T
  have hA : Nat.card (A22 p) = p ^ 4 := by
    rw [Nat.card_eq_fintype_card]
    change Fintype.card (Multiplicative (ZMod (p ^ 2) × ZMod (p ^ 2))) = p ^ 4
    rw [Fintype.card_multiplicative, Fintype.card_prod, ZMod.card]
    ring
  have hM : Nat.card (M8 p) = p ^ 4 := M8.card_m8 p
  have hEq := card_abelianization_eq_of_speciesTableIso_of_pgroup three_le_p_of_odd hA hM T
  rw [card_abelianization_of_comm] at hEq
  have hM8nc : ∃ a b : M8 p, a * b ≠ b * a := by
    refine ⟨⟨1, 0⟩, ⟨0, 1⟩, ?_⟩
    rw [Ne, M8.ext_iff, not_and_or]
    left
    rw [M8.mul_def, M8.mul_def]
    change (1 : ZMod (p ^ 2)) + 0 + liftp p (redp p (0 : ZMod (p ^ 2)) * redp p 0)
        ≠ 0 + 1 + liftp p (redp p (1 : ZMod (p ^ 2)) * redp p 1)
    rw [map_zero, zero_mul, liftp_zero, map_one, mul_one]
    intro heq
    exact liftp_one_ne_zero (by linear_combination -heq)
  have hlt := card_abelianization_lt_of_not_comm hM8nc
  rw [hA] at hEq
  rw [hM] at hlt
  omega

/-- **A211 vs G9**: identical subgroup-count vectors, but `A211` is abelian
(`|G^ab| = p⁴`) and `G9 = Mod3 × C_p` is not (`|G^ab| < p⁴`). -/
theorem isEmpty_tableIso_a211_g9 :
    IsEmpty (SpeciesTableIso (A211 p) (G9 p)) := by
  constructor
  intro T
  have hA : Nat.card (A211 p) = p ^ 4 := by
    rw [Nat.card_eq_fintype_card]
    change Fintype.card (Multiplicative (ZMod (p ^ 2) × ZMod p × ZMod p)) = p ^ 4
    rw [Fintype.card_multiplicative, Fintype.card_prod, Fintype.card_prod,
      ZMod.card, ZMod.card]
    ring
  have hM : Nat.card (G9 p) = p ^ 4 := by
    rw [Nat.card_prod, Mod3.card_mod3, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card]
    ring
  have hEq := card_abelianization_eq_of_speciesTableIso_of_pgroup three_le_p_of_odd hA hM T
  rw [card_abelianization_of_comm] at hEq
  have hG9nc : ∃ a b : G9 p, a * b ≠ b * a := by
    refine ⟨(⟨0, 1⟩, 1), (⟨1, 0⟩, 1), ?_⟩
    rw [Prod.mk_mul_mk, Prod.mk_mul_mk, Ne, Prod.ext_iff, not_and_or]
    left
    rw [Mod3.ext_iff, not_and_or]
    left
    rw [Mod3.mul_def, Mod3.mul_def]
    change (0 : ZMod (p ^ 2)) + 1 + liftp p ((1 : ZMod p) * redp p 1)
        ≠ 1 + 0 + liftp p ((0 : ZMod p) * redp p 0)
    rw [map_one, mul_one, zero_mul, liftp_zero]
    intro heq
    exact liftp_one_ne_zero (by linear_combination heq)
  have hlt := card_abelianization_lt_of_not_comm hG9nc
  rw [hA] at hEq
  rw [hM] at hlt
  omega

/-- **A1111 vs G14**: identical subgroup-count vectors, but `A1111` is abelian
(`|G^ab| = p⁴`) and `G14 = Heis × C_p` is not (`|G^ab| < p⁴`). -/
theorem isEmpty_tableIso_a1111_g14 (_hp5 : 5 ≤ p) :
    IsEmpty (SpeciesTableIso (A1111 p) (G14 p)) := by
  constructor
  intro T
  have hA : Nat.card (A1111 p) = p ^ 4 := by
    rw [Nat.card_eq_fintype_card]
    change Fintype.card (Multiplicative (ZMod p × ZMod p × ZMod p × ZMod p)) = p ^ 4
    rw [Fintype.card_multiplicative, Fintype.card_prod, Fintype.card_prod,
      Fintype.card_prod, ZMod.card]
    ring
  have hM : Nat.card (G14 p) = p ^ 4 := card_g14 p
  have hEq := card_abelianization_eq_of_speciesTableIso_of_pgroup three_le_p_of_odd hA hM T
  rw [card_abelianization_of_comm] at hEq
  have hG14nc : ∃ a b : G14 p, a * b ≠ b * a := by
    refine ⟨(⟨1, 0, 0⟩, 1), (⟨0, 1, 0⟩, 1), ?_⟩
    rw [Prod.mk_mul_mk, Prod.mk_mul_mk, Ne, Prod.ext_iff, not_and_or]
    left
    rw [Heis.ext_iff, not_and_or]
    right
    rw [not_and_or]
    right
    rw [Heis.mul_def, Heis.mul_def]
    change (0 : ZMod p) + 0 + 1 * 1 ≠ 0 + 0 + 0 * 0
    intro heq
    simp only [mul_one, mul_zero, add_zero, zero_add] at heq
    exact one_ne_zero heq
  have hlt := card_abelianization_lt_of_not_comm hG14nc
  rw [hA] at hEq
  rw [hM] at hlt
  omega

/-- **A1111 vs MaxClass**: identical subgroup-count vectors, but `A1111` is
abelian (`|G^ab| = p⁴`) and the maximal-class group `(C_p)³ ⋊ C_p` is not
(`|G^ab| < p⁴`). -/
theorem isEmpty_tableIso_a1111_maxClass (_hp5 : 5 ≤ p) :
    IsEmpty (SpeciesTableIso (A1111 p) (MaxClass p)) := by
  constructor
  intro T
  have hA : Nat.card (A1111 p) = p ^ 4 := by
    rw [Nat.card_eq_fintype_card]
    change Fintype.card (Multiplicative (ZMod p × ZMod p × ZMod p × ZMod p)) = p ^ 4
    rw [Fintype.card_multiplicative, Fintype.card_prod, Fintype.card_prod,
      Fintype.card_prod, ZMod.card]
    ring
  have hM : Nat.card (MaxClass p) = p ^ 4 := MaxClass.card_maxClass p
  have hEq := card_abelianization_eq_of_speciesTableIso_of_pgroup three_le_p_of_odd hA hM T
  rw [card_abelianization_of_comm] at hEq
  have hMCnc : ∃ a b : MaxClass p, a * b ≠ b * a := by
    refine ⟨⟨(1, 0, 0), 0⟩, ⟨(0, 0, 0), 1⟩, ?_⟩
    rw [Ne, MaxClass.ext_iff, not_and_or]
    left
    rw [MaxClass.mul_def, MaxClass.mul_def]
    change ((1, 0, 0) + actMC p 0 (0, 0, 0) : ZMod p × ZMod p × ZMod p)
        ≠ (0, 0, 0) + actMC p 1 (1, 0, 0)
    intro heq
    apply one_ne_zero (α := ZMod p)
    have hmid := congrArg (fun v : ZMod p × ZMod p × ZMod p => v.2.1) heq
    simpa [actMC, tri] using hmid.symm
  have hlt := card_abelianization_lt_of_not_comm hMCnc
  rw [hA] at hEq
  rw [hM] at hlt
  omega

/-! ## `Gid3` vs `Gid8`: identical subgroup counts, separated only by `|G^ab|`

Both models have order `p⁴` and share their entire subgroup-count vector, so no
subgroup count separates them.  They differ **only** in abelianization order:
`|Gid3^ab| = p³` (class 2, `|[Gid3,Gid3]| = p`) versus `|Gid8^ab| = p²`
(maximal class, `|[Gid8,Gid8]| = p²`).  A species-table isomorphism forces the
abelianization orders equal, giving `p³ = p²` — a contradiction. -/

omit [Fact (Odd p)] in
/-- Commutators in `Gid3` land in the central `⟨0,1,0⟩`-line: the `α` and `u`
coordinates cancel, leaving only the `y`-coordinate
`x.u·redp(w.α) − w.u·redp(x.α)`. -/
theorem gid3_comm (x w : Gid3 p) :
    ⁅x, w⁆ = ⟨0, x.u * redp p w.α - w.u * redp p x.α, 0⟩ := by
  have hxi : x⁻¹ = ⟨-x.α, -x.y + x.u * redp p x.α, -x.u⟩ := rfl
  have hwi : w⁻¹ = ⟨-w.α, -w.y + w.u * redp p w.α, -w.u⟩ := rfl
  rw [commutatorElement_def, hxi, hwi]
  refine Gid3.ext ?_ ?_ ?_
  · change x.α + w.α + -x.α + -w.α = 0
    ring
  · change x.y + w.y + x.u * redp p w.α + (-x.y + x.u * redp p x.α)
        + (x.u + w.u) * redp p (-x.α)
        + (-w.y + w.u * redp p w.α)
        + (x.u + w.u + -x.u) * redp p (-w.α)
      = x.u * redp p w.α - w.u * redp p x.α
    rw [map_neg, map_neg]
    ring
  · change x.u + w.u + -x.u + -w.u = 0
    ring

/-- `|[Gid3, Gid3]| ≤ p`: the derived subgroup lies in the order-`p` line
`⟨(0,1,0)⟩`. -/
theorem card_commutator_gid3_le : Nat.card (commutator (Gid3 p)) ≤ p := by
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  -- `c = ⟨0,1,0⟩` has order `p`.
  have hcp : (⟨0, 1, 0⟩ : Gid3 p) ^ p = 1 := by
    rw [Gid3.pow_formula, Gid3.one_def]
    refine Gid3.ext ?_ ?_ ?_
    · change ((p : ℕ) : ZMod (p ^ 2)) * 0 = 0
      rw [mul_zero]
    · change ((p : ℕ) : ZMod p) * 1
          + tri p ((p : ℕ) : ZMod p) * ((0 : ZMod p) * redp p 0) = 0
      rw [hp0]; ring
    · change ((p : ℕ) : ZMod p) * 0 = 0
      rw [mul_zero]
  have hcne : (⟨0, 1, 0⟩ : Gid3 p) ≠ 1 := by
    rw [Gid3.one_def]
    intro h
    exact one_ne_zero (congrArg Gid3.y h)
  have hord : orderOf (⟨0, 1, 0⟩ : Gid3 p) = p := orderOf_eq_prime hcp hcne
  have hle : commutator (Gid3 p) ≤ Subgroup.zpowers (⟨0, 1, 0⟩ : Gid3 p) := by
    change ⁅(⊤ : Subgroup (Gid3 p)), ⊤⁆ ≤ Subgroup.zpowers _
    rw [Subgroup.commutator_le]
    intro x _ w _
    rw [gid3_comm]
    have hpow : (⟨0, 1, 0⟩ : Gid3 p)
        ^ (x.u * redp p w.α - w.u * redp p x.α).val
        = ⟨0, x.u * redp p w.α - w.u * redp p x.α, 0⟩ := by
      rw [Gid3.pow_formula]
      refine Gid3.ext ?_ ?_ ?_
      · change (((x.u * redp p w.α - w.u * redp p x.α).val : ℕ) : ZMod (p ^ 2))
            * 0 = 0
        rw [mul_zero]
      · change (((x.u * redp p w.α - w.u * redp p x.α).val : ℕ) : ZMod p) * 1
            + tri p (((x.u * redp p w.α - w.u * redp p x.α).val : ℕ) : ZMod p)
              * ((0 : ZMod p) * redp p 0)
            = x.u * redp p w.α - w.u * redp p x.α
        rw [mul_one, zero_mul, mul_zero, add_zero]
        exact ZMod.natCast_rightInverse _
      · change (((x.u * redp p w.α - w.u * redp p x.α).val : ℕ) : ZMod p) * 0 = 0
        rw [mul_zero]
    rw [← hpow]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  calc Nat.card (commutator (Gid3 p))
      ≤ Nat.card (Subgroup.zpowers (⟨0, 1, 0⟩ : Gid3 p)) :=
        Subgroup.card_le_of_le hle
    _ = orderOf (⟨0, 1, 0⟩ : Gid3 p) := Nat.card_zpowers _
    _ = p := hord

/-! ### `|[Gid8, Gid8]| ≥ p²`

The outer generator `s = ⟨(0,0,0),1⟩` acts on the normal `(C_p)³` by the regular
unipotent, and `⁅s, ⟨(a,b,0),0⟩⁆ = ⟨(0,a,b),0⟩`.  Hence every element of the
order-`p²` subgroup `{⟨(0,a,b),0⟩}` is a single commutator. -/

omit [Fact (Odd p)] in
/-- Carry bit `cbit(x, 0) = 0` (no wrap when adding `0`). -/
theorem cbitN_right_zero (x : ZMod p) : cbitN p x 0 = 0 := by
  unfold cbitN
  rw [add_zero, ZMod.val_zero, Nat.add_zero, Nat.sub_self, Nat.zero_div]

omit [Fact (Odd p)] in
/-- Carry bit `cbit(-1, 1) = 1` (the wrap `(p-1) + 1 = p`). -/
theorem cbitN_neg_one_one : cbitN p (-1 : ZMod p) 1 = 1 := by
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  obtain ⟨hs, hle⟩ := cbit_spec (-1 : ZMod p) (1 : ZMod p)
  have h0 : ((-1 : ZMod p) + 1) = 0 := by ring
  rw [h0, ZMod.val_zero, Nat.zero_add] at hs
  have h1 : (1 : ZMod p).val = 1 := ZMod.val_one p
  rw [h1] at hs
  rcases Nat.lt_or_ge (cbitN p (-1 : ZMod p) 1) 1 with h | h
  · have hz : cbitN p (-1 : ZMod p) 1 = 0 := by omega
    rw [hz, Nat.mul_zero] at hs
    omega
  · omega

omit [Fact (Odd p)] in
/-- Carry bit `cbit(1, -1) = 1`. -/
theorem cbitN_one_neg_one : cbitN p (1 : ZMod p) (-1) = 1 := by
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  obtain ⟨hs, hle⟩ := cbit_spec (1 : ZMod p) (-1 : ZMod p)
  have h0 : ((1 : ZMod p) + (-1)) = 0 := by ring
  rw [h0, ZMod.val_zero, Nat.zero_add] at hs
  have h1 : (1 : ZMod p).val = 1 := ZMod.val_one p
  rw [h1] at hs
  rcases Nat.lt_or_ge (cbitN p (1 : ZMod p) (-1)) 1 with h | h
  · have hz : cbitN p (1 : ZMod p) (-1) = 0 := by omega
    rw [hz, Nat.mul_zero] at hs
    omega
  · omega

/-- The key `Gid8` commutator: `⁅s, ⟨(a,b,0),0⟩⁆ = ⟨(0,a,b),0⟩` with the outer
generator `s = ⟨(0,0,0),1⟩`. -/
theorem gid8_comm (a b : ZMod p) :
    ⁅(⟨(0, 0, 0), 1⟩ : Gid8 p), (⟨(a, b, 0), 0⟩ : Gid8 p)⁆
      = ⟨(0, a, b), 0⟩ := by
  have htri1 : tri p (1 : ZMod p) = 0 := by unfold tri; ring
  -- inverses
  have hsinv : (⟨(0, 0, 0), 1⟩ : Gid8 p)⁻¹ = ⟨(0, 0, -1), -1⟩ := by
    have hrw : (⟨(0, 0, 0), 1⟩ : Gid8 p)⁻¹
        = ⟨-(actMC p (-(1 : ZMod p)) ((0 : ZMod p), (0 : ZMod p), (0 : ZMod p)))
            - Gid8.cvec p (-(1 : ZMod p)) (1 : ZMod p), -(1 : ZMod p)⟩ := rfl
    rw [hrw]
    refine Gid8.ext ?_ rfl
    have hact : actMC p (-(1 : ZMod p)) ((0 : ZMod p), (0 : ZMod p), (0 : ZMod p))
        = 0 := by
      unfold actMC; dsimp only
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
    have hcv : Gid8.cvec p (-(1 : ZMod p)) (1 : ZMod p)
        = ((0 : ZMod p), (0 : ZMod p), (1 : ZMod p)) := by
      unfold Gid8.cvec; rw [cbitN_neg_one_one]; simp
    rw [hact, hcv, neg_zero, zero_sub]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
  have hhinv : (⟨(a, b, 0), 0⟩ : Gid8 p)⁻¹ = ⟨(-a, -b, 0), 0⟩ := by
    have hrw : (⟨(a, b, 0), 0⟩ : Gid8 p)⁻¹
        = ⟨-(actMC p (-(0 : ZMod p)) ((a : ZMod p), (b : ZMod p), (0 : ZMod p)))
            - Gid8.cvec p (-(0 : ZMod p)) (0 : ZMod p), -(0 : ZMod p)⟩ := rfl
    rw [hrw]
    refine Gid8.ext ?_ (by simp)
    have hact : actMC p (-(0 : ZMod p)) ((a : ZMod p), (b : ZMod p), (0 : ZMod p))
        = (a, b, 0) := by rw [neg_zero, actMC_zero]
    have hcv : Gid8.cvec p (-(0 : ZMod p)) (0 : ZMod p) = 0 := by
      rw [neg_zero]; exact Gid8.cvec_zero 0
    rw [hact, hcv, sub_zero]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
  -- three products
  have e1 : (⟨(0, 0, 0), 1⟩ : Gid8 p) * ⟨(a, b, 0), 0⟩ = ⟨(a, a + b, b), 1⟩ := by
    rw [Gid8.mul_def]
    refine Gid8.ext ?_ ?_
    · have hact : actMC p (1 : ZMod p) ((a : ZMod p), (b : ZMod p), (0 : ZMod p))
          = (a, a + b, b) := by
        unfold actMC; dsimp only; rw [htri1]
        refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> ring
      have hcv : Gid8.cvec p (1 : ZMod p) (0 : ZMod p) = 0 := by
        unfold Gid8.cvec; rw [cbitN_right_zero]; simp
      rw [hcv, add_zero, hact]
      simp only [Prod.mk_add_mk, zero_add]
    · change (1 : ZMod p) + 0 = 1
      ring
  have e2 : (⟨(a, a + b, b), 1⟩ : Gid8 p) * ⟨(0, 0, -1), -1⟩
      = ⟨(a, a + b, b), 0⟩ := by
    rw [Gid8.mul_def]
    refine Gid8.ext ?_ ?_
    · have hact : actMC p (1 : ZMod p) ((0 : ZMod p), (0 : ZMod p), (-1 : ZMod p))
          = (0, 0, -1) := by
        unfold actMC; dsimp only; rw [htri1]
        refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> ring
      have hcv : Gid8.cvec p (1 : ZMod p) (-1 : ZMod p)
          = ((0 : ZMod p), (0 : ZMod p), (1 : ZMod p)) := by
        unfold Gid8.cvec; rw [cbitN_one_neg_one]; simp
      rw [hact, hcv]
      simp only [Prod.mk_add_mk]
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> ring
    · change (1 : ZMod p) + -1 = 0
      ring
  have e3 : (⟨(a, a + b, b), 0⟩ : Gid8 p) * ⟨(-a, -b, 0), 0⟩ = ⟨(0, a, b), 0⟩ := by
    rw [Gid8.mul_def]
    refine Gid8.ext ?_ ?_
    · rw [actMC_zero, Gid8.cvec_zero, add_zero]
      simp only [Prod.mk_add_mk]
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> ring
    · change (0 : ZMod p) + 0 = 0
      ring
  rw [commutatorElement_def, hsinv, hhinv, e1, e2, e3]

variable (p) in
/-- The order-`p²` subgroup `{⟨(0,a,b),0⟩}` inside the derived subgroup of
`Gid8`. -/
def H8 : Subgroup (Gid8 p) where
  carrier := {g | g.w = 0 ∧ g.vec.1 = 0}
  one_mem' := ⟨rfl, rfl⟩
  mul_mem' := by
    rintro g h ⟨hgw, hgv⟩ ⟨hhw, hhv⟩
    refine ⟨?_, ?_⟩
    · change g.w + h.w = 0
      rw [hgw, hhw, add_zero]
    · change (g.vec + actMC p g.w h.vec + Gid8.cvec p g.w h.w).1 = 0
      rw [hgw, actMC_zero, Gid8.cvec_zero, add_zero]
      change g.vec.1 + h.vec.1 = 0
      rw [hgv, hhv, add_zero]
  inv_mem' := by
    rintro g ⟨hgw, hgv⟩
    refine ⟨?_, ?_⟩
    · change -g.w = 0
      rw [hgw, neg_zero]
    · change (-(actMC p (-g.w) g.vec) - Gid8.cvec p (-g.w) g.w).1 = 0
      rw [hgw, neg_zero, actMC_zero, Gid8.cvec_zero, sub_zero]
      rw [Prod.fst_neg, hgv, neg_zero]

variable (p) in
theorem card_H8 : Nat.card (H8 p) = p ^ 2 := by
  have e : H8 p ≃ ZMod p × ZMod p :=
    { toFun := fun g => (g.1.vec.2.1, g.1.vec.2.2)
      invFun := fun ab => ⟨⟨(0, ab.1, ab.2), 0⟩, ⟨rfl, rfl⟩⟩
      left_inv := by
        rintro ⟨g, hw, hv⟩
        apply Subtype.ext
        refine Gid8.ext ?_ hw.symm
        exact Prod.ext hv.symm rfl
      right_inv := fun ab => rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_zmod]
  ring

theorem H8_le_commutator : H8 p ≤ commutator (Gid8 p) := by
  intro g hg
  obtain ⟨hgw, hgv⟩ := hg
  have hg' : g = ⁅(⟨(0, 0, 0), 1⟩ : Gid8 p),
      (⟨(g.vec.2.1, g.vec.2.2, 0), 0⟩ : Gid8 p)⁆ := by
    rw [gid8_comm]
    refine Gid8.ext ?_ hgw
    exact Prod.ext hgv rfl
  rw [hg']
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- `|[Gid8, Gid8]| ≥ p²`. -/
theorem card_commutator_gid8_ge : p ^ 2 ≤ Nat.card (commutator (Gid8 p)) := by
  rw [← card_H8 p]
  exact Subgroup.card_le_of_le H8_le_commutator

/-- **`Gid3` vs `Gid8`**: identical subgroup-count vectors, but
`|Gid3^ab| = p³` while `|Gid8^ab| = p²` — a species-table isomorphism forces
these equal, an impossibility. -/
theorem isEmpty_tableIso_gid3_gid8 :
    IsEmpty (SpeciesTableIso (Gid3 p) (Gid8 p)) := by
  constructor
  intro T
  have hp0 : 0 < p := Nat.pos_of_ne_zero (Fact.out : p.Prime).ne_zero
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hA : Nat.card (Gid3 p) = p ^ 4 := Gid3.card_gid3 p
  have hB : Nat.card (Gid8 p) = p ^ 4 := Gid8.card_gid8 p
  have hEq := card_abelianization_eq_of_speciesTableIso_of_pgroup
    three_le_p_of_odd hA hB T
  have h3mul : Nat.card (Abelianization (Gid3 p))
      * Nat.card (commutator (Gid3 p)) = p ^ 4 := by
    rw [card_abelianization_mul_commutator, hA]
  have h8mul : Nat.card (Abelianization (Gid8 p))
      * Nat.card (commutator (Gid8 p)) = p ^ 4 := by
    rw [card_abelianization_mul_commutator, hB]
  have h3c : Nat.card (commutator (Gid3 p)) ≤ p := card_commutator_gid3_le
  have h8c : p ^ 2 ≤ Nat.card (commutator (Gid8 p)) := card_commutator_gid8_ge
  -- `|Gid3^ab| ≥ p³`
  have hge : p ^ 3 ≤ Nat.card (Abelianization (Gid3 p)) := by
    have h1 : p ^ 3 * p ≤ Nat.card (Abelianization (Gid3 p)) * p := by
      calc p ^ 3 * p = p ^ 4 := by ring
        _ = Nat.card (Abelianization (Gid3 p))
              * Nat.card (commutator (Gid3 p)) := h3mul.symm
        _ ≤ Nat.card (Abelianization (Gid3 p)) * p := by gcongr
    exact Nat.le_of_mul_le_mul_right h1 hp0
  -- `|Gid8^ab| ≤ p²`
  have hle : Nat.card (Abelianization (Gid8 p)) ≤ p ^ 2 := by
    have h1 : Nat.card (Abelianization (Gid8 p)) * p ^ 2 ≤ p ^ 2 * p ^ 2 := by
      calc Nat.card (Abelianization (Gid8 p)) * p ^ 2
          ≤ Nat.card (Abelianization (Gid8 p))
              * Nat.card (commutator (Gid8 p)) := by gcongr
        _ = p ^ 4 := h8mul
        _ = p ^ 2 * p ^ 2 := by ring
    exact Nat.le_of_mul_le_mul_right h1 (by positivity)
  rw [hEq] at hge
  have hcontra : p ^ 3 ≤ p ^ 2 := le_trans hge hle
  have hlt : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp1 (by omega)
  omega

end LeanDring.P4
