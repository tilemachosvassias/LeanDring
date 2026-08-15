/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P4.ADetect
import LeanDring.P4.ExpA
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Row detection: `subA` is the unique order-`p³` subgroup with a primitive character

`eq_subA_of_char_primitive`: an order-`p³` subgroup `K` of `Model p d` that admits
a character `χ : K →* ℂˣ` taking a value `χ(g)` with `χ(g)ᵖ ≠ 1` (a primitive
`p²`-th root of unity) must be `subA p d`.  Reason: such a character forces the
abelianization `K/[K,K]` to have an element of order `p²`, so `K` is abelian (a
`p`-group whose center-quotient is cyclic), hence `= subA` by
`eq_subA_of_abelian_maximal`.

This is the "row = A" detector for the twin-separation reduction `hentry`: the
`G₂` distinguished entry `z ∉ ℤ[ζ_p]` lives over a row whose subgroup admits
exactly such a character, pinning that row to the A-block.
-/

namespace LeanDring.P4

open Model

variable {p : ℕ} [Fact p.Prime] [Fact (Odd p)]

/-- **`Model p d` has exponent `p²`**: every element satisfies `x^{p²} = 1`.
Applying `pow_p` twice, `x^p = ⟨liftp(redp α + d·u), 0, 0⟩` has `a`-coordinate a
`liftp`, and `redp ∘ liftp = 0`, so `(x^p)^p = 1`. -/
theorem model_pow_psq {d : ZMod p} (hp5 : 5 ≤ p) (x : Model p d) : x ^ (p ^ 2) = 1 := by
  rw [show p ^ 2 = p * p by ring, pow_mul, pow_p hp5, pow_p hp5]
  apply Model.ext
  · change liftp p (redp p (liftp p (redp p x.α + d * x.u)) + d * 0) = (0 : ZMod (p ^ 2))
    rw [redp_liftp, mul_zero, add_zero, liftp_zero]
  · rfl
  · rfl

/-- **A normal subgroup of prime order in a finite `q`-group is central.**
The conjugation action of `K` on `N` fixes `1`; since `q ∣ |N|`,
`exists_fixed_point_of_prime_dvd_card_of_fixed_point` produces another fixed
point `n ≠ 1`, a nontrivial element of `N ⊓ center K`.  As `|N| = q` is prime,
`N ⊓ center K = N`, so `N ≤ center K`. -/
theorem prime_normal_le_center {K : Type*} [Group K] [Finite K] {q : ℕ} [Fact q.Prime]
    (hK : IsPGroup q K) (N : Subgroup K) [hNnorm : N.Normal] (hN : Nat.card N = q) :
    N ≤ Subgroup.center K := by
  letI : MulAction K N :=
    { smul := fun k n => ⟨k * (n : K) * k⁻¹, hNnorm.conj_mem (n : K) n.2 k⟩
      one_smul := fun n => Subtype.ext (by change (1 : K) * (n : K) * (1 : K)⁻¹ = (n : K); group)
      mul_smul := fun a b n => Subtype.ext (by
        change (a * b) * (n : K) * (a * b)⁻¹ = a * (b * (n : K) * b⁻¹) * a⁻¹; group) }
  have hsmul : ∀ (k : K) (n : N), ((k • n : N) : K) = k * (n : K) * k⁻¹ := fun _ _ => rfl
  have hfix1 : (1 : N) ∈ MulAction.fixedPoints K N := by
    intro k; apply Subtype.ext; rw [hsmul]; simp
  have hdvd : q ∣ Nat.card N := hN ▸ dvd_refl q
  obtain ⟨n, hn_fix, hn_ne⟩ :=
    hK.exists_fixed_point_of_prime_dvd_card_of_fixed_point N hdvd hfix1
  have hn_center : (n : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro k
    have h2 : k * (n : K) * k⁻¹ = (n : K) := by
      have := congrArg (Subtype.val) (hn_fix k); rwa [hsmul] at this
    calc k * (n : K) = (k * (n : K) * k⁻¹) * k := by group
      _ = (n : K) * k := by rw [h2]
  -- `N ⊓ center` is nontrivial (contains `n ≠ 1`) and ≤ `N` of prime order, so `= N`
  have hmem : (n : K) ∈ N ⊓ Subgroup.center K := ⟨n.2, hn_center⟩
  have hne_bot : (N ⊓ Subgroup.center K) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hn_ne (Subtype.ext hmem).symm
  have hdvd2 : Nat.card (N ⊓ Subgroup.center K : Subgroup K) ∣ q :=
    hN ▸ Subgroup.card_dvd_of_le inf_le_left
  have hpos : 1 < Nat.card (N ⊓ Subgroup.center K : Subgroup K) :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr hne_bot
  have heqcard : Nat.card (N ⊓ Subgroup.center K : Subgroup K) = Nat.card N := by
    rw [hN]
    rcases (Nat.Prime.eq_one_or_self_of_dvd Fact.out _ hdvd2) with h | h
    · omega
    · exact h
  have hEq : (N ⊓ Subgroup.center K) = N :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq heqcard.symm)
  rw [← hEq]; exact inf_le_right

/-- **`subA` is the unique order-`p³` subgroup admitting a primitive character.**
If `K ≤ Model p d` has `|K| = p³` and some character `χ : K →* ℂˣ` takes a value
`χ(g)` with `χ(g)ᵖ ≠ 1` (a primitive `p²`-th root), then `K = subA p d`.  Proof:
`χ(g)` has order `p²`, and every value `χ(k)` satisfies `χ(k)^{p²} = 1` (model
exponent `p²`), so the cyclic image `χ.range` has order exactly `p²`; hence
`|ker χ| = p`, so `ker χ ≤ center K` (`prime_normal_le_center`), whence
`K/center K` is cyclic (a quotient of `K/ker χ ≅ χ.range`) and `K` is abelian —
so `K = subA` by `eq_subA_of_abelian_maximal`. -/
theorem eq_subA_of_char_primitive {d : ZMod p} (hp5 : 5 ≤ p) (K : Subgroup (Model p d))
    (hcard : Nat.card K = p ^ 3) (χ : K →* ℂˣ) (g : K)
    (hg : ((χ g : ℂˣ) : ℂ) ^ p ≠ 1) :
    K = subA p d := by
  have hp : p.Prime := Fact.out
  haveI : Finite K := Subtype.finite
  have hKp : IsPGroup p K := IsPGroup.of_card hcard
  -- every value is killed by `p²`; `χ(g)` has order exactly `p²`
  have hkill : ∀ x : K, (χ x) ^ (p ^ 2) = 1 := by
    intro x
    rw [← map_pow, show x ^ (p ^ 2) = 1 from
      Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]; exact model_pow_psq hp5 (x : Model p d)),
      map_one]
  have hgpu : (χ g) ^ p ≠ 1 :=
    fun h => hg (by rw [← Units.val_pow_eq_pow_val, h, Units.val_one])
  have horder : orderOf (χ g) = p ^ 2 :=
    orderOf_eq_prime_pow (by rw [pow_one]; exact hgpu) (hkill g)
  -- the image is cyclic of order exactly `p²`
  haveI : Finite χ.range := (Set.finite_range χ).to_subtype
  haveI : IsCyclic χ.range := isCyclic_subgroup_units _
  have hoe : orderOf (⟨χ g, ⟨g, rfl⟩⟩ : χ.range) = p ^ 2 :=
    (orderOf_injective χ.range.subtype Subtype.val_injective
      (⟨χ g, ⟨g, rfl⟩⟩ : χ.range)) ▸ horder
  have hp2_dvd : p ^ 2 ∣ Nat.card χ.range := hoe ▸ orderOf_dvd_natCard _
  have hdvd_p2 : Nat.card χ.range ∣ p ^ 2 := by
    obtain ⟨y, hy⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := χ.range)
    obtain ⟨k, hk⟩ := y.2
    rw [← hy]
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    change (y : ℂˣ) ^ (p ^ 2) = 1
    rw [← hk, hkill k]
  have hrange : Nat.card χ.range = p ^ 2 := Nat.dvd_antisymm hdvd_p2 hp2_dvd
  -- `|ker χ| = p`
  have hlagrange : Nat.card K = Nat.card χ.range * Nat.card (χ.ker) := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange χ).toEquiv]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup χ.ker)
  have hker : Nat.card (χ.ker) = p := by
    rw [hcard, hrange] at hlagrange
    have : p ^ 3 = p ^ 2 * p := by ring
    rw [this] at hlagrange
    exact (Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) hlagrange.symm)
  -- `ker χ ≤ center K`, so `K` is abelian
  have hkc : χ.ker ≤ Subgroup.center K := prime_normal_le_center hKp χ.ker hker
  have hcomm : ∀ x y : K, x * y = y * x :=
    (χ.rangeRestrict.isMulCommutative_of_isCyclic_of_ker_le_center
      (by rw [MonoidHom.ker_rangeRestrict]; exact hkc)).is_comm.comm
  refine eq_subA_of_abelian_maximal K hcard (fun x hx y hy => ?_)
  exact congrArg Subtype.val (hcomm ⟨x, hx⟩ ⟨y, hy⟩)

end LeanDring.P4
