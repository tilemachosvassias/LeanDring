/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P4.ModularModels
import LeanDring.P4.LastModels
import LeanDring.P4.NoTableIso
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.IndexNormal
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Cast.Lemmas

-- Several statements below do not mention the section's `[Fintype _]` /
-- group binders, but their proofs need them for instance synthesis, so the
-- binders cannot be `omit`ted.  The linters' suggested rewrite to `[Finite _]`
-- plus `Fintype.ofFinite` is a genuine refactor, not a cleanup.
set_option linter.unusedSectionVars false

/-!
# Closing the last order-`p⁴` species-table pair: `G9` vs `Gid3`

The final residual pair `(G9, Gid3)` of the order-`p⁴` sweep is tied on every
subgroup-count column through order `p²`, and is separated only at order `p³`.

In a group of order `p⁴` the order-`p³` subgroups are exactly the index-`p`
(= maximal) subgroups; being of index the smallest prime factor they are
normal, with quotient `≅ C_p`.  Counting them by **Hom-counting**:

  `#{index-p subgroups} · (p-1) = |Hom(G, C_p)| - 1`,

where `|Hom(G, C_p)| = Nat.card (G →* Multiplicative (ZMod p))` is a direct
count on the concrete group.  For the two models:

* `|Hom(G9, C_p)| = p³`  (⟹ `p²+p+1` subgroups of order `p³`);
* `|Hom(Gid3, C_p)| = p²` (⟹ `p+1` subgroups of order `p³`).

`SpeciesTableIso.card_subgroups_eq (p^3)` forces these equal — contradiction.
-/

namespace LeanDring

namespace P4

open DRing Finset

variable {p : ℕ} [Fact p.Prime] [Fact (Odd p)]

/-! ## Section A: counting homomorphisms into `C_p = Multiplicative (ZMod p)` -/

instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
/-- `|Multiplicative (ZMod p)| = p`. -/
theorem card_multZMod : Nat.card (Multiplicative (ZMod p)) = p := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

/-- The additive endomorphisms of `ZMod n` number `n` (determined by the image
of `1`). -/
theorem card_zmod_addEndo (n : ℕ) [NeZero n] :
    Nat.card (ZMod n →+ ZMod n) = n := by
  have hall : ∀ a : ZMod n, ((n : ℤ) • a) = 0 := fun a => by
    rw [zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]
  calc
    Nat.card (ZMod n →+ ZMod n)
        = Nat.card {f : ℤ →+ ZMod n // f n = 0} :=
          (Nat.card_congr (ZMod.lift n)).symm
    _ = Nat.card {a : ZMod n // (zmultiplesHom (ZMod n) a) (n : ℤ) = 0} :=
          (Nat.card_congr
            (Equiv.subtypeEquiv (zmultiplesHom (ZMod n)) (fun a => Iff.rfl))).symm
    _ = Nat.card (ZMod n) :=
          Nat.card_congr (Equiv.subtypeUnivEquiv (fun a => by
            rw [zmultiplesHom_apply]; exact hall a))
    _ = n := Nat.card_zmod n

omit [Fact (Odd p)] in
/-- For a group `Q` of prime order `p`, `|Hom(Q, C_p)| = p`. -/
theorem card_hom_multZMod_of_card_p {Q : Type*} [Group Q] (hQ : Nat.card Q = p) :
    Nat.card (Q →* Multiplicative (ZMod p)) = p := by
  have e : Q ≃* Multiplicative (ZMod p) :=
    mulEquivOfPrimeCardEq hQ card_multZMod
  rw [Nat.card_congr (MulEquiv.monoidHomCongrLeftEquiv (N := Multiplicative (ZMod p)) e),
    Nat.card_congr (AddMonoidHom.toMultiplicative (α := ZMod p) (β := ZMod p)).symm]
  exact card_zmod_addEndo p

/-! ## Section B: the Hom-counting bridge for a group of order `p⁴` -/

section Bridge

variable {G : Type*} [Group G] [Finite G]

instance finite_hom_multZMod : Finite (G →* Multiplicative (ZMod p)) :=
  Finite.of_injective (fun f => (f : G → Multiplicative (ZMod p)))
    DFunLike.coe_injective

omit [Finite G] in
omit [Fact (Odd p)] in
/-- A nonzero character has kernel of index `p`. -/
theorem nonzero_hom_ker_index (φ : G →* Multiplicative (ZMod p)) (hφ : φ ≠ 1) :
    φ.ker.index = p := by
  have hp : p.Prime := Fact.out
  rw [Subgroup.index_ker]
  have hdvd : Nat.card (φ.range) ∣ p := by
    have := Subgroup.card_subgroup_dvd_card (φ.range)
    rwa [card_multZMod] at this
  have hne : Nat.card (φ.range) ≠ 1 := by
    intro h1
    rw [Subgroup.card_eq_one] at h1
    apply hφ
    ext g
    have hg : φ g ∈ φ.range := ⟨g, rfl⟩
    rw [h1, Subgroup.mem_bot] at hg
    simpa using hg
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact absurd h hne
  · exact h

omit [Fact (Odd p)] [Finite G] in
/-- **Killing count**: the characters vanishing on a normal subgroup `H` are in
bijection with `Hom(G ⧸ H, C_p)`. -/
theorem card_killing (H : Subgroup G) [H.Normal] :
    Nat.card {φ : G →* Multiplicative (ZMod p) // H ≤ φ.ker} =
      Nat.card (G ⧸ H →* Multiplicative (ZMod p)) := by
  have e1 : {φ : G →* Multiplicative (ZMod p) // H ≤ φ.ker} ≃
      ((MonoidHom.restrictHom H (Multiplicative (ZMod p))).ker) := by
    apply Equiv.subtypeEquivRight
    intro φ
    rw [MonoidHom.mem_ker, MonoidHom.restrictHom_apply,
      MonoidHom.restrict_eq_one_iff]
    constructor
    · intro h x hx; exact MonoidHom.mem_ker.mp (h hx)
    · intro h x hx; exact MonoidHom.mem_ker.mpr (h x hx)
  rw [Nat.card_congr e1,
    Nat.card_congr (MonoidHom.restrictHomKerEquiv (Multiplicative (ZMod p)) H).toEquiv]

omit [Fact (Odd p)] in
/-- **The bridge**, order-`p⁴` form: the number of index-`p` subgroups times
`p-1` equals `|Hom(G, C_p)| - 1`. -/
theorem card_index_p_mul (hG4 : Nat.card G = p ^ 4) :
    Nat.card {H : Subgroup G // H.index = p} * (p - 1) =
      Nat.card (G →* Multiplicative (ZMod p)) - 1 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (G →* Multiplicative (ZMod p)) := Fintype.ofFinite _
  haveI : Fintype (Subgroup G) := Fintype.ofFinite _
  have hp : p.Prime := Fact.out
  -- the fiber (kernel) count for a fixed index-`p` subgroup
  have hfiber : ∀ H : Subgroup G, H.index = p →
      (univ.filter (fun φ : G →* Multiplicative (ZMod p) => φ.ker = H)).card
        = p - 1 := by
    intro H hH
    haveI hnorm : H.Normal := by
      have hidxmin : H.index = (Nat.card G).minFac := by
        rw [hH, hG4, hp.pow_minFac (k := 4) (by norm_num)]
      exact Subgroup.normal_of_index_eq_minFac_card hidxmin
    -- number of characters killing H is p
    have hkill : (univ.filter
        (fun φ : G →* Multiplicative (ZMod p) => H ≤ φ.ker)).card = p := by
      have h := card_killing (p := p) H
      have hQ : Nat.card (G ⧸ H) = p := by rw [← Subgroup.index_eq_card, hH]
      rw [card_hom_multZMod_of_card_p hQ] at h
      have hconv : (univ.filter
          (fun φ : G →* Multiplicative (ZMod p) => H ≤ φ.ker)).card
          = Nat.card {φ : G →* Multiplicative (ZMod p) // H ≤ φ.ker} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      rw [hconv]; exact h
    -- rewrite the exact-kernel filter as the killing filter with `1` erased
    have hsub : (univ.filter
        (fun φ : G →* Multiplicative (ZMod p) => φ.ker = H))
        = (univ.filter
            (fun φ : G →* Multiplicative (ZMod p) => H ≤ φ.ker)).erase 1 := by
      ext φ
      simp only [mem_filter, mem_univ, true_and, mem_erase]
      constructor
      · intro hker
        refine ⟨?_, le_of_eq hker.symm⟩
        intro h1
        rw [h1, MonoidHom.ker_one] at hker
        have : H.index = 1 := by rw [← hker]; exact Subgroup.index_top
        rw [this] at hH; exact hp.ne_one hH.symm
      · rintro ⟨h1, hle⟩
        -- `H ≤ φ.ker`, `φ ≠ 1` ⟹ `φ.ker = H` by maximality of `H`
        have hkerne : φ.ker ≠ ⊤ := by
          intro htop
          exact h1 (MonoidHom.ker_eq_top_iff.mp htop)
        have hidx : φ.ker.index = p := by
          have hdvd : φ.ker.index ∣ H.index := Subgroup.index_dvd_of_le hle
          rw [hH] at hdvd
          rcases (Nat.dvd_prime hp).mp hdvd with h | h
          · exact absurd (Subgroup.index_eq_one.mp h) hkerne
          · exact h
        have hcard : Nat.card φ.ker = Nat.card H := by
          have e1 := Subgroup.card_mul_index φ.ker
          have e2 := Subgroup.card_mul_index H
          rw [hidx, hG4] at e1
          rw [hH, hG4] at e2
          have hp0 : 0 < p := hp.pos
          have := e1.trans e2.symm
          exact Nat.eq_of_mul_eq_mul_right hp0 this
        exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)).symm
    rw [hsub, Finset.card_erase_of_mem, hkill]
    simp only [mem_filter, mem_univ, true_and, MonoidHom.ker_one, le_top]
  -- count the nonzero characters fiberwise over their kernels
  have hstep : (univ.filter
      (fun φ : G →* Multiplicative (ZMod p) => φ ≠ 1)).card
      = (univ.filter (fun H : Subgroup G => H.index = p)).card * (p - 1) := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun φ : G →* Multiplicative (ZMod p) => φ.ker)
      (t := univ.filter (fun H : Subgroup G => H.index = p))
      (fun φ hφ => Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,
          nonzero_hom_ker_index φ (Finset.mem_filter.mp hφ).2⟩)]
    rw [Finset.sum_congr rfl (fun H hH => ?_), Finset.sum_const, smul_eq_mul,
      mul_comm]
    · -- each fiber has `p-1` elements
      simp only [mem_filter, mem_univ, true_and] at hH
      have : (univ.filter (fun φ : G →* Multiplicative (ZMod p) =>
          φ ≠ 1)).filter (fun φ => φ.ker = H)
          = univ.filter (fun φ => φ.ker = H) := by
        ext φ
        simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
        intro hker h1
        rw [h1, MonoidHom.ker_one] at hker
        have : H.index = 1 := by rw [← hker]; exact Subgroup.index_top
        rw [this] at hH; exact hp.ne_one hH.symm
      rw [this, hfiber H hH]
  -- translate the two Finset cardinalities to `Nat.card`
  have hLHS : (univ.filter
      (fun φ : G →* Multiplicative (ZMod p) => φ ≠ 1)).card
      = Nat.card (G →* Multiplicative (ZMod p)) - 1 := by
    have hone : (1 : G →* Multiplicative (ZMod p)) ∈
        univ.filter (fun φ => φ = 1) := by simp
    have : univ.filter (fun φ : G →* Multiplicative (ZMod p) => φ ≠ 1)
        = univ.erase 1 := by
      ext φ; simp only [mem_filter, mem_univ, true_and, mem_erase, and_true]
    rw [this, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ,
      Nat.card_eq_fintype_card]
  have hRHS : (univ.filter (fun H : Subgroup G => H.index = p)).card
      = Nat.card {H : Subgroup G // H.index = p} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← hLHS, hstep, hRHS]

omit [Fact (Odd p)] [Finite G] in
/-- For `|G| = p⁴`, order-`p³` subgroups are exactly the index-`p` subgroups. -/
theorem card_order_p3_eq_index_p (hG4 : Nat.card G = p ^ 4) :
    Nat.card {H : Subgroup G // Nat.card H = p ^ 3} =
      Nat.card {H : Subgroup G // H.index = p} := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro H
  have hkey := Subgroup.card_mul_index H
  rw [hG4] at hkey
  have hp : p.Prime := Fact.out
  have hp0 : 0 < p := hp.pos
  constructor
  · intro hcard
    rw [hcard] at hkey
    have : p ^ 3 * p ^ 1 = p ^ 3 * H.index := by
      rw [pow_one]; rw [hkey]; ring
    have h3 : 0 < p ^ 3 := pow_pos hp0 3
    have := Nat.eq_of_mul_eq_mul_left h3 this
    rw [pow_one] at this; exact this.symm
  · intro hidx
    rw [hidx] at hkey
    have : Nat.card H * p = p ^ 3 * p := by rw [hkey]; ring
    exact Nat.eq_of_mul_eq_mul_right hp0 this

end Bridge

omit [Fact (Odd p)] in
/-- The number of order-`p³` subgroups from the number of characters, for a
group of order `p⁴`. -/
theorem card_order_p3_of_card_hom {G : Type*} [Group G] [Finite G]
    (hG4 : Nat.card G = p ^ 4) :
    Nat.card {H : Subgroup G // Nat.card H = p ^ 3} * (p - 1) =
      Nat.card (G →* Multiplicative (ZMod p)) - 1 := by
  rw [card_order_p3_eq_index_p hG4, card_index_p_mul hG4]

/-! ## Section C: the two direct character counts -/

/-- Splitting a character of a product (with commutative target). -/
def homProdEquiv {M N P : Type*} [Monoid M] [Monoid N] [CommMonoid P] :
    (M × N →* P) ≃ (M →* P) × (N →* P) where
  toFun f := (f.comp (MonoidHom.inl M N), f.comp (MonoidHom.inr M N))
  invFun gh := gh.1.coprod gh.2
  left_inv f := MonoidHom.coprod_unique f
  right_inv gh := by
    ext
    · simp [MonoidHom.coprod_comp_inl]
    · simp [MonoidHom.coprod_comp_inr]

/-! ### `Mod3` -/

namespace Mod3

/-- The character of `Mod3` attached to a pair `(r,s) ∈ (ZMod p)²`:
`⟨α,u⟩ ↦ r·(α mod p) + s·u` (additively in `ZMod p`). -/
def homOfPair (rs : ZMod p × ZMod p) : Mod3 p →* Multiplicative (ZMod p) where
  toFun x := Multiplicative.ofAdd (rs.1 * redp p x.α + rs.2 * x.u)
  map_one' := by
    change Multiplicative.ofAdd (rs.1 * redp p (0 : ZMod (p ^ 2)) + rs.2 * 0) = 1
    rw [map_zero, mul_zero, mul_zero, add_zero]; rfl
  map_mul' x y := by
    change Multiplicative.ofAdd (rs.1 * redp p (x.α + y.α + liftp p (x.u * redp p y.α))
          + rs.2 * (x.u + y.u))
        = Multiplicative.ofAdd (rs.1 * redp p x.α + rs.2 * x.u)
          * Multiplicative.ofAdd (rs.1 * redp p y.α + rs.2 * y.u)
    rw [← ofAdd_add]
    congr 1
    rw [map_add, map_add, redp_liftp, add_zero]
    ring

/-- `⟨α,u⟩ = a^{α.val} · b^{u.val}` with `a = ⟨1,0⟩`, `b = ⟨0,1⟩`. -/
theorem gen_decomp (α : ZMod (p ^ 2)) (u : ZMod p) :
    (⟨α, u⟩ : Mod3 p) = (⟨1, 0⟩ : Mod3 p) ^ α.val * (⟨0, 1⟩ : Mod3 p) ^ u.val := by
  have ha : (⟨1, 0⟩ : Mod3 p) ^ α.val = ⟨α, 0⟩ := by
    rw [pow_formula]
    refine Mod3.ext ?_ ?_
    · change (α.val : ZMod (p ^ 2)) * 1
          + liftp p (tri p (α.val : ZMod p) * (0 * redp p 1)) = α
      rw [zero_mul, mul_zero, liftp_zero, add_zero, mul_one, ZMod.natCast_zmod_val]
    · change (α.val : ZMod p) * 0 = 0
      rw [mul_zero]
  have hb : (⟨0, 1⟩ : Mod3 p) ^ u.val = ⟨0, u⟩ := by
    rw [pow_formula]
    refine Mod3.ext ?_ ?_
    · change (u.val : ZMod (p ^ 2)) * 0
          + liftp p (tri p (u.val : ZMod p) * (1 * redp p 0)) = 0
      rw [mul_zero, map_zero, mul_zero, mul_zero, liftp_zero, add_zero]
    · change (u.val : ZMod p) * 1 = u
      rw [mul_one, ZMod.natCast_zmod_val]
  rw [ha, hb, mul_def]
  refine Mod3.ext ?_ ?_
  · change α = α + 0 + liftp p (0 * redp p 0)
    rw [zero_mul, liftp_zero, add_zero, add_zero]
  · change u = 0 + u
    rw [zero_add]

/-- `|Hom(Mod3, C_p)| = p²`. -/
theorem card_hom : Nat.card (Mod3 p →* Multiplicative (ZMod p)) = p ^ 2 := by
  have e : (Mod3 p →* Multiplicative (ZMod p)) ≃ ZMod p × ZMod p := by
    refine ⟨fun φ => ((φ ⟨1, 0⟩).toAdd, (φ ⟨0, 1⟩).toAdd),
      fun rs => homOfPair rs, ?_, ?_⟩
    · intro φ
      ext x
      obtain ⟨α, u⟩ := x
      change Multiplicative.ofAdd ((φ ⟨1, 0⟩).toAdd * redp p α +
        (φ ⟨0, 1⟩).toAdd * u) = φ ⟨α, u⟩
      have hα : redp p α = (α.val : ZMod p) := by
        simp only [redp, ZMod.castHom_apply, ZMod.natCast_val]
      have hval : (φ ⟨α, u⟩).toAdd =
          (φ ⟨1, 0⟩).toAdd * redp p α + (φ ⟨0, 1⟩).toAdd * u := by
        rw [gen_decomp α u]
        simp only [map_mul, map_pow, toAdd_mul, toAdd_pow, nsmul_eq_mul]
        rw [hα, ZMod.natCast_zmod_val u]
        ring
      rw [← hval]
      exact ofAdd_toAdd _
    · intro rs
      ext
      · change ((homOfPair rs) ⟨1, 0⟩).toAdd = rs.1
        change (Multiplicative.ofAdd (rs.1 * redp p (1 : ZMod (p ^ 2))
          + rs.2 * 0)).toAdd = rs.1
        rw [map_one, mul_one, mul_zero, add_zero, toAdd_ofAdd]
      · change ((homOfPair rs) ⟨0, 1⟩).toAdd = rs.2
        change (Multiplicative.ofAdd (rs.1 * redp p (0 : ZMod (p ^ 2))
          + rs.2 * 1)).toAdd = rs.2
        rw [map_zero, mul_zero, mul_one, zero_add, toAdd_ofAdd]
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_zmod]
  ring

end Mod3

/-- `|Hom(G9, C_p)| = p³`, via `G9 = Mod3 × C_p`. -/
theorem card_hom_g9 :
    Nat.card (G9 p →* Multiplicative (ZMod p)) = p ^ 3 := by
  rw [Nat.card_congr homProdEquiv, Nat.card_prod, Mod3.card_hom,
    card_hom_multZMod_of_card_p (Q := Multiplicative (ZMod p)) card_multZMod]
  ring

/-! ### `Gid3` -/

namespace Gid3

/-- The character of `Gid3` attached to a pair `(r,s)`:
`⟨α,y,u⟩ ↦ r·(α mod p) + s·u` (the central `y`-coordinate is killed). -/
def homOfPair (rs : ZMod p × ZMod p) : Gid3 p →* Multiplicative (ZMod p) where
  toFun x := Multiplicative.ofAdd (rs.1 * redp p x.α + rs.2 * x.u)
  map_one' := by
    change Multiplicative.ofAdd (rs.1 * redp p (0 : ZMod (p ^ 2)) + rs.2 * 0) = 1
    rw [map_zero, mul_zero, mul_zero, add_zero]; rfl
  map_mul' x y := by
    change Multiplicative.ofAdd (rs.1 * redp p (x.α + y.α) + rs.2 * (x.u + y.u))
        = Multiplicative.ofAdd (rs.1 * redp p x.α + rs.2 * x.u)
          * Multiplicative.ofAdd (rs.1 * redp p y.α + rs.2 * y.u)
    rw [← ofAdd_add]
    congr 1
    rw [map_add]
    ring

/-- `⟨α,y,u⟩ = a^{α.val} · c^{y.val} · b^{u.val}`. -/
theorem gen_decomp (α : ZMod (p ^ 2)) (y u : ZMod p) :
    (⟨α, y, u⟩ : Gid3 p) =
      (⟨1, 0, 0⟩ : Gid3 p) ^ α.val * (⟨0, 1, 0⟩ : Gid3 p) ^ y.val
        * (⟨0, 0, 1⟩ : Gid3 p) ^ u.val := by
  have ha : (⟨1, 0, 0⟩ : Gid3 p) ^ α.val = ⟨α, 0, 0⟩ := by
    rw [pow_formula]
    ext
    · change (α.val : ZMod (p ^ 2)) * 1 = α
      rw [mul_one, ZMod.natCast_zmod_val]
    · change (α.val : ZMod p) * 0 + tri p ((α.val : ZMod p)) * (0 * redp p 1) = 0
      rw [mul_zero, zero_mul, mul_zero, add_zero]
    · change (α.val : ZMod p) * 0 = 0
      rw [mul_zero]
  have hc : (⟨0, 1, 0⟩ : Gid3 p) ^ y.val = ⟨0, y, 0⟩ := by
    rw [pow_formula]
    ext
    · change (y.val : ZMod (p ^ 2)) * 0 = 0
      rw [mul_zero]
    · change (y.val : ZMod p) * 1 + tri p ((y.val : ZMod p)) * (0 * redp p 0) = y
      rw [mul_one, zero_mul, mul_zero, add_zero, ZMod.natCast_zmod_val]
    · change (y.val : ZMod p) * 0 = 0
      rw [mul_zero]
  have hb : (⟨0, 0, 1⟩ : Gid3 p) ^ u.val = ⟨0, 0, u⟩ := by
    rw [pow_formula]
    ext
    · change (u.val : ZMod (p ^ 2)) * 0 = 0
      rw [mul_zero]
    · change (u.val : ZMod p) * 0 + tri p ((u.val : ZMod p)) * (1 * redp p 0) = 0
      rw [map_zero, mul_zero, mul_zero, zero_add, mul_zero]
    · change (u.val : ZMod p) * 1 = u
      rw [mul_one, ZMod.natCast_zmod_val]
  rw [ha, hc, hb]
  refine Gid3.ext ?_ ?_ ?_ <;>
    simp only [mul_def, zero_mul, add_zero, zero_add]

-- `Fact (Odd p)` is needed transitively: omitting it stops `simp only [mul_def]`
-- from unifying against the `Gid3 p` multiplication, so the linter is wrong here.
/-- Any character kills the central commutator `c = ⟨0,1,0⟩`. -/
theorem hom_c_eq_one (φ : Gid3 p →* Multiplicative (ZMod p)) :
    φ ⟨0, 1, 0⟩ = 1 := by
  have e1 : (⟨0, 0, 1⟩ : Gid3 p) * ⟨1, 0, 0⟩
      = ⟨1, 0, 0⟩ * ⟨0, 0, 1⟩ * ⟨0, 1, 0⟩ := by
    refine Gid3.ext ?_ ?_ ?_ <;>
      simp only [mul_def, map_one, map_zero] <;> ring
  have h := congrArg φ e1
  rw [map_mul, map_mul, map_mul, mul_comm (φ ⟨0, 0, 1⟩) (φ ⟨1, 0, 0⟩)] at h
  exact left_eq_mul.mp h

/-- `|Hom(Gid3, C_p)| = p²`. -/
theorem card_hom : Nat.card (Gid3 p →* Multiplicative (ZMod p)) = p ^ 2 := by
  have e : (Gid3 p →* Multiplicative (ZMod p)) ≃ ZMod p × ZMod p := by
    refine ⟨fun φ => ((φ ⟨1, 0, 0⟩).toAdd, (φ ⟨0, 0, 1⟩).toAdd),
      fun rs => homOfPair rs, ?_, ?_⟩
    · intro φ
      ext x
      obtain ⟨α, y, u⟩ := x
      change Multiplicative.ofAdd ((φ ⟨1, 0, 0⟩).toAdd * redp p α +
        (φ ⟨0, 0, 1⟩).toAdd * u) = φ ⟨α, y, u⟩
      have hα : redp p α = (α.val : ZMod p) := by
        simp only [redp, ZMod.castHom_apply, ZMod.natCast_val]
      have hval : (φ ⟨α, y, u⟩).toAdd =
          (φ ⟨1, 0, 0⟩).toAdd * redp p α + (φ ⟨0, 0, 1⟩).toAdd * u := by
        rw [gen_decomp α y u]
        simp only [map_mul, map_pow, hom_c_eq_one φ, one_pow, mul_one,
          toAdd_mul, toAdd_pow, nsmul_eq_mul]
        rw [hα, ZMod.natCast_zmod_val u]
        ring
      rw [← hval]
      exact ofAdd_toAdd _
    · intro rs
      ext
      · change ((homOfPair rs) ⟨1, 0, 0⟩).toAdd = rs.1
        change (Multiplicative.ofAdd (rs.1 * redp p (1 : ZMod (p ^ 2))
          + rs.2 * 0)).toAdd = rs.1
        rw [map_one, mul_one, mul_zero, add_zero, toAdd_ofAdd]
      · change ((homOfPair rs) ⟨0, 0, 1⟩).toAdd = rs.2
        change (Multiplicative.ofAdd (rs.1 * redp p (0 : ZMod (p ^ 2))
          + rs.2 * 1)).toAdd = rs.2
        rw [map_zero, mul_zero, mul_one, zero_add, toAdd_ofAdd]
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_zmod]
  ring

end Gid3

/-! ## Section D: the subgroup counts and the separation -/

/-- **Order-`p³` subgroups of `G9`**: exactly `p² + p + 1`. -/
theorem card_order_p3_subgroups_g9 :
    Nat.card {H : Subgroup (G9 p) // Nat.card H = p ^ 3} = p ^ 2 + p + 1 := by
  have hG4 : Nat.card (G9 p) = p ^ 4 := by
    rw [Nat.card_prod, Mod3.card_mod3, card_multZMod]; ring
  have h := card_order_p3_of_card_hom (G := G9 p) hG4
  rw [card_hom_g9] at h
  have hp : p.Prime := Fact.out
  have hp1 : 1 < p := hp.one_lt
  have hq : 0 < p - 1 := by omega
  have hg := geom_sum_mul_pred (p := p) 3 hp.one_lt.le
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, pow_zero, pow_one] at hg
  rw [← hg] at h
  rw [Nat.eq_of_mul_eq_mul_right hq h]; ring

/-- **Order-`p³` subgroups of `Gid3`**: exactly `p + 1`. -/
theorem card_order_p3_subgroups_gid3 :
    Nat.card {H : Subgroup (Gid3 p) // Nat.card H = p ^ 3} = p + 1 := by
  have hG4 : Nat.card (Gid3 p) = p ^ 4 := Gid3.card_gid3 p
  have h := card_order_p3_of_card_hom (G := Gid3 p) hG4
  rw [Gid3.card_hom] at h
  have hp : p.Prime := Fact.out
  have hp1 : 1 < p := hp.one_lt
  have hq : 0 < p - 1 := by omega
  have hg := geom_sum_mul_pred (p := p) 2 hp.one_lt.le
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, pow_zero, pow_one] at hg
  rw [← hg] at h
  rw [Nat.eq_of_mul_eq_mul_right hq h]; ring

/-- **G9 vs Gid3**: separated by the order-`p³` subgroup count
(`p²+p+1` vs `p+1`) — the last open pair of the order-`p⁴` sweep. -/
theorem isEmpty_tableIso_g9_gid3 :
    IsEmpty (SpeciesTableIso (G9 p) (Gid3 p)) := by
  constructor
  intro T
  have h := T.card_subgroups_eq (p ^ 3)
  rw [card_order_p3_subgroups_g9, card_order_p3_subgroups_gid3] at h
  have hpos : 0 < p ^ 2 := pow_pos (Fact.out : p.Prime).pos 2
  omega

/-! ## Section E: three further character counts -/

/-! ### `CH7` (generator rank 3) -/

namespace CH7

/-- The character of `CH7` attached to a triple `(r,s,t)`:
`⟨x,y,z⟩ ↦ r·x + s·y + t·(z mod p)` (the `p·C_{p²}` part of `z` is killed). -/
def homOfPair (rst : ZMod p × ZMod p × ZMod p) :
    CH7 p →* Multiplicative (ZMod p) where
  toFun a := Multiplicative.ofAdd (rst.1 * a.x + rst.2.1 * a.y + rst.2.2 * redp p a.z)
  map_one' := by
    change Multiplicative.ofAdd (rst.1 * (0 : ZMod p) + rst.2.1 * 0
      + rst.2.2 * redp p (0 : ZMod (p ^ 2))) = 1
    rw [map_zero, mul_zero, mul_zero, mul_zero, add_zero, add_zero]; rfl
  map_mul' a b := by
    change Multiplicative.ofAdd (rst.1 * (a * b).x + rst.2.1 * (a * b).y
        + rst.2.2 * redp p (a * b).z)
      = Multiplicative.ofAdd (rst.1 * a.x + rst.2.1 * a.y + rst.2.2 * redp p a.z)
        * Multiplicative.ofAdd (rst.1 * b.x + rst.2.1 * b.y + rst.2.2 * redp p b.z)
    rw [← ofAdd_add]
    congr 1
    change rst.1 * (a.x + b.x) + rst.2.1 * (a.y + b.y)
        + rst.2.2 * redp p (a.z + b.z + liftp p (a.x * b.y))
      = rst.1 * a.x + rst.2.1 * a.y + rst.2.2 * redp p a.z
        + (rst.1 * b.x + rst.2.1 * b.y + rst.2.2 * redp p b.z)
    rw [map_add, map_add, redp_liftp, add_zero]
    ring

/-- `⟨x,y,z⟩ = b^{y.val} · a^{x.val} · c^{z.val}` with `a = ⟨1,0,0⟩`,
`b = ⟨0,1,0⟩`, `c = ⟨0,0,1⟩` (this order avoids the `liftp` twist). -/
theorem gen_decomp (x y : ZMod p) (z : ZMod (p ^ 2)) :
    (⟨x, y, z⟩ : CH7 p) =
      (⟨0, 1, 0⟩ : CH7 p) ^ y.val * (⟨1, 0, 0⟩ : CH7 p) ^ x.val
        * (⟨0, 0, 1⟩ : CH7 p) ^ z.val := by
  have ha : (⟨1, 0, 0⟩ : CH7 p) ^ x.val = ⟨x, 0, 0⟩ := by
    rw [pow_formula]
    refine CH7.ext ?_ ?_ ?_
    · change (x.val : ZMod p) * 1 = x
      rw [mul_one, ZMod.natCast_zmod_val]
    · change (x.val : ZMod p) * 0 = 0
      rw [mul_zero]
    · change (x.val : ZMod (p ^ 2)) * 0
          + liftp p (tri p (x.val : ZMod p) * (1 * 0)) = 0
      rw [mul_zero, mul_zero, mul_zero, liftp_zero, add_zero]
  have hb : (⟨0, 1, 0⟩ : CH7 p) ^ y.val = ⟨0, y, 0⟩ := by
    rw [pow_formula]
    refine CH7.ext ?_ ?_ ?_
    · change (y.val : ZMod p) * 0 = 0
      rw [mul_zero]
    · change (y.val : ZMod p) * 1 = y
      rw [mul_one, ZMod.natCast_zmod_val]
    · change (y.val : ZMod (p ^ 2)) * 0
          + liftp p (tri p (y.val : ZMod p) * (0 * 1)) = 0
      rw [mul_zero, zero_mul, mul_zero, liftp_zero, add_zero]
  have hc : (⟨0, 0, 1⟩ : CH7 p) ^ z.val = ⟨0, 0, z⟩ := by
    rw [pow_formula]
    refine CH7.ext ?_ ?_ ?_
    · change (z.val : ZMod p) * 0 = 0
      rw [mul_zero]
    · change (z.val : ZMod p) * 0 = 0
      rw [mul_zero]
    · change (z.val : ZMod (p ^ 2)) * 1
          + liftp p (tri p (z.val : ZMod p) * (0 * 0)) = z
      rw [mul_one, mul_zero, mul_zero, liftp_zero, add_zero,
        ZMod.natCast_zmod_val]
  rw [ha, hb, hc]
  refine CH7.ext ?_ ?_ ?_ <;>
    simp only [mul_def, mul_zero, liftp_zero, add_zero, zero_add]

/-- `|Hom(CH7, C_p)| = p³`. -/
theorem card_hom : Nat.card (CH7 p →* Multiplicative (ZMod p)) = p ^ 3 := by
  have e : (CH7 p →* Multiplicative (ZMod p)) ≃ ZMod p × ZMod p × ZMod p := by
    refine ⟨fun φ => ((φ ⟨1, 0, 0⟩).toAdd, (φ ⟨0, 1, 0⟩).toAdd,
      (φ ⟨0, 0, 1⟩).toAdd), fun rst => homOfPair rst, ?_, ?_⟩
    · intro φ
      ext a
      obtain ⟨x, y, z⟩ := a
      change Multiplicative.ofAdd ((φ ⟨1, 0, 0⟩).toAdd * x
        + (φ ⟨0, 1, 0⟩).toAdd * y + (φ ⟨0, 0, 1⟩).toAdd * redp p z) = φ ⟨x, y, z⟩
      have hz : redp p z = (z.val : ZMod p) := by
        simp only [redp, ZMod.castHom_apply, ZMod.natCast_val]
      have hval : (φ ⟨x, y, z⟩).toAdd =
          (φ ⟨1, 0, 0⟩).toAdd * x + (φ ⟨0, 1, 0⟩).toAdd * y
            + (φ ⟨0, 0, 1⟩).toAdd * redp p z := by
        rw [gen_decomp x y z]
        simp only [map_mul, map_pow, toAdd_mul, toAdd_pow, nsmul_eq_mul]
        rw [hz, ZMod.natCast_zmod_val x, ZMod.natCast_zmod_val y]
        ring
      rw [← hval]
      exact ofAdd_toAdd _
    · intro rst
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · change ((homOfPair rst) ⟨1, 0, 0⟩).toAdd = rst.1
        change (Multiplicative.ofAdd (rst.1 * (1 : ZMod p) + rst.2.1 * 0
          + rst.2.2 * redp p (0 : ZMod (p ^ 2)))).toAdd = rst.1
        rw [map_zero, mul_one, mul_zero, mul_zero, add_zero, add_zero,
          toAdd_ofAdd]
      · change ((homOfPair rst) ⟨0, 1, 0⟩).toAdd = rst.2.1
        change (Multiplicative.ofAdd (rst.1 * (0 : ZMod p) + rst.2.1 * 1
          + rst.2.2 * redp p (0 : ZMod (p ^ 2)))).toAdd = rst.2.1
        rw [map_zero, mul_one, mul_zero, mul_zero, add_zero, zero_add,
          toAdd_ofAdd]
      · change ((homOfPair rst) ⟨0, 0, 1⟩).toAdd = rst.2.2
        change (Multiplicative.ofAdd (rst.1 * (0 : ZMod p) + rst.2.1 * 0
          + rst.2.2 * redp p (1 : ZMod (p ^ 2)))).toAdd = rst.2.2
        rw [map_one, mul_one, mul_zero, mul_zero, add_zero, zero_add,
          toAdd_ofAdd]
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, Nat.card_zmod]
  ring

end CH7

/-! ### `Gid8` (generator rank 2) -/

namespace Gid8

/-- The character of `Gid8` attached to a pair `(r,t)`:
`⟨vec,w⟩ ↦ r·vec.1 + t·w` (the twisted coordinates `vec.2` are killed). -/
def homOfPair (rt : ZMod p × ZMod p) : Gid8 p →* Multiplicative (ZMod p) where
  toFun x := Multiplicative.ofAdd (rt.1 * x.vec.1 + rt.2 * x.w)
  map_one' := by
    change Multiplicative.ofAdd (rt.1 * (0 : ZMod p) + rt.2 * (0 : ZMod p)) = 1
    rw [mul_zero, mul_zero, add_zero]; rfl
  map_mul' g h := by
    change Multiplicative.ofAdd (rt.1 * (g * h).vec.1 + rt.2 * (g * h).w)
      = Multiplicative.ofAdd (rt.1 * g.vec.1 + rt.2 * g.w)
        * Multiplicative.ofAdd (rt.1 * h.vec.1 + rt.2 * h.w)
    rw [mul_def, ← ofAdd_add]
    congr 1
    change rt.1 * (g.vec.1 + h.vec.1 + 0) + rt.2 * (g.w + h.w)
      = rt.1 * g.vec.1 + rt.2 * g.w + (rt.1 * h.vec.1 + rt.2 * h.w)
    ring

omit [Fact (Odd p)] in
/-- The carry bit `cbit(j, 1)` vanishes as long as `j + 1 < p` (no wrap). -/
theorem cbitN_succ_zero (j : ℕ) (hj : j + 1 < p) :
    cbitN p ((j : ZMod p)) 1 = 0 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  have hjp : j < p := by omega
  have hval : ((j : ZMod p)).val = j := ZMod.val_natCast_of_lt hjp
  have h1 : (1 : ZMod p).val = 1 := ZMod.val_one p
  have hsum : ((j : ZMod p) + 1).val = j + 1 := by
    rw [← Nat.cast_one, ← Nat.cast_add, ZMod.val_natCast_of_lt hj]
  unfold cbitN
  rw [hval, h1, hsum, Nat.sub_self, Nat.zero_div]

omit [Fact (Odd p)] in
/-- `cbit(1, 0) = 0`. -/
theorem cbitN_one_zero : cbitN p (1 : ZMod p) 0 = 0 := by
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  unfold cbitN
  rw [add_zero]
  simp [ZMod.val_one, ZMod.val_zero]

omit [Fact (Odd p)] in
/-- `cvec(1, 0) = 0`. -/
theorem cvec_one_zero : cvec p (1 : ZMod p) 0 = 0 := by
  unfold cvec
  rw [cbitN_one_zero]
  simp

/-- Powers of a `w = 0` element (`⟨v,0⟩`) are scalar multiples. -/
theorem vec_pow (v : ZMod p × ZMod p × ZMod p) (n : ℕ) :
    (⟨v, 0⟩ : Gid8 p) ^ n = ⟨n • v, 0⟩ := by
  rw [pow_formula]
  dsimp only
  have key : ∀ j : ℕ, actMC p ((j : ZMod p) * 0) v = v :=
    fun j => by rw [mul_zero, actMC_zero]
  have hcbz : (∑ j ∈ range n, cbitN p ((j : ZMod p) * 0) 0) = 0 := by
    apply Finset.sum_eq_zero; intro j _; rw [mul_zero]; unfold cbitN; simp
  simp only [key, Finset.sum_const, Finset.card_range, hcbz, Nat.cast_zero]
  refine Gid8.ext ?_ ?_ <;> simp

/-- Powers of the outer generator `s = ⟨(0,0,0),1⟩` below `p` have no carry:
`s^{w.val} = ⟨(0,0,0), w⟩`. -/
theorem s_pow (w : ZMod p) :
    (⟨(0, 0, 0), 1⟩ : Gid8 p) ^ w.val = ⟨(0, 0, 0), w⟩ := by
  rw [pow_formula]
  dsimp only
  have hact : (∑ j ∈ range w.val,
      actMC p ((j : ZMod p) * 1) ((0, 0, 0) : ZMod p × ZMod p × ZMod p)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _; exact MaxClass.actMC_zero_vec _
  have hcb : ((∑ j ∈ range w.val, cbitN p ((j : ZMod p) * 1) 1 : ℕ) : ZMod p) = 0 := by
    have hz : (∑ j ∈ range w.val, cbitN p ((j : ZMod p) * 1) 1) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [mul_one]
      have hjw : j < w.val := Finset.mem_range.mp hj
      have hwv : w.val < p := ZMod.val_lt w
      exact cbitN_succ_zero j (by omega)
    rw [hz]; simp
  refine Gid8.ext ?_ ?_
  · rw [hact, zero_add]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    exact hcb
  · change ((w.val : ℕ) : ZMod p) * 1 = w
    rw [mul_one, ZMod.natCast_zmod_val]

/-- `⟨(a1,a2,a3),w⟩ = e1^{a1} e2^{a2} e3^{a3} s^{w}` on generators. -/
theorem gen_decomp (a1 a2 a3 w : ZMod p) :
    (⟨(a1, a2, a3), w⟩ : Gid8 p) =
      (⟨(1, 0, 0), 0⟩ : Gid8 p) ^ a1.val * (⟨(0, 1, 0), 0⟩ : Gid8 p) ^ a2.val
        * (⟨(0, 0, 1), 0⟩ : Gid8 p) ^ a3.val * (⟨(0, 0, 0), 1⟩ : Gid8 p) ^ w.val := by
  have ha : (⟨(1, 0, 0), 0⟩ : Gid8 p) ^ a1.val = ⟨(a1, 0, 0), 0⟩ := by
    rw [vec_pow]
    refine Gid8.ext ?_ rfl
    simp [Prod.smul_mk, nsmul_eq_mul]
  have hb : (⟨(0, 1, 0), 0⟩ : Gid8 p) ^ a2.val = ⟨(0, a2, 0), 0⟩ := by
    rw [vec_pow]
    refine Gid8.ext ?_ rfl
    simp [Prod.smul_mk, nsmul_eq_mul]
  have hc : (⟨(0, 0, 1), 0⟩ : Gid8 p) ^ a3.val = ⟨(0, 0, a3), 0⟩ := by
    rw [vec_pow]
    refine Gid8.ext ?_ rfl
    simp [Prod.smul_mk, nsmul_eq_mul]
  rw [ha, hb, hc, s_pow]
  refine Gid8.ext ?_ ?_ <;>
    simp only [mul_def, actMC_zero, cvec_zero, Prod.mk_add_mk,
      add_zero, zero_add]

/-- Any character kills the central generator `e3 = ⟨(0,0,1),0⟩`, via
`s·e2 = e2·s·e3`. -/
theorem hom_e3_eq_one (φ : Gid8 p →* Multiplicative (ZMod p)) :
    φ ⟨(0, 0, 1), 0⟩ = 1 := by
  have e1 : (⟨(0, 0, 0), 1⟩ : Gid8 p) * ⟨(0, 1, 0), 0⟩
      = ⟨(0, 1, 0), 0⟩ * ⟨(0, 0, 0), 1⟩ * ⟨(0, 0, 1), 0⟩ := by
    refine Gid8.ext ?_ ?_
    · simp only [mul_def, actMC_zero, cvec_zero, cvec_one_zero, add_zero, zero_add]
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
        simp only [actMC, tri, Prod.fst_add, Prod.snd_add] <;> ring
    · simp only [mul_def]; ring
  have h := congrArg φ e1
  rw [map_mul, map_mul, map_mul,
    mul_comm (φ ⟨(0, 0, 0), 1⟩) (φ ⟨(0, 1, 0), 0⟩)] at h
  exact left_eq_mul.mp h

/-- Any character kills `e2 = ⟨(0,1,0),0⟩`, via `s·e1·e3 = e1·s·e2`. -/
theorem hom_e2_eq_one (φ : Gid8 p →* Multiplicative (ZMod p)) :
    φ ⟨(0, 1, 0), 0⟩ = 1 := by
  have e1 : (⟨(0, 0, 0), 1⟩ : Gid8 p) * ⟨(1, 0, 0), 0⟩ * ⟨(0, 0, 1), 0⟩
      = ⟨(1, 0, 0), 0⟩ * ⟨(0, 0, 0), 1⟩ * ⟨(0, 1, 0), 0⟩ := by
    refine Gid8.ext ?_ ?_
    · simp only [mul_def, actMC_zero, cvec_zero, cvec_one_zero, add_zero, zero_add]
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
        simp only [actMC, tri, Prod.fst_add, Prod.snd_add] <;> ring
    · simp only [mul_def]; ring
  have h := congrArg φ e1
  rw [map_mul, map_mul, map_mul, map_mul, hom_e3_eq_one φ, mul_one,
    mul_comm (φ ⟨(0, 0, 0), 1⟩) (φ ⟨(1, 0, 0), 0⟩)] at h
  exact left_eq_mul.mp h

/-- `|Hom(Gid8, C_p)| = p²`. -/
theorem card_hom : Nat.card (Gid8 p →* Multiplicative (ZMod p)) = p ^ 2 := by
  have e : (Gid8 p →* Multiplicative (ZMod p)) ≃ ZMod p × ZMod p := by
    refine ⟨fun φ => ((φ ⟨(1, 0, 0), 0⟩).toAdd, (φ ⟨(0, 0, 0), 1⟩).toAdd),
      fun rt => homOfPair rt, ?_, ?_⟩
    · intro φ
      ext x
      obtain ⟨⟨a1, a2, a3⟩, w⟩ := x
      change Multiplicative.ofAdd ((φ ⟨(1, 0, 0), 0⟩).toAdd * a1
        + (φ ⟨(0, 0, 0), 1⟩).toAdd * w) = φ ⟨(a1, a2, a3), w⟩
      have hval : (φ ⟨(a1, a2, a3), w⟩).toAdd =
          (φ ⟨(1, 0, 0), 0⟩).toAdd * a1 + (φ ⟨(0, 0, 0), 1⟩).toAdd * w := by
        rw [gen_decomp a1 a2 a3 w]
        simp only [map_mul, map_pow, hom_e2_eq_one φ, hom_e3_eq_one φ, one_pow,
          mul_one, toAdd_mul, toAdd_pow, nsmul_eq_mul]
        rw [ZMod.natCast_zmod_val a1, ZMod.natCast_zmod_val w]
        ring
      rw [← hval]
      exact ofAdd_toAdd _
    · intro rt
      refine Prod.ext ?_ ?_
      · change ((homOfPair rt) ⟨(1, 0, 0), 0⟩).toAdd = rt.1
        change (Multiplicative.ofAdd (rt.1 * (1 : ZMod p) + rt.2 * 0)).toAdd = rt.1
        rw [mul_one, mul_zero, add_zero, toAdd_ofAdd]
      · change ((homOfPair rt) ⟨(0, 0, 0), 1⟩).toAdd = rt.2
        change (Multiplicative.ofAdd (rt.1 * (0 : ZMod p) + rt.2 * 1)).toAdd = rt.2
        rw [mul_zero, mul_one, zero_add, toAdd_ofAdd]
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_zmod]
  ring

end Gid8

/-! ### `Model p d` (maximal class, generator rank 2) -/

namespace Model

variable {d : ZMod p}

/-- The character of `Model` attached to a pair `(r,t)`:
`⟨α,u,v⟩ ↦ r·(α mod p) + t·u` (the `v`-coordinate is killed). -/
def homOfPair (rt : ZMod p × ZMod p) : Model p d →* Multiplicative (ZMod p) where
  toFun x := Multiplicative.ofAdd (rt.1 * redp p x.α + rt.2 * x.u)
  map_one' := by
    change Multiplicative.ofAdd (rt.1 * redp p (0 : ZMod (p ^ 2)) + rt.2 * 0) = 1
    rw [map_zero, mul_zero, mul_zero, add_zero]; rfl
  map_mul' x y := by
    change Multiplicative.ofAdd (rt.1 * redp p (x * y).α + rt.2 * (x * y).u)
      = Multiplicative.ofAdd (rt.1 * redp p x.α + rt.2 * x.u)
        * Multiplicative.ofAdd (rt.1 * redp p y.α + rt.2 * y.u)
    rw [mul_def, ← ofAdd_add]
    congr 1
    change rt.1 * redp p (x.α + y.α + liftp p (tauP p d (redp p y.α) x.u x.v)
        + dc d * carryF p x.u y.u) + rt.2 * (x.u + y.u)
      = rt.1 * redp p x.α + rt.2 * x.u + (rt.1 * redp p y.α + rt.2 * y.u)
    simp only [map_add, map_mul, redp_liftp, redp_carryF, mul_zero, add_zero]
    ring

omit [Fact (Odd p)] in
/-- The carry `carryF(j, 1)` vanishes as long as `j + 1 < p` (no wrap). -/
theorem carryF_succ_zero (j : ℕ) (hj : j + 1 < p) :
    carryF p ((j : ZMod p)) 1 = 0 := by
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  have hjp : j < p := by omega
  have hval : ((j : ZMod p)).val = j := ZMod.val_natCast_of_lt hjp
  have h1 : (1 : ZMod p).val = 1 := ZMod.val_one p
  have hsum : ((j : ZMod p) + 1).val = j + 1 := by
    rw [← Nat.cast_one, ← Nat.cast_add, ZMod.val_natCast_of_lt hj]
  unfold carryF
  rw [hval, h1, hsum, Nat.sub_self]; simp

/-- `a^{α.val} = ⟨α,0,0⟩` with `a = ⟨1,0,0⟩`. -/
theorem a_pow (α : ZMod (p ^ 2)) : (⟨1, 0, 0⟩ : Model p d) ^ α.val = ⟨α, 0, 0⟩ := by
  rw [pow_formula]
  have htau : (∑ j ∈ range α.val,
      tauP p d (redp p (1 : ZMod (p ^ 2))) ((j : ZMod p) * 0)
        ((j : ZMod p) * 0 + tri p (j : ZMod p) * redp p (1 : ZMod (p ^ 2)) * 0)) = 0 :=
    Finset.sum_eq_zero (fun j _ => by
      simp only [mul_zero, add_zero]; exact tauP_zero_right _)
  have hcar : (∑ j ∈ range α.val, carryF p ((j : ZMod p) * 0) 0) = 0 :=
    Finset.sum_eq_zero (fun j _ => by rw [mul_zero]; exact carryF_zero' 0)
  refine Model.ext ?_ ?_ ?_
  · rw [htau, hcar, liftp_zero, mul_zero, add_zero, add_zero, nsmul_eq_mul,
      mul_one, ZMod.natCast_zmod_val]
  · change ((α.val : ℕ) : ZMod p) * 0 = 0
    rw [mul_zero]
  · change ((α.val : ℕ) : ZMod p) * 0
        + tri p ((α.val : ℕ) : ZMod p) * redp p (1 : ZMod (p ^ 2)) * 0 = 0
    rw [mul_zero, mul_zero, add_zero]

/-- `s^{u.val} = ⟨0,u,0⟩` with `s = ⟨0,1,0⟩` (no carry below `p`). -/
theorem s_pow (u : ZMod p) : (⟨0, 1, 0⟩ : Model p d) ^ u.val = ⟨0, u, 0⟩ := by
  rw [pow_formula]
  have htau : (∑ j ∈ range u.val,
      tauP p d (redp p (0 : ZMod (p ^ 2))) ((j : ZMod p) * 1)
        ((j : ZMod p) * 0 + tri p (j : ZMod p) * redp p (0 : ZMod (p ^ 2)) * 1)) = 0 :=
    Finset.sum_eq_zero (fun j _ => by rw [map_zero]; exact tauP_zero_left _ _)
  have hcar : (∑ j ∈ range u.val, carryF p ((j : ZMod p) * 1) 1) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [mul_one]
    have hjw : j < u.val := Finset.mem_range.mp hj
    have hwv : u.val < p := ZMod.val_lt u
    exact carryF_succ_zero j (by omega)
  refine Model.ext ?_ ?_ ?_
  · rw [htau, hcar, liftp_zero, mul_zero, add_zero, add_zero, smul_zero]
  · change ((u.val : ℕ) : ZMod p) * 1 = u
    rw [mul_one, ZMod.natCast_zmod_val]
  · change ((u.val : ℕ) : ZMod p) * 0
        + tri p ((u.val : ℕ) : ZMod p) * redp p (0 : ZMod (p ^ 2)) * 1 = 0
    rw [map_zero, mul_zero, mul_zero, zero_mul, add_zero]

/-- `b^{v.val} = ⟨0,0,v⟩` with `b = ⟨0,0,1⟩`. -/
theorem b_pow (v : ZMod p) : (⟨0, 0, 1⟩ : Model p d) ^ v.val = ⟨0, 0, v⟩ := by
  rw [pow_formula]
  have htau : (∑ j ∈ range v.val,
      tauP p d (redp p (0 : ZMod (p ^ 2))) ((j : ZMod p) * 0)
        ((j : ZMod p) * 1 + tri p (j : ZMod p) * redp p (0 : ZMod (p ^ 2)) * 0)) = 0 :=
    Finset.sum_eq_zero (fun j _ => by rw [map_zero]; exact tauP_zero_left _ _)
  have hcar : (∑ j ∈ range v.val, carryF p ((j : ZMod p) * 0) 0) = 0 :=
    Finset.sum_eq_zero (fun j _ => by rw [mul_zero]; exact carryF_zero' 0)
  refine Model.ext ?_ ?_ ?_
  · rw [htau, hcar, liftp_zero, mul_zero, add_zero, add_zero, smul_zero]
  · change ((v.val : ℕ) : ZMod p) * 0 = 0
    rw [mul_zero]
  · change ((v.val : ℕ) : ZMod p) * 1
        + tri p ((v.val : ℕ) : ZMod p) * redp p (0 : ZMod (p ^ 2)) * 0 = v
    rw [map_zero, mul_zero, add_zero, mul_one, ZMod.natCast_zmod_val]

/-- `⟨α,u,v⟩ = a^{α} s^{u} b^{v}` on generators. -/
theorem gen_decomp (α : ZMod (p ^ 2)) (u v : ZMod p) :
    (⟨α, u, v⟩ : Model p d) =
      (⟨1, 0, 0⟩ : Model p d) ^ α.val * (⟨0, 1, 0⟩ : Model p d) ^ u.val
        * (⟨0, 0, 1⟩ : Model p d) ^ v.val := by
  rw [a_pow, s_pow, b_pow]
  refine Model.ext ?_ ?_ ?_ <;>
    simp only [mul_def, map_zero, tauP_zero_left, tauP_zero_right, liftp_zero,
      carryF_zero, carryF_zero', mul_zero, zero_mul, add_zero, zero_add]

/-- Any character kills `b = ⟨0,0,1⟩`. The commutator `s·a·(a·s)⁻¹` equals
`b` times the central element `⟨liftp d, 0, 0⟩ ∈ p·C_{p²}`; both the central
element and the `p`-torsion force `φ b = 1`. -/
theorem hom_b_eq_one (φ : Model p d →* Multiplicative (ZMod p)) :
    φ ⟨0, 0, 1⟩ = 1 := by
  -- the central `α`-element `⟨liftp d, 0, 0⟩` is killed
  have hcentral : φ (⟨liftp p d, 0, 0⟩ : Model p d) = 1 := by
    have hpc : (φ (⟨1, 0, 0⟩ : Model p d)) ^ p = 1 := by
      rw [← ofAdd_toAdd (φ (⟨1, 0, 0⟩ : Model p d)), ← ofAdd_nsmul, nsmul_eq_mul,
        ZMod.natCast_self, zero_mul, ofAdd_zero]
    rw [← a_pow (liftp p d), map_pow, liftp_val, pow_mul, hpc, one_pow]
  -- the group relation `s·a = a·s·⟨liftp d, 0, 1⟩`
  have htauval : tauP p d (redp p (1 : ZMod (p ^ 2))) 1 0 = d := by
    rw [map_one]; unfold tauP tri; ring
  have e1 : (⟨0, 1, 0⟩ : Model p d) * ⟨1, 0, 0⟩
      = ⟨1, 0, 0⟩ * ⟨0, 1, 0⟩ * ⟨liftp p d, 0, 1⟩ := by
    refine Model.ext ?_ ?_ ?_
    · simp only [mul_def, map_zero, redp_liftp, tauP_zero_left, tauP_zero_right,
        liftp_zero, carryF_zero, carryF_zero', mul_zero, zero_mul, add_zero,
        zero_add, htauval]
    · simp only [mul_def, add_zero, zero_add]
    · simp only [mul_def, map_zero, map_one, redp_liftp, mul_zero,
        mul_one, add_zero, zero_add]
  -- `⟨liftp d, 0, 1⟩ = ⟨liftp d, 0, 0⟩ · b`
  have hsplit : (⟨liftp p d, 0, 1⟩ : Model p d) = ⟨liftp p d, 0, 0⟩ * ⟨0, 0, 1⟩ := by
    refine Model.ext ?_ ?_ ?_ <;>
      simp only [mul_def, map_zero, tauP_zero_right, liftp_zero,
        carryF_zero, mul_zero, add_zero, zero_add]
  have h := congrArg φ e1
  rw [map_mul, map_mul, map_mul,
    mul_comm (φ ⟨0, 1, 0⟩) (φ ⟨1, 0, 0⟩)] at h
  have hb1 : φ (⟨liftp p d, 0, 1⟩ : Model p d) = 1 := (left_eq_mul.mp h)
  rw [hsplit, map_mul, hcentral, one_mul] at hb1
  exact hb1

/-- `|Hom(Model, C_p)| = p²`. -/
theorem card_hom : Nat.card (Model p d →* Multiplicative (ZMod p)) = p ^ 2 := by
  have e : (Model p d →* Multiplicative (ZMod p)) ≃ ZMod p × ZMod p := by
    refine ⟨fun φ => ((φ ⟨1, 0, 0⟩).toAdd, (φ ⟨0, 1, 0⟩).toAdd),
      fun rt => homOfPair rt, ?_, ?_⟩
    · intro φ
      ext x
      obtain ⟨α, u, v⟩ := x
      change Multiplicative.ofAdd ((φ ⟨1, 0, 0⟩).toAdd * redp p α
        + (φ ⟨0, 1, 0⟩).toAdd * u) = φ ⟨α, u, v⟩
      have hα : redp p α = (α.val : ZMod p) := by
        simp only [redp, ZMod.castHom_apply, ZMod.natCast_val]
      have hval : (φ ⟨α, u, v⟩).toAdd =
          (φ ⟨1, 0, 0⟩).toAdd * redp p α + (φ ⟨0, 1, 0⟩).toAdd * u := by
        rw [gen_decomp α u v]
        simp only [map_mul, map_pow, hom_b_eq_one φ, one_pow, mul_one,
          toAdd_mul, toAdd_pow, nsmul_eq_mul]
        rw [hα, ZMod.natCast_zmod_val u]
        ring
      rw [← hval]
      exact ofAdd_toAdd _
    · intro rt
      refine Prod.ext ?_ ?_
      · change ((homOfPair rt) ⟨1, 0, 0⟩).toAdd = rt.1
        change (Multiplicative.ofAdd (rt.1 * redp p (1 : ZMod (p ^ 2))
          + rt.2 * 0)).toAdd = rt.1
        rw [map_one, mul_one, mul_zero, add_zero, toAdd_ofAdd]
      · change ((homOfPair rt) ⟨0, 1, 0⟩).toAdd = rt.2
        change (Multiplicative.ofAdd (rt.1 * redp p (0 : ZMod (p ^ 2))
          + rt.2 * 1)).toAdd = rt.2
        rw [map_zero, mul_zero, mul_one, zero_add, toAdd_ofAdd]
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_zmod]
  ring

end Model

/-! ## Section F: three more subgroup counts and two more separations -/

/-- **Order-`p³` subgroups of `Gid8`**: exactly `p + 1`. -/
theorem card_order_p3_subgroups_gid8 :
    Nat.card {H : Subgroup (Gid8 p) // Nat.card H = p ^ 3} = p + 1 := by
  have hG4 : Nat.card (Gid8 p) = p ^ 4 := Gid8.card_gid8 p
  have h := card_order_p3_of_card_hom (G := Gid8 p) hG4
  rw [Gid8.card_hom] at h
  have hp : p.Prime := Fact.out
  have hq : 0 < p - 1 := by have := hp.one_lt; omega
  have hg := geom_sum_mul_pred (p := p) 2 hp.one_lt.le
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, pow_zero, pow_one] at hg
  rw [← hg] at h
  rw [Nat.eq_of_mul_eq_mul_right hq h]; ring

/-- **Order-`p³` subgroups of `CH7`**: exactly `p² + p + 1`. -/
theorem card_order_p3_subgroups_ch7 :
    Nat.card {H : Subgroup (CH7 p) // Nat.card H = p ^ 3} = p ^ 2 + p + 1 := by
  have hG4 : Nat.card (CH7 p) = p ^ 4 := CH7.card_ch7 p
  have h := card_order_p3_of_card_hom (G := CH7 p) hG4
  rw [CH7.card_hom] at h
  have hp : p.Prime := Fact.out
  have hq : 0 < p - 1 := by have := hp.one_lt; omega
  have hg := geom_sum_mul_pred (p := p) 3 hp.one_lt.le
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, pow_zero, pow_one] at hg
  rw [← hg] at h
  rw [Nat.eq_of_mul_eq_mul_right hq h]; ring

/-- **Order-`p³` subgroups of `Model p d`**: exactly `p + 1`. -/
theorem card_order_p3_subgroups_model {d : ZMod p} :
    Nat.card {H : Subgroup (Model p d) // Nat.card H = p ^ 3} = p + 1 := by
  have hG4 : Nat.card (Model p d) = p ^ 4 := Model.card_model
  have h := card_order_p3_of_card_hom (G := Model p d) hG4
  rw [Model.card_hom] at h
  have hp : p.Prime := Fact.out
  have hq : 0 < p - 1 := by have := hp.one_lt; omega
  have hg := geom_sum_mul_pred (p := p) 2 hp.one_lt.le
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, pow_zero, pow_one] at hg
  rw [← hg] at h
  rw [Nat.eq_of_mul_eq_mul_right hq h]; ring

/-- **G9 vs Gid8**: separated by the order-`p³` subgroup count
(`p²+p+1` vs `p+1`). -/
theorem isEmpty_tableIso_g9_gid8 :
    IsEmpty (SpeciesTableIso (G9 p) (Gid8 p)) := by
  constructor
  intro T
  have h := T.card_subgroups_eq (p ^ 3)
  rw [card_order_p3_subgroups_g9, card_order_p3_subgroups_gid8] at h
  have hpos : 0 < p ^ 2 := pow_pos (Fact.out : p.Prime).pos 2
  omega

/-- **CH7 vs Model**: separated by the order-`p³` subgroup count
(`p²+p+1` vs `p+1`). -/
theorem isEmpty_tableIso_ch7_model (_hp5 : 5 ≤ p) {d : ZMod p} (_hd : d ≠ 0) :
    IsEmpty (SpeciesTableIso (CH7 p) (Model p d)) := by
  constructor
  intro T
  have h := T.card_subgroups_eq (p ^ 3)
  rw [card_order_p3_subgroups_ch7, card_order_p3_subgroups_model] at h
  have hpos : 0 < p ^ 2 := pow_pos (Fact.out : p.Prime).pos 2
  omega

end P4

end LeanDring

