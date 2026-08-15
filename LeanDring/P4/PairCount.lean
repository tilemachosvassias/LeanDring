/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P4.ColTwo
import Mathlib.GroupTheory.PGroup

/-!
# Commuting-pair counting: order-`p²` subgroups of exponent-`p` groups

In a finite group of exponent `p`, order-`p²` subgroups are counted by
**commuting pairs**:

  `#{H : |H| = p²} · (p²−1)·(p²−p) = ∑_{x ≠ 1} (|C_G(x)| − p)`.

Mechanism: a pair `(x, y)` with `x ≠ 1`, `y` commuting with `x`,
`y ∉ ⟨x⟩` generates a subgroup of order exactly `p²`
(`card_closure_pair`, via an injective hom from `C_p × C_p`); fibering
the pair set by the generated subgroup gives `(p²−1)(p²−p)` pairs per
subgroup (via commutativity of groups of order `p²`); counting the same
pair set by its first coordinate gives the centralizer sum.

This is the engine for column 2 of rows (xiv) and (xv).
-/

namespace LeanDring

namespace P4

open Finset

variable {p : ℕ} [Fact p.Prime] [Fact (Odd p)]

section PairCount

variable {G : Type*} [Group G] [Fintype G]

omit [Fintype G] in
omit [Fact (Odd p)] in
/-- In an exponent-`p` group, non-identity elements have order `p`. -/
theorem orderOf_eq_prime_of_exponent {x : G} (hx : x ^ p = 1) (hx1 : x ≠ 1) :
    orderOf x = p := by
  have hp : p.Prime := Fact.out
  rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hx) with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hx1
  · exact h

omit [Fintype G] in
omit [Fact (Odd p)] in
/-- If `yᵖ = 1` and some power `y^b` with `b ≢ 0 (mod p)` lies in a
subgroup, then so does `y`. -/
theorem mem_of_pow_mem {y : G} (hy : y ^ p = 1) {K : Subgroup G}
    {b : ZMod p} (hb : b ≠ 0) (hmem : y ^ b.val ∈ K) : y ∈ K := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hu : IsUnit b := by
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
  have hcancel : ((b.val * (b⁻¹).val : ℕ) : ZMod p) = 1 := by
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id, ZMod.natCast_val, ZMod.cast_id]
    exact ZMod.mul_inv_of_unit b hu
  have hmod : (b.val * (b⁻¹).val) % p = 1 % p := by
    have h1 : ((b.val * (b⁻¹).val : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      rw [Nat.cast_one]
      exact hcancel
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h1
  have hpow : (y ^ b.val) ^ (b⁻¹).val = y := by
    rw [← pow_mul, pow_eq_pow_mod _ hy, hmod, ← pow_eq_pow_mod _ hy,
      pow_one]
  rw [← hpow]
  exact K.pow_mem hmem _

omit [Fintype G] in
omit [Fact (Odd p)] in
/-- **A commuting independent pair generates `C_p × C_p`**: if `xᵖ = yᵖ = 1`,
`x ≠ 1`, `y` commutes with `x` and `y ∉ ⟨x⟩`, then `|⟨x, y⟩| = p²`. -/
theorem card_closure_pair {x y : G} (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hcomm : y * x = x * y) (hx1 : x ≠ 1)
    (hyx : y ∉ Subgroup.zpowers x) :
    Nat.card (Subgroup.closure ({x, y} : Set G)) = p ^ 2 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hox : orderOf x = p := orderOf_eq_prime_of_exponent hx hx1
  have hCxy : Commute x y := hcomm.symm
  have hkey : ∀ w w' : Multiplicative (ZMod p) × Multiplicative (ZMod p),
      x ^ ((w * w').1.toAdd).val * y ^ ((w * w').2.toAdd).val =
        x ^ (w.1.toAdd).val * y ^ (w.2.toAdd).val *
          (x ^ (w'.1.toAdd).val * y ^ (w'.2.toAdd).val) := by
    intro w w'
    have hxadd : x ^ ((w.1.toAdd + w'.1.toAdd)).val =
        x ^ (w.1.toAdd).val * x ^ (w'.1.toAdd).val := by
      rw [ZMod.val_add, ← pow_eq_pow_mod _ hx, pow_add]
    have hyadd : y ^ ((w.2.toAdd + w'.2.toAdd)).val =
        y ^ (w.2.toAdd).val * y ^ (w'.2.toAdd).val := by
      rw [ZMod.val_add, ← pow_eq_pow_mod _ hy, pow_add]
    change x ^ ((w.1.toAdd + w'.1.toAdd)).val *
        y ^ ((w.2.toAdd + w'.2.toAdd)).val = _
    rw [hxadd, hyadd]
    have hswap : y ^ (w.2.toAdd).val * x ^ (w'.1.toAdd).val =
        x ^ (w'.1.toAdd).val * y ^ (w.2.toAdd).val :=
      (hCxy.pow_pow _ _).symm
    calc x ^ (w.1.toAdd).val * x ^ (w'.1.toAdd).val *
          (y ^ (w.2.toAdd).val * y ^ (w'.2.toAdd).val)
        = x ^ (w.1.toAdd).val *
            (x ^ (w'.1.toAdd).val * y ^ (w.2.toAdd).val) *
            y ^ (w'.2.toAdd).val := by group
      _ = x ^ (w.1.toAdd).val *
            (y ^ (w.2.toAdd).val * x ^ (w'.1.toAdd).val) *
            y ^ (w'.2.toAdd).val := by rw [hswap]
      _ = _ := by group
  let ψ : Multiplicative (ZMod p) × Multiplicative (ZMod p) →* G :=
    MonoidHom.mk' (fun w => x ^ (w.1.toAdd).val * y ^ (w.2.toAdd).val)
      hkey
  have hψ : ∀ w : Multiplicative (ZMod p) × Multiplicative (ZMod p),
      ψ w = x ^ (w.1.toAdd).val * y ^ (w.2.toAdd).val := fun _ => rfl
  -- injectivity
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro w hw
    rw [MonoidHom.mem_ker, hψ] at hw
    have hb0 : (w.2.toAdd) = 0 := by
      by_contra hb
      refine hyx (mem_of_pow_mem hy hb ?_)
      have h1 : y ^ (w.2.toAdd).val = (x ^ (w.1.toAdd).val)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]
        calc y ^ (w.2.toAdd).val * x ^ (w.1.toAdd).val
            = x ^ (w.1.toAdd).val * y ^ (w.2.toAdd).val :=
              ((hCxy.pow_pow _ _).symm).eq
          _ = 1 := hw
      rw [h1]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _
        (Subgroup.mem_zpowers x) _)
    have ha0 : (w.1.toAdd) = 0 := by
      rw [hb0] at hw
      simp only [ZMod.val_zero, pow_zero, mul_one] at hw
      have hdvd : orderOf x ∣ (w.1.toAdd).val := orderOf_dvd_of_pow_eq_one hw
      rw [hox] at hdvd
      have hlt : (w.1.toAdd).val < p := ZMod.val_lt _
      have hz : (w.1.toAdd).val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
      exact (ZMod.val_eq_zero _).mp hz
    change w = 1
    have h1 : w.1 = 1 := by
      have := congrArg Multiplicative.ofAdd ha0
      simpa using this
    have h2 : w.2 = 1 := by
      have := congrArg Multiplicative.ofAdd hb0
      simpa using this
    exact Prod.ext h1 h2
  -- the range is the closure
  have hrange : ψ.range = Subgroup.closure ({x, y} : Set G) := by
    apply le_antisymm
    · rintro g ⟨w, rfl⟩
      rw [hψ]
      have hxmem : x ∈ Subgroup.closure ({x, y} : Set G) :=
        Subgroup.subset_closure (Set.mem_insert x {y})
      have hymem : y ∈ Subgroup.closure ({x, y} : Set G) :=
        Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hxmem _)
        (Subgroup.pow_mem _ hymem _)
    · rw [Subgroup.closure_le]
      intro g hg
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with h | h
      · refine ⟨(Multiplicative.ofAdd (1 : ZMod p), 1), ?_⟩
        rw [hψ, h]
        change x ^ (1 : ZMod p).val * y ^ (0 : ZMod p).val = x
        rw [ZMod.val_one, ZMod.val_zero, pow_one, pow_zero, mul_one]
      · refine ⟨(1, Multiplicative.ofAdd (1 : ZMod p)), ?_⟩
        rw [hψ, h]
        change x ^ (0 : ZMod p).val * y ^ (1 : ZMod p).val = y
        rw [ZMod.val_one, ZMod.val_zero, pow_one, pow_zero, one_mul]
  rw [← hrange]
  have hcard := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [← hcard, Nat.card_prod]
  have h1 : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  rw [h1]
  ring

omit [Fact (Odd p)] in
/-- **The pair-counting identity** for exponent-`p` groups:
`#{H : |H| = p²}·(p²−1)(p²−p) = ∑_{x≠1} (|C(x)| − p)`. -/
theorem card_p2_subgroups_mul_eq_pairs [DecidableEq G]
    (hexp : ∀ g : G, g ^ p = 1) :
    Nat.card {H : Subgroup G // Nat.card H = p ^ 2} *
        ((p ^ 2 - 1) * (p ^ 2 - p)) =
      ∑ x ∈ univ.filter (fun x : G => x ≠ 1),
        ((univ.filter (fun y : G => y * x = x * y)).card - p) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : Fintype (Subgroup G) := Fintype.ofFinite _
  have hPmem : ∀ w : G × G, w ∈ univ.filter (fun w : G × G =>
      w.1 ≠ 1 ∧ w.2 * w.1 = w.1 * w.2 ∧ w.2 ∉ Subgroup.zpowers w.1) ↔
      (w.1 ≠ 1 ∧ w.2 * w.1 = w.1 * w.2 ∧ w.2 ∉ Subgroup.zpowers w.1) := by
    intro w
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  -- LHS: fiber the pair set by the generated subgroup
  have hmapsto : ∀ w ∈ univ.filter (fun w : G × G =>
      w.1 ≠ 1 ∧ w.2 * w.1 = w.1 * w.2 ∧ w.2 ∉ Subgroup.zpowers w.1),
      Subgroup.closure ({w.1, w.2} : Set G) ∈
        univ.filter (fun H : Subgroup G => Nat.card H = p ^ 2) := by
    intro w hw
    obtain ⟨h1, h2, h3⟩ := (hPmem w).mp hw
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _,
      card_closure_pair (hexp w.1) (hexp w.2) h2 h1 h3⟩
  have hfiber : ∀ H ∈ univ.filter (fun H : Subgroup G =>
      Nat.card H = p ^ 2),
      ((univ.filter (fun w : G × G =>
        w.1 ≠ 1 ∧ w.2 * w.1 = w.1 * w.2 ∧ w.2 ∉ Subgroup.zpowers w.1)).filter
          fun w => Subgroup.closure ({w.1, w.2} : Set G) = H).card =
        (p ^ 2 - 1) * (p ^ 2 - p) := by
    intro H hH
    have hHcard : Nat.card H = p ^ 2 := (Finset.mem_filter.mp hH).2
    have hHcomm : ∀ a b : G, a ∈ H → b ∈ H → b * a = a * b := by
      intro a b ha hb
      letI : CommGroup H := IsPGroup.commGroupOfCardEqPrimeSq hHcard
      exact congrArg Subtype.val (mul_comm (⟨b, hb⟩ : H) ⟨a, ha⟩)
    -- fiber = independent pairs inside `H`, counted `(p²−1)·(p²−p)`
    haveI : Fintype H := Fintype.ofFinite _
    have hHfin : Fintype.card (H : Set G) = p ^ 2 := by
      rw [← Nat.card_eq_fintype_card]
      have h0 : Nat.card (H : Set G) = Nat.card H := rfl
      rw [h0, hHcard]
    -- rewrite the fiber as pairs `(a, b) ∈ H × H` with `a ≠ 1`, `b ∉ ⟨a⟩`
    have hset : ((univ.filter (fun w : G × G =>
        w.1 ≠ 1 ∧ w.2 * w.1 = w.1 * w.2 ∧ w.2 ∉ Subgroup.zpowers w.1)).filter
          fun w => Subgroup.closure ({w.1, w.2} : Set G) = H) =
        univ.filter (fun w : G × G => (w.1 ∈ H ∧ w.2 ∈ H) ∧ w.1 ≠ 1 ∧
          w.2 ∉ Subgroup.zpowers w.1) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨h1, h2, h3⟩, hcl⟩
        refine ⟨⟨?_, ?_⟩, h1, h3⟩
        · rw [← hcl]
          exact Subgroup.subset_closure (Set.mem_insert _ _)
        · rw [← hcl]
          exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
      · rintro ⟨⟨hw1, hw2⟩, h1, h3⟩
        have h2 : w.2 * w.1 = w.1 * w.2 := hHcomm w.1 w.2 hw1 hw2
        refine ⟨⟨h1, h2, h3⟩, ?_⟩
        have hle : Subgroup.closure ({w.1, w.2} : Set G) ≤ H := by
          rw [Subgroup.closure_le]
          intro g hg
          rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
          rcases hg with rfl | rfl
          · exact hw1
          · exact hw2
        exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq
          (by rw [hHcard,
            card_closure_pair (hexp w.1) (hexp w.2) h2 h1 h3]))
    rw [hset]
    -- fiber the pair set inside `H` by the first coordinate
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun w : G × G => w.1) (t := (H : Set G).toFinset)
      (by
        intro w hw
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe,
          Set.mem_toFinset, Finset.mem_univ,
          true_and] at hw ⊢
        exact hw.1.1)]
    have hinner : ∀ a ∈ (H : Set G).toFinset,
        ((univ.filter (fun w : G × G => (w.1 ∈ H ∧ w.2 ∈ H) ∧ w.1 ≠ 1 ∧
          w.2 ∉ Subgroup.zpowers w.1)).filter
            (fun w => w.1 = a)).card =
        if a = 1 then 0 else p ^ 2 - p := by
      intro a ha
      rw [Set.mem_toFinset] at ha
      by_cases ha1 : a = 1
      · rw [if_pos ha1, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro w hw
        rw [Finset.mem_filter] at hw
        intro hfst
        exact hw.2.2.1 (hfst.trans ha1)
      · rw [if_neg ha1]
        have hbij : ((univ.filter (fun w : G × G =>
            (w.1 ∈ H ∧ w.2 ∈ H) ∧ w.1 ≠ 1 ∧
              w.2 ∉ Subgroup.zpowers w.1)).filter
                (fun w => w.1 = a)).card =
            ((H : Set G).toFinset \ (Subgroup.zpowers a : Set G).toFinset).card := by
          refine Finset.card_bij (fun w _ => w.2) ?_ ?_ ?_
          · intro w hw
            rw [Finset.mem_filter, Finset.mem_filter] at hw
            obtain ⟨⟨-, ⟨-, hw2⟩, -, hz⟩, hfst⟩ := hw
            rw [Finset.mem_sdiff, Set.mem_toFinset, Set.mem_toFinset]
            refine ⟨hw2, ?_⟩
            rwa [← hfst]
          · intro w₁ h₁ w₂ h₂ he
            rw [Finset.mem_filter, Finset.mem_filter] at h₁ h₂
            exact Prod.ext (h₁.2.trans h₂.2.symm) he
          · intro b hb
            rw [Finset.mem_sdiff, Set.mem_toFinset, Set.mem_toFinset] at hb
            refine ⟨(a, b), ?_, rfl⟩
            rw [Finset.mem_filter, Finset.mem_filter]
            exact ⟨⟨Finset.mem_univ _, ⟨ha, hb.1⟩, ha1, hb.2⟩, rfl⟩
        rw [hbij, Finset.card_sdiff, Finset.inter_eq_left.mpr ?_,
          Set.toFinset_card, Set.toFinset_card]
        · have hz : Fintype.card (Subgroup.zpowers a : Set G) = p := by
            rw [← Nat.card_eq_fintype_card]
            have h0 : Nat.card (Subgroup.zpowers a : Set G) =
                Nat.card (Subgroup.zpowers a) := rfl
            rw [h0, Nat.card_zpowers,
              orderOf_eq_prime_of_exponent (hexp a) ha1]
          rw [hz, hHfin]
        · intro g hg
          rw [Set.mem_toFinset] at hg ⊢
          exact (Subgroup.zpowers_le.mpr ha) hg
    rw [Finset.sum_congr rfl hinner]
    have hflip : ∀ a ∈ (H : Set G).toFinset,
        (if a = 1 then 0 else p ^ 2 - p) =
          (if a ≠ 1 then p ^ 2 - p else 0) := by
      intro a _
      by_cases h : a = 1
      · rw [if_pos h, if_neg (by simpa using h)]
      · rw [if_neg h, if_pos h]
    rw [Finset.sum_congr rfl hflip, ← Finset.sum_filter,
      Finset.sum_const, smul_eq_mul, Finset.filter_ne']
    have h1H : (1 : G) ∈ (H : Set G).toFinset := by
      rw [Set.mem_toFinset]
      exact H.one_mem
    rw [Finset.card_erase_of_mem h1H, Set.toFinset_card, hHfin]
  -- assemble: count the pair set two ways
  have hleft : (univ.filter (fun w : G × G =>
      w.1 ≠ 1 ∧ w.2 * w.1 = w.1 * w.2 ∧
        w.2 ∉ Subgroup.zpowers w.1)).card =
      Nat.card {H : Subgroup G // Nat.card H = p ^ 2} *
        ((p ^ 2 - 1) * (p ^ 2 - p)) := by
    rw [Finset.card_eq_sum_card_fiberwise hmapsto,
      Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul]
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hright : (univ.filter (fun w : G × G =>
      w.1 ≠ 1 ∧ w.2 * w.1 = w.1 * w.2 ∧
        w.2 ∉ Subgroup.zpowers w.1)).card =
      ∑ x ∈ univ.filter (fun x : G => x ≠ 1),
        ((univ.filter (fun y : G => y * x = x * y)).card - p) := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun w : G × G => w.1) (t := univ.filter (fun x : G => x ≠ 1))
      (by
        intro w hw
        simp only [Finset.coe_filter, Set.mem_setOf_eq,
          Finset.mem_univ,
          true_and] at hw ⊢
        exact hw.1)]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx1 : x ≠ 1 := (Finset.mem_filter.mp hx).2
    have hbijx : ((univ.filter (fun w : G × G =>
        w.1 ≠ 1 ∧ w.2 * w.1 = w.1 * w.2 ∧
          w.2 ∉ Subgroup.zpowers w.1)).filter
            fun w => w.1 = x).card =
        ((univ.filter (fun y : G => y * x = x * y)) \
          (Subgroup.zpowers x : Set G).toFinset).card := by
      refine Finset.card_bij (fun w _ => w.2) ?_ ?_ ?_
      · intro w hw
        rw [Finset.mem_filter] at hw
        obtain ⟨hwP, hfst⟩ := hw
        obtain ⟨-, hcm, hz⟩ := (hPmem w).mp hwP
        rw [Finset.mem_sdiff, Finset.mem_filter, Set.mem_toFinset]
        subst hfst
        exact ⟨⟨Finset.mem_univ _, hcm⟩, hz⟩
      · intro w₁ h₁ w₂ h₂ he
        rw [Finset.mem_filter] at h₁ h₂
        exact Prod.ext (h₁.2.trans h₂.2.symm) he
      · intro y hy
        rw [Finset.mem_sdiff, Finset.mem_filter, Set.mem_toFinset] at hy
        refine ⟨(x, y), ?_, rfl⟩
        rw [Finset.mem_filter]
        exact ⟨(hPmem (x, y)).mpr ⟨hx1, hy.1.2, hy.2⟩, rfl⟩
    rw [hbijx, Finset.card_sdiff, Finset.inter_eq_left.mpr ?_,
      Set.toFinset_card]
    · have hz : Fintype.card (Subgroup.zpowers x : Set G) = p := by
        rw [← Nat.card_eq_fintype_card]
        have h0 : Nat.card (Subgroup.zpowers x : Set G) =
            Nat.card (Subgroup.zpowers x) := rfl
        rw [h0, Nat.card_zpowers,
          orderOf_eq_prime_of_exponent (hexp x) hx1]
      rw [hz]
    · intro g hg
      rw [Set.mem_toFinset] at hg
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hg
      rw [← hn]
      group
  rw [← hleft, hright]

end PairCount

end P4

end LeanDring
