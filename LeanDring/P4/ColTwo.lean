/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P4.ModularModels

/-!
# Column 2 of the `p⁴` table: order-`p²` subgroups of (vi) and (viii)

Generic counting lemmas:

* `card_orderOf_eq_prime_sq` — `#{g : ord g = p²} = #{H cyclic, |H| = p²}·φ(p²)`
  (each cyclic `C_{p²}` has `φ(p²) = p² − p` generators);
* `subgroup_p2_exists_or_torsion` — a subgroup of order `p²` either has an
  element of order `p²` (hence is cyclic) or is all `p`-torsion — **no**
  commutativity input needed;
* `card_p2_subgroups` — if the `p`-torsion set of `G` is (the carrier of)
  a subgroup `W` with `|W| = p²`, then `W` is the **unique** non-cyclic
  order-`p²` subgroup, so `#{|H| = p²} = #cyclic + 1`;
* `card_orderOf_sq_of_omega` — `#{ord = p²} = |Ω₂| − |Ω₁|`.

Model results (first `Ω₂` counts, then the rows):

* **(vi)** `M6`: `Ω₂ = p³`, `Ω₁` is a subgroup of order `p²` ⇒
  column 2 = `p + 1`;
* **(viii)** `M8`: `Ω₂ = G`, `Ω₁` a subgroup of order `p²` ⇒
  column 2 = `p² + p + 1`.

Both match the corrected [GJG10] table.
-/

namespace LeanDring

namespace P4

open Finset Model

variable {p : ℕ} [Fact p.Prime] [Fact (Odd p)]

/-! ## Generic counting lemmas -/

section Generic

variable {G : Type*} [Group G] [Fintype G]

omit [Fintype G] in
omit [Fact (Odd p)] in
/-- Elements of order `p²` inside a subgroup of order `p²` generate it. -/
theorem zpowers_eq_of_orderOf_sq {H : Subgroup G} (hH : Nat.card H = p ^ 2)
    {g : G} (hg : g ∈ H) (ho : orderOf g = p ^ 2) :
    Subgroup.zpowers g = H := by
  have hle : Subgroup.zpowers g ≤ H := Subgroup.zpowers_le.mpr hg
  have hcard : Nat.card (Subgroup.zpowers g) = Nat.card H := by
    rw [Nat.card_zpowers, ho, hH]
  have hp : p.Prime := Fact.out
  haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; exact (pow_pos hp.pos 2).ne')
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)

omit [Fact (Odd p)] in
/-- **Cyclic double counting**: `#{g : ord g = p²} = #{H : |H| = p², H cyclic}·(p² − p)`. -/
theorem card_orderOf_eq_prime_sq :
    (univ.filter fun g : G => orderOf g = p ^ 2).card =
      Nat.card {H : Subgroup G // Nat.card H = p ^ 2 ∧ IsCyclic H} *
        (p ^ 2 - p) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : Fintype (Subgroup G) := Fintype.ofFinite _
  set T : Finset (Subgroup G) :=
    univ.filter (fun H => Nat.card H = p ^ 2 ∧ IsCyclic H) with hT
  have hmapsto : ∀ g ∈ univ.filter (fun g : G => orderOf g = p ^ 2),
      Subgroup.zpowers g ∈ T := by
    intro g hg
    rw [hT, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [Nat.card_zpowers, (Finset.mem_filter.mp hg).2]
    · refine ⟨⟨⟨g, Subgroup.mem_zpowers g⟩, fun x => ?_⟩⟩
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp x.2
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext (by simpa using hn)⟩
  rw [Finset.card_eq_sum_card_fiberwise hmapsto]
  have hfiber : ∀ H ∈ T,
      ((univ.filter fun g : G => orderOf g = p ^ 2).filter
        fun g => Subgroup.zpowers g = H).card = p ^ 2 - p := by
    intro H hH
    obtain ⟨-, hHcard, hHcyc⟩ := Finset.mem_filter.mp hH
    -- the fiber is the set of order-`p²` elements of `H`
    have hset : ((univ.filter fun g : G => orderOf g = p ^ 2).filter
        fun g => Subgroup.zpowers g = H) =
        (univ.filter fun g : G => orderOf g = p ^ 2 ∧ g ∈ H) := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨ho, hz⟩
        exact ⟨ho, hz ▸ Subgroup.mem_zpowers g⟩
      · rintro ⟨ho, hmem⟩
        exact ⟨ho, zpowers_eq_of_orderOf_sq hHcard hmem ho⟩
    rw [hset]
    -- transfer the count into `↥H`, a cyclic group of order `p²`
    haveI := hHcyc
    haveI : Fintype H := Fintype.ofFinite _
    have hbij : (univ.filter fun g : G => orderOf g = p ^ 2 ∧ g ∈ H).card =
        (univ.filter fun h : H => orderOf h = p ^ 2).card := by
      refine Finset.card_bij (fun g hg => ⟨g, ((Finset.mem_filter.mp hg).2).2⟩)
        (fun g hg => ?_) (fun g₁ h₁ g₂ h₂ he => ?_) (fun h hh => ?_)
      · obtain ⟨-, ho, hmem⟩ := Finset.mem_filter.mp hg
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [Subgroup.orderOf_mk]
        exact ho
      · exact congrArg Subtype.val he
      · obtain ⟨-, ho⟩ := Finset.mem_filter.mp hh
        refine ⟨(h : G), ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [Subgroup.orderOf_coe]
        exact ⟨ho, h.2⟩
    rw [hbij]
    have hdvd : p ^ 2 ∣ Fintype.card H := by
      rw [← Nat.card_eq_fintype_card, hHcard]
    rw [IsCyclic.card_orderOf_eq_totient hdvd,
      Nat.totient_prime_pow hp (by norm_num : 0 < 2)]
    have : p ^ (2 - 1) * (p - 1) = p * (p - 1) := by norm_num
    rw [this, Nat.mul_sub, mul_one, ← pow_two]
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

omit [Fintype G] in
omit [Fact (Odd p)] in
/-- A subgroup of order `p²` has an element of order `p²` or is all
`p`-torsion (no commutativity needed: element orders divide `p²`). -/
theorem subgroup_p2_exists_or_torsion {H : Subgroup G}
    (hH : Nat.card H = p ^ 2) :
    (∃ g ∈ H, orderOf g = p ^ 2) ∨ (∀ g ∈ H, g ^ p = 1) := by
  have hp : p.Prime := Fact.out
  by_cases hex : ∃ g ∈ H, orderOf g = p ^ 2
  · exact Or.inl hex
  · refine Or.inr fun g hg => ?_
    haveI : Finite H := Nat.finite_of_card_ne_zero
      (by rw [hH]; exact (pow_pos hp.pos 2).ne')
    have hdvd : orderOf g ∣ p ^ 2 := by
      have h1 : orderOf (⟨g, hg⟩ : H) ∣ p ^ 2 := hH ▸ orderOf_dvd_natCard _
      rwa [Subgroup.orderOf_mk] at h1
    rcases (Nat.dvd_prime_pow hp).mp hdvd with ⟨k, hk, hord⟩
    interval_cases k
    · have hg1 : g = 1 := orderOf_eq_one_iff.mp (by simpa using hord)
      rw [hg1]
      exact one_pow p
    · have hop : orderOf g = p := by simpa using hord
      rw [← hop]
      exact pow_orderOf_eq_one g
    · exact absurd ⟨g, hg, by simpa using hord⟩ hex

omit [Fintype G] in
omit [Fact (Odd p)] in
/-- If the `p`-torsion of `G` is a subgroup `W` of order `p²`, then `W` is
the unique non-cyclic subgroup of order `p²`, and
`#{|H| = p²} = #{|H| = p² cyclic} + 1`. -/
theorem card_p2_subgroups [Finite G] (W : Subgroup G) (hWcard : Nat.card W = p ^ 2)
    (hWmem : ∀ x : G, x ^ p = 1 ↔ x ∈ W) :
    Nat.card {H : Subgroup G // Nat.card H = p ^ 2} =
      Nat.card {H : Subgroup G // Nat.card H = p ^ 2 ∧ IsCyclic H} + 1 := by
  classical
  have hp : p.Prime := Fact.out
  haveI : Fintype (Subgroup G) := Fintype.ofFinite _
  -- a non-cyclic order-`p²` subgroup is all `p`-torsion, hence `≤ W`, hence `= W`
  have huniq : ∀ H : Subgroup G, Nat.card H = p ^ 2 → ¬ IsCyclic H → H = W := by
    intro H hH hnc
    rcases subgroup_p2_exists_or_torsion hH with ⟨g, hg, ho⟩ | htor
    · refine absurd (⟨⟨⟨g, hg⟩, fun x => ?_⟩⟩ : IsCyclic H) hnc
      have hz := zpowers_eq_of_orderOf_sq hH hg ho
      have hx : (x : G) ∈ Subgroup.zpowers g := by
        rw [hz]
        exact x.2
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext (by simpa using hn)⟩
    · have hle : H ≤ W := fun x hx => (hWmem x).mp (htor x hx)
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [hH, hWcard])
  -- `W` itself is not cyclic
  have hWnc : ¬ IsCyclic W := by
    intro hcyc
    obtain ⟨⟨g, hgW⟩, hgen⟩ := hcyc
    have hord : orderOf (⟨g, hgW⟩ : W) = p ^ 2 := by
      have h1 : Subgroup.zpowers (⟨g, hgW⟩ : W) = ⊤ := by
        ext x
        simp only [Subgroup.mem_top, iff_true]
        exact hgen x
      have h2 := Nat.card_zpowers (⟨g, hgW⟩ : W)
      rw [h1] at h2
      have h3 : Nat.card (⊤ : Subgroup W) = Nat.card W :=
        Nat.card_congr Subgroup.topEquiv.toEquiv
      rw [h3, hWcard] at h2
      exact h2.symm
    have htor : g ^ p = 1 := (hWmem g).mpr hgW
    have htorW : (⟨g, hgW⟩ : W) ^ p = 1 := by
      refine Subtype.ext ?_
      simpa using htor
    have hdvd : orderOf (⟨g, hgW⟩ : W) ∣ p := orderOf_dvd_of_pow_eq_one htorW
    rw [hord] at hdvd
    have hple : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos hdvd
    have := hp.one_lt
    nlinarith
  -- count: the classifying predicate splits as `cyclic ⊕ {W}`
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype, Fintype.card_subtype]
  have hsplit : (univ.filter fun H : Subgroup G => Nat.card H = p ^ 2) =
      (univ.filter fun H : Subgroup G => Nat.card H = p ^ 2 ∧ IsCyclic H)
        ∪ {W} := by
    ext H
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_singleton]
    constructor
    · intro hH
      by_cases hc : IsCyclic H
      · exact Or.inl ⟨hH, hc⟩
      · exact Or.inr (huniq H hH hc)
    · rintro (⟨hH, -⟩ | rfl)
      · exact hH
      · exact hWcard
  have hdisj : Disjoint
      (univ.filter fun H : Subgroup G => Nat.card H = p ^ 2 ∧ IsCyclic H)
      ({W} : Finset (Subgroup G)) := by
    rw [Finset.disjoint_singleton_right, Finset.mem_filter]
    rintro ⟨-, -, hcyc⟩
    exact hWnc hcyc
  rw [hsplit, Finset.card_union_of_disjoint hdisj, Finset.card_singleton]

omit [Fact (Odd p)] in
/-- `#{ord = p²} = |Ω₂| − |Ω₁|`. -/
theorem card_orderOf_sq_sub [DecidableEq G] :
    (univ.filter fun g : G => orderOf g = p ^ 2).card =
      (univ.filter fun g : G => g ^ p ^ 2 = 1).card -
        (univ.filter fun g : G => g ^ p = 1).card := by
  classical
  have hp : p.Prime := Fact.out
  have hsub : (univ.filter fun g : G => g ^ p = 1) ⊆
      (univ.filter fun g : G => g ^ p ^ 2 = 1) := by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    calc g ^ p ^ 2 = (g ^ p) ^ p := by rw [← pow_mul, pow_two]
      _ = 1 := by rw [hg, one_pow]
  have hset : (univ.filter fun g : G => orderOf g = p ^ 2) =
      (univ.filter fun g : G => g ^ p ^ 2 = 1) \
        (univ.filter fun g : G => g ^ p = 1) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff]
    constructor
    · intro ho
      refine ⟨by rw [← ho]; exact pow_orderOf_eq_one g, fun h1 => ?_⟩
      have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one h1
      rw [ho] at hdvd
      have := Nat.le_of_dvd hp.pos hdvd
      have h2 := hp.one_lt
      nlinarith
    · rintro ⟨h2, h1⟩
      have hdvd : orderOf g ∣ p ^ 2 := orderOf_dvd_of_pow_eq_one h2
      rcases (Nat.dvd_prime_pow hp).mp hdvd with ⟨k, hk, hord⟩
      interval_cases k
      · exfalso
        apply h1
        have hg1 : g = 1 := orderOf_eq_one_iff.mp (by simpa using hord)
        rw [hg1]
        exact one_pow p
      · exfalso
        apply h1
        have hop : orderOf g = p := by simpa using hord
        rw [← hop]
        exact pow_orderOf_eq_one g
      · simpa using hord
  rw [hset, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]

end Generic

/-! ## The mid-level lift `ZMod p² → ZMod p³` -/

variable (p) in
/-- The lift `ZMod p² → ZMod p³`, `x ↦ p·x`. -/
def lift23 (x : ZMod (p ^ 2)) : ZMod (p ^ 3) :=
  (p : ZMod (p ^ 3)) * (x.val : ZMod (p ^ 3))

omit [Fact (Odd p)] in
theorem lift23_val (t : ZMod (p ^ 2)) : (lift23 p t).val = p * t.val := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  haveI : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp.ne_zero⟩
  have h1 : lift23 p t = ((p * t.val : ℕ) : ZMod (p ^ 3)) := by
    unfold lift23
    push_cast
    ring
  rw [h1, ZMod.val_natCast, Nat.mod_eq_of_lt]
  have hlt := ZMod.val_lt t
  calc p * t.val < p * p ^ 2 :=
        mul_lt_mul_of_pos_left hlt (Nat.pos_of_ne_zero hp.ne_zero)
    _ = p ^ 3 := by ring

omit [Fact (Nat.Prime p)] [Fact (Odd p)] in
theorem sq_mul_lift23 (t : ZMod (p ^ 2)) :
    (p : ZMod (p ^ 3)) ^ 2 * lift23 p t = 0 := by
  unfold lift23
  calc (p : ZMod (p ^ 3)) ^ 2 * ((p : ZMod (p ^ 3)) * (t.val : ZMod (p ^ 3)))
      = (p : ZMod (p ^ 3)) ^ 2 * (p : ZMod (p ^ 3)) *
        (t.val : ZMod (p ^ 3)) := by ring
    _ = 0 := by rw [p3_cast_zero, zero_mul]

omit [Fact (Odd p)] in
/-- Solutions of `p²·α = 0` in `ZMod p³` are exactly the `lift23`s. -/
theorem lift23_of_sq_mul_zero {α : ZMod (p ^ 3)}
    (h : (p : ZMod (p ^ 3)) ^ 2 * α = 0) :
    lift23 p (((α.val / p : ℕ) : ZMod (p ^ 2))) = α := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  haveI : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp.ne_zero⟩
  have hppos : 0 < p := Nat.pos_of_ne_zero hp.ne_zero
  have hα : ((α.val : ℕ) : ZMod (p ^ 3)) = α := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  have hcast : ((p ^ 2 * α.val : ℕ) : ZMod (p ^ 3)) = 0 := by
    push_cast
    rw [hα]
    exact h
  have hdvd3 : p ^ 3 ∣ p ^ 2 * α.val :=
    (CharP.cast_eq_zero_iff (ZMod (p ^ 3)) (p ^ 3) _).mp hcast
  have hdvd1 : p ∣ α.val := by
    rcases hdvd3 with ⟨c, hc⟩
    have hc2 : p ^ 2 * α.val = p ^ 2 * (p * c) := by
      rw [hc]
      ring
    exact ⟨c, Nat.eq_of_mul_eq_mul_left (pow_pos hppos 2) hc2⟩
  have hdiv : α.val = p * (α.val / p) := (Nat.mul_div_cancel' hdvd1).symm
  have hlt : α.val / p < p ^ 2 := by
    have hv : α.val < p ^ 3 := ZMod.val_lt α
    refine Nat.div_lt_of_lt_mul ?_
    calc α.val < p ^ 3 := hv
      _ = p * p ^ 2 := by ring
  have hvalcast : ((((α.val / p : ℕ) : ZMod (p ^ 2))).val) = α.val / p := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  unfold lift23
  rw [hvalcast]
  calc (p : ZMod (p ^ 3)) * ((α.val / p : ℕ) : ZMod (p ^ 3))
      = ((p * (α.val / p) : ℕ) : ZMod (p ^ 3)) := by
        push_cast
        ring
    _ = ((α.val : ℕ) : ZMod (p ^ 3)) := by rw [← hdiv]
    _ = α := hα

/-! ## Column 2 for group (vi): `M6` -/

namespace M6

/-- The `x^{p²}` law in `M6`: `x^{p²} = a^{p²α}`. -/
theorem pow_p_sq_eq_one_iff (x : M6 p) :
    x ^ p ^ 2 = 1 ↔ (p : ZMod (p ^ 3)) ^ 2 * x.α = 0 := by
  have hp : p.Prime := Fact.out
  have hp0 : ((p ^ 2 : ℕ) : ZMod p) = 0 := by
    rw [CharP.cast_eq_zero_iff (ZMod p) p]
    exact dvd_pow_self p two_ne_zero
  have htri : tri p (0 : ZMod p) = 0 := by
    unfold tri
    ring
  have hpow : x ^ p ^ 2 = ⟨(p : ZMod (p ^ 3)) ^ 2 * x.α, 0⟩ := by
    rw [pow_formula]
    ext
    · change ((p ^ 2 : ℕ) : ZMod (p ^ 3)) * x.α +
          liftpp p (tri p ((p ^ 2 : ℕ) : ZMod p) * (x.u * red3 p x.α)) =
        (p : ZMod (p ^ 3)) ^ 2 * x.α
      rw [hp0, htri, zero_mul, liftpp_zero, add_zero]
      push_cast
      ring
    · change ((p ^ 2 : ℕ) : ZMod p) * x.u = 0
      rw [hp0, zero_mul]
  rw [hpow, one_def]
  constructor
  · intro h
    exact congrArg M6.α h
  · intro h
    rw [h]

variable (p) in
/-- `|Ω₂(M6)| = p³`. -/
theorem card_omega2 : Nat.card {x : M6 p // x ^ p ^ 2 = 1} = p ^ 3 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  let f : ZMod (p ^ 2) × ZMod p → {x : M6 p // x ^ p ^ 2 = 1} := fun w =>
    ⟨⟨lift23 p w.1, w.2⟩, by
      rw [pow_p_sq_eq_one_iff]
      exact sq_mul_lift23 w.1⟩
  let g : {x : M6 p // x ^ p ^ 2 = 1} → ZMod (p ^ 2) × ZMod p := fun x =>
    (((x.1.α.val / p : ℕ) : ZMod (p ^ 2)), x.1.u)
  have hbij : Function.Bijective f := by
    rw [Function.bijective_iff_has_inverse]
    refine ⟨g, fun w => ?_, fun x => ?_⟩
    · change ((((lift23 p w.1).val / p : ℕ) : ZMod (p ^ 2)), w.2) = w
      rw [lift23_val, Nat.mul_div_cancel_left _
        (Nat.pos_of_ne_zero hp.ne_zero), ZMod.natCast_val, ZMod.cast_id]
    · obtain ⟨x, hx⟩ := x
      have hred : (p : ZMod (p ^ 3)) ^ 2 * x.α = 0 :=
        (pow_p_sq_eq_one_iff x).mp hx
      refine Subtype.ext ?_
      change (⟨lift23 p (((x.α.val / p : ℕ) : ZMod (p ^ 2))), x.u⟩ : M6 p) = x
      ext
      · exact lift23_of_sq_mul_zero hred
      · rfl
  rw [← Nat.card_eq_of_bijective f hbij, Nat.card_prod, Nat.card_zmod,
    Nat.card_zmod]
  ring

variable (p) in
/-- The `p`-torsion subgroup `W = Ω₁(M6) ≅ C_p × C_p`. -/
noncomputable def torsionW : Subgroup (M6 p) where
  carrier := {x | x ^ p = 1}
  mul_mem' := by
    intro x y hx hy
    rw [Set.mem_setOf_eq, pow_p_eq_one_iff] at hx hy ⊢
    change (p : ZMod (p ^ 3)) * (x.α + y.α + liftpp p (x.u * red3 p y.α)) = 0
    rw [mul_add, mul_add, hx, hy, p_mul_liftpp]
    ring
  one_mem' := by
    rw [Set.mem_setOf_eq]
    exact one_pow p
  inv_mem' := by
    intro x hx
    rw [Set.mem_setOf_eq, pow_p_eq_one_iff] at hx ⊢
    change (p : ZMod (p ^ 3)) * (-x.α + liftpp p (x.u * red3 p x.α)) = 0
    rw [mul_add, mul_neg, hx, p_mul_liftpp]
    ring

theorem mem_torsionW {x : M6 p} : x ∈ torsionW p ↔ x ^ p = 1 := Iff.rfl

variable (p) in
theorem card_torsionW : Nat.card (torsionW p) = p ^ 2 := by
  have h := card_omega p
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => mem_torsionW)

variable (p) in
/-- **Table row (vi), second column**: `M6` has exactly `p + 1`
subgroups of order `p²`. -/
theorem card_order_p2_subgroups_m6 :
    Nat.card {H : Subgroup (M6 p) // Nat.card H = p ^ 2} = p + 1 := by
  classical
  have hp : p.Prime := Fact.out
  -- element counts
  have hΩ1 : (univ.filter fun x : M6 p => x ^ p = 1).card = p ^ 2 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact card_omega p
  have hΩ2 : (univ.filter fun x : M6 p => x ^ p ^ 2 = 1).card = p ^ 3 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact card_omega2 p
  have hcount : (univ.filter fun x : M6 p => orderOf x = p ^ 2).card =
      p ^ 3 - p ^ 2 := by
    rw [card_orderOf_sq_sub, hΩ1, hΩ2]
  -- cyclic count: `N·(p² − p) = p³ − p² = p·(p² − p)`
  have hcyc := card_orderOf_eq_prime_sq (G := M6 p) (p := p)
  rw [hcount] at hcyc
  have harith : p ^ 3 - p ^ 2 = p * (p ^ 2 - p) := by
    rw [Nat.mul_sub]
    ring_nf
  rw [harith] at hcyc
  have hpos : 0 < p ^ 2 - p := by
    have h1 := hp.one_lt
    have h2 : p < p ^ 2 := by nlinarith
    omega
  have hN : Nat.card {H : Subgroup (M6 p) //
      Nat.card H = p ^ 2 ∧ IsCyclic H} = p :=
    (Nat.eq_of_mul_eq_mul_right hpos hcyc).symm
  -- assemble
  rw [card_p2_subgroups (torsionW p) (card_torsionW p)
    (fun x => mem_torsionW.symm), hN]

end M6

/-! ## Column 2 for group (viii): `M8` -/

namespace M8

/-- `M8` has exponent `p²`. -/
theorem pow_p_sq (x : M8 p) : x ^ p ^ 2 = 1 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hp0 : ((p ^ 2 : ℕ) : ZMod p) = 0 := by
    rw [CharP.cast_eq_zero_iff (ZMod p) p]
    exact dvd_pow_self p two_ne_zero
  have hp20 : ((p ^ 2 : ℕ) : ZMod (p ^ 2)) = 0 := ZMod.natCast_self _
  have htri : tri p (0 : ZMod p) = 0 := by
    unfold tri
    ring
  rw [pow_formula, one_def]
  ext
  · change ((p ^ 2 : ℕ) : ZMod (p ^ 2)) * x.α +
        liftp p (tri p ((p ^ 2 : ℕ) : ZMod p) *
          (redp p x.γ * redp p x.α)) = 0
    rw [hp0, hp20, htri]
    simp
  · change ((p ^ 2 : ℕ) : ZMod (p ^ 2)) * x.γ = 0
    rw [hp20, zero_mul]

variable (p) in
/-- The `p`-torsion subgroup `W = Ω₁(M8) ≅ C_p × C_p`. -/
noncomputable def torsionW : Subgroup (M8 p) where
  carrier := {x | x ^ p = 1}
  mul_mem' := by
    intro x y hx hy
    rw [Set.mem_setOf_eq, pow_p_eq_one_iff] at hx hy ⊢
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    constructor
    · change redp p (x.α + y.α + liftp p (redp p x.γ * redp p y.α)) = 0
      rw [map_add, map_add, redp_liftp, hx1, hy1]
      ring
    · change redp p (x.γ + y.γ) = 0
      rw [map_add, hx2, hy2]
      ring
  one_mem' := by
    rw [Set.mem_setOf_eq]
    exact one_pow p
  inv_mem' := by
    intro x hx
    rw [Set.mem_setOf_eq, pow_p_eq_one_iff] at hx ⊢
    obtain ⟨hx1, hx2⟩ := hx
    constructor
    · change redp p (-x.α + liftp p (redp p x.γ * redp p x.α)) = 0
      rw [map_add, map_neg, redp_liftp, hx1]
      ring
    · change redp p (-x.γ) = 0
      rw [map_neg, hx2]
      ring

theorem mem_torsionW {x : M8 p} : x ∈ torsionW p ↔ x ^ p = 1 := Iff.rfl

variable (p) in
theorem card_torsionW : Nat.card (torsionW p) = p ^ 2 := by
  have h := card_omega p
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => mem_torsionW)

variable (p) in
/-- **Table row (viii), second column**: `M8` has exactly `p² + p + 1`
subgroups of order `p²`. -/
theorem card_order_p2_subgroups_m8 :
    Nat.card {H : Subgroup (M8 p) // Nat.card H = p ^ 2} =
      p ^ 2 + p + 1 := by
  classical
  have hp : p.Prime := Fact.out
  have hΩ1 : (univ.filter fun x : M8 p => x ^ p = 1).card = p ^ 2 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact card_omega p
  have hΩ2 : (univ.filter fun x : M8 p => x ^ p ^ 2 = 1).card = p ^ 4 := by
    have hall : (univ.filter fun x : M8 p => x ^ p ^ 2 = 1) = univ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact pow_p_sq x
    rw [hall, Finset.card_univ, ← Nat.card_eq_fintype_card, card_m8]
  have hcount : (univ.filter fun x : M8 p => orderOf x = p ^ 2).card =
      p ^ 4 - p ^ 2 := by
    rw [card_orderOf_sq_sub, hΩ1, hΩ2]
  have hcyc := card_orderOf_eq_prime_sq (G := M8 p) (p := p)
  rw [hcount] at hcyc
  have harith : p ^ 4 - p ^ 2 = (p ^ 2 + p) * (p ^ 2 - p) := by
    have h1 : (p ^ 2 + p) * (p ^ 2 - p) = p ^ 2 * p ^ 2 + p * p ^ 2 -
        (p ^ 2 * p + p * p) := by
      rw [Nat.add_mul, Nat.mul_sub, Nat.mul_sub]
      have hle1 : p ^ 2 * p ≤ p ^ 2 * p ^ 2 := by
        refine Nat.mul_le_mul_left _ ?_
        nlinarith [hp.one_lt]
      have hle2 : p * p ≤ p * p ^ 2 := by
        refine Nat.mul_le_mul_left _ ?_
        nlinarith [hp.one_lt]
      omega
    have h2 : p ^ 2 * p ^ 2 = p ^ 4 := by ring
    have h3 : p ^ 2 * p + p * p ^ 2 = 2 * p ^ 3 := by ring
    have h4 : p * p = p ^ 2 := by ring
    have h5 : p * p ^ 2 = p ^ 3 := by ring
    have h6 : p ^ 2 * p = p ^ 3 := by ring
    have hle : p ^ 3 + p ^ 2 ≤ p ^ 4 + p ^ 3 := by
      nlinarith [hp.one_lt, pow_pos hp.pos 2, pow_pos hp.pos 3]
    omega
  rw [harith] at hcyc
  have hpos : 0 < p ^ 2 - p := by
    have h1 := hp.one_lt
    have h2 : p < p ^ 2 := by nlinarith
    omega
  have hN : Nat.card {H : Subgroup (M8 p) //
      Nat.card H = p ^ 2 ∧ IsCyclic H} = p ^ 2 + p :=
    (Nat.eq_of_mul_eq_mul_right hpos hcyc).symm
  rw [card_p2_subgroups (torsionW p) (card_torsionW p)
    (fun x => mem_torsionW.symm), hN]

end M8

end P4

end LeanDring
