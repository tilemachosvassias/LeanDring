/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P4.PairCount

/-!
# The socle decomposition for order-`p²` subgroup counts

For a finite `p`-group `G` of exponent `p²`, the order-`p²` subgroups split into
the cyclic ones and the elementary-abelian ones, and every elementary-abelian
order-`p²` subgroup lies inside the **socle** — any subgroup `Ω ≤ G` of exponent
`p` that contains all `p`-torsion. Since the order-`p²` subgroups of `Ω` are
exactly its noncyclic ones (viewed in `G`), we get

  `N_{p²}(G) = #{cyclic order-p² subgroups} + N_{p²}(Ω)`.

This reduces the order-`p²` subgroup count of an exponent-`p²` model (`G9`, `CH7`,
`Gid3`, `Gid8`, `Model`) to a count on its exponent-`p` socle, where the
exponent-`p` engine (`card_p2_subgroups_mul_eq_pairs`) applies.
-/

namespace LeanDring.P4

open Finset

variable {p : ℕ} [Fact p.Prime]
variable {G : Type*} [Group G] [Finite G]

omit [Fact p.Prime] in
/-- An order-`p²` group with an element of order `p²` is cyclic. -/
theorem isCyclic_of_orderOf_sq {H : Subgroup G} (hH : Nat.card H = p ^ 2)
    {g : H} (hg : orderOf g = p ^ 2) : IsCyclic H :=
  isCyclic_of_orderOf_eq_card g (by rw [hg, hH])

/-- For an order-`p²` subgroup, being noncyclic is equivalent to lying inside a
socle `Ω` (an exponent-`p` subgroup containing all `p`-torsion). -/
theorem not_isCyclic_iff_le_socle {H : Subgroup G} (hH : Nat.card H = p ^ 2)
    (Ω : Subgroup G) (hΩexp : ∀ x ∈ Ω, x ^ p = 1)
    (hΩtors : ∀ x : G, x ^ p = 1 → x ∈ Ω) :
    ¬ IsCyclic H ↔ H ≤ Ω := by
  have hp : p.Prime := Fact.out
  constructor
  · intro hnc x hx
    apply hΩtors x
    have hgo : orderOf (⟨x, hx⟩ : H) ∣ p ^ 2 := hH ▸ orderOf_dvd_natCard _
    rcases (Nat.dvd_prime_pow hp).mp hgo with ⟨k, hk, hord⟩
    interval_cases k
    · have hg1 : (⟨x, hx⟩ : H) = 1 := orderOf_eq_one_iff.mp (by simpa using hord)
      have : x = 1 := by simpa using congrArg Subtype.val hg1
      rw [this]; exact one_pow p
    · have hgp : (⟨x, hx⟩ : H) ^ p = 1 := by
        have hop : orderOf (⟨x, hx⟩ : H) = p := by simpa using hord
        rw [← hop]; exact pow_orderOf_eq_one _
      exact by simpa [SubmonoidClass.coe_pow] using congrArg Subtype.val hgp
    · exact absurd (isCyclic_of_orderOf_sq hH (g := ⟨x, hx⟩)
        (by simpa using hord)) hnc
  · intro hle hcyc
    haveI := hcyc
    obtain ⟨g, hgen⟩ := IsCyclic.exists_generator (α := ↥H)
    haveI : Fintype H := Fintype.ofFinite _
    have hgo : orderOf g = p ^ 2 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hgen, hH]
    have hgHp : g ^ p = 1 := by
      have h : (g : G) ^ p = 1 := hΩexp _ (hle g.2)
      exact Subtype.ext (by simpa [SubmonoidClass.coe_pow] using h)
    have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgHp
    rw [hgo] at hdvd
    have : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos hdvd
    nlinarith [hp.one_lt]

omit [Fact p.Prime] [Finite G] in
/-- Subgroups of `G` of order `p²` lying inside `Ω` biject with the order-`p²`
subgroups of `Ω`. -/
theorem card_p2_le_socle_eq (Ω : Subgroup G) :
    Nat.card {H : Subgroup G // Nat.card H = p ^ 2 ∧ H ≤ Ω} =
      Nat.card {K : Subgroup Ω // Nat.card K = p ^ 2} := by
  have hinj : Function.Injective Ω.subtype := Subgroup.subtype_injective Ω
  refine Nat.card_congr (Equiv.symm ?_)
  refine
    { toFun := fun K => ⟨K.1.map Ω.subtype, ?_, Subgroup.map_subtype_le K.1⟩
      invFun := fun H => ⟨H.1.subgroupOf Ω, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [Nat.card_congr (Subgroup.equivMapOfInjective K.1 Ω.subtype hinj).toEquiv.symm]
    exact K.2
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe H.2.2).toEquiv]
    exact H.2.1
  · rintro ⟨K, hK⟩
    exact Subtype.ext (Subgroup.comap_map_eq_self_of_injective hinj K)
  · rintro ⟨H, hH, hle⟩
    exact Subtype.ext (Subgroup.map_subgroupOf_eq_of_le hle)

/-- **Socle decomposition of the order-`p²` subgroup count.**
If `Ω ≤ G` has exponent `p` and contains every `p`-torsion element, then
`N_{p²}(G) = #{cyclic order-p² subgroups} + N_{p²}(Ω)`. -/
theorem card_p2_subgroups_socle (Ω : Subgroup G)
    (hΩexp : ∀ x ∈ Ω, x ^ p = 1) (hΩtors : ∀ x : G, x ^ p = 1 → x ∈ Ω) :
    Nat.card {H : Subgroup G // Nat.card H = p ^ 2} =
      Nat.card {H : Subgroup G // Nat.card H = p ^ 2 ∧ IsCyclic H} +
        Nat.card {K : Subgroup Ω // Nat.card K = p ^ 2} := by
  classical
  haveI : Fintype (Subgroup G) := Fintype.ofFinite _
  have hsplit : Nat.card {H : Subgroup G // Nat.card H = p ^ 2} =
      Nat.card {H : Subgroup G // Nat.card H = p ^ 2 ∧ IsCyclic H} +
        Nat.card {H : Subgroup G // Nat.card H = p ^ 2 ∧ ¬ IsCyclic H} := by
    rw [Nat.card_eq_fintype_card (α := {H : Subgroup G // Nat.card H = p ^ 2}),
      Nat.card_eq_fintype_card (α := {H : Subgroup G // Nat.card H = p ^ 2 ∧ IsCyclic H}),
      Nat.card_eq_fintype_card (α := {H : Subgroup G // Nat.card H = p ^ 2 ∧ ¬ IsCyclic H}),
      Fintype.card_subtype, Fintype.card_subtype, Fintype.card_subtype]
    have e1 : (univ.filter fun H : Subgroup G => Nat.card H = p ^ 2 ∧ IsCyclic H) =
        (univ.filter fun H : Subgroup G => Nat.card H = p ^ 2).filter
          (fun H : Subgroup G => IsCyclic H) := by rw [Finset.filter_filter]
    have e2 : (univ.filter fun H : Subgroup G => Nat.card H = p ^ 2 ∧ ¬ IsCyclic H) =
        (univ.filter fun H : Subgroup G => Nat.card H = p ^ 2).filter
          (fun H : Subgroup G => ¬ IsCyclic H) := by rw [Finset.filter_filter]
    rw [e1, e2, Finset.card_filter_add_card_filter_not]
  rw [hsplit]
  congr 1
  rw [← card_p2_le_socle_eq Ω]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun H => ?_)
  by_cases hH : Nat.card H = p ^ 2
  · simp only [hH, true_and]
    exact not_isCyclic_iff_le_socle hH Ω hΩexp hΩtors
  · constructor <;> intro h <;> exact absurd h.1 hH

omit [Fact p.Prime] in
/-- Arithmetic identity behind the abelian socle count, valid for `1 ≤ p`. -/
theorem sq_factor_mul_eq (hp : 1 ≤ p) :
    (p ^ 2 + p + 1) * ((p ^ 2 - 1) * (p ^ 2 - p)) = (p ^ 3 - 1) * (p ^ 3 - p) := by
  have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : p ≤ p ^ 2 := by nlinarith
  have h3 : 1 ≤ p ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h4 : p ≤ p ^ 3 := by nlinarith
  zify [h1, h2, h3, h4]
  ring

/-- **`N_{p²} = p² + p + 1` for an abelian exponent-`p` group of order `p³`.**
The exponent-`p` pair-counting engine, with every centralizer the whole group. -/
theorem card_p2_subgroups_abelian_exp_p [Fact (Odd p)]
    (hcomm : ∀ x y : G, x * y = y * x) (hexp : ∀ x : G, x ^ p = 1)
    (hcard : Nat.card G = p ^ 3) :
    Nat.card {H : Subgroup G // Nat.card H = p ^ 2} = p ^ 2 + p + 1 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hp : p.Prime := Fact.out
  have hcardF : Fintype.card G = p ^ 3 := by rw [← Nat.card_eq_fintype_card, hcard]
  have hkey := card_p2_subgroups_mul_eq_pairs (G := G) hexp
  -- every centralizer is the whole group
  have hcent : ∀ x : G, (univ.filter fun y : G => y * x = x * y) = univ := fun x =>
    Finset.filter_true_of_mem fun y _ => hcomm y x
  -- evaluate the RHS sum
  have hsum : ∑ x ∈ univ.filter (fun x : G => x ≠ 1),
      ((univ.filter fun y : G => y * x = x * y).card - p) =
      (p ^ 3 - 1) * (p ^ 3 - p) := by
    have hconst : ∀ x ∈ univ.filter (fun x : G => x ≠ 1),
        ((univ.filter fun y : G => y * x = x * y).card - p) = p ^ 3 - p := by
      intro x _
      rw [hcent x, Finset.card_univ, hcardF]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
    congr 1
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ 1),
      Finset.card_univ, hcardF]
  rw [hsum] at hkey
  -- solve  N · ((p²-1)(p²-p)) = (p³-1)(p³-p)  for  N = p²+p+1
  have hpos : 0 < (p ^ 2 - 1) * (p ^ 2 - p) := by
    have h1 : 1 < p ^ 2 := by nlinarith [hp.one_lt]
    have h2 : p < p ^ 2 := by nlinarith [hp.one_lt]
    exact Nat.mul_pos (by omega) (by omega)
  have := hkey.trans (sq_factor_mul_eq (le_of_lt hp.one_lt)).symm
  exact Nat.eq_of_mul_eq_mul_right hpos this

omit [Fact p.Prime] in
/-- Arithmetic identity behind the nonabelian (Heisenberg) socle count, `1 ≤ p`:
`(p+1)·((p²-1)(p²-p)) = (p-1)(p³-p) + (p³-p)(p²-p)` (both `= p·(p²-1)²`). -/
theorem heis_factor_mul_eq (hp : 1 ≤ p) :
    (p + 1) * ((p ^ 2 - 1) * (p ^ 2 - p)) =
      (p - 1) * (p ^ 3 - p) + (p ^ 3 - p) * (p ^ 2 - p) := by
  have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : p ≤ p ^ 2 := by nlinarith
  have h4 : p ≤ p ^ 3 := by nlinarith
  zify [h1, h2, h4, hp]
  ring

/-- **`N_{p²} = p + 1` for a nonabelian exponent-`p` group of order `p³`** (the
Heisenberg / extraspecial type). The exponent-`p` pair-counting engine with the
centralizer sum split into the central stratum (`|C|=p³`, `p-1` elements) and the
non-central stratum (`|C|=p²`, `p³-p` elements). -/
theorem card_p2_subgroups_nonabelian_exp_p [Fact (Odd p)]
    (hexp : ∀ x : G, x ^ p = 1) (hcard : Nat.card G = p ^ 3)
    (hnonab : ∃ a b : G, a * b ≠ b * a) :
    Nat.card {H : Subgroup G // Nat.card H = p ^ 2} = p + 1 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hp : p.Prime := Fact.out
  have hp1 := hp.one_lt
  have hcardF : Fintype.card G = p ^ 3 := by rw [← Nat.card_eq_fintype_card, hcard]
  haveI : Nontrivial G :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; exact Nat.one_lt_pow (by norm_num) hp1)
  have hpg : IsPGroup p G := IsPGroup.of_card hcard
  -- Step 2: the center of a nonabelian order-`p³` group has order `p`.
  have hZcard : Nat.card (Subgroup.center G) = p := by
    have hZdvd : Nat.card (Subgroup.center G) ∣ p ^ 3 :=
      hcard ▸ Subgroup.card_subgroup_dvd_card (Subgroup.center G)
    obtain ⟨k, hk3, hZk⟩ := (Nat.dvd_prime_pow hp).mp hZdvd
    haveI : Nontrivial (Subgroup.center G) := hpg.center_nontrivial
    have hk1 : 1 ≤ k := by
      by_contra h
      push Not at h
      interval_cases k
      rw [pow_zero] at hZk
      have h1 : 1 < Nat.card (Subgroup.center G) :=
        Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      omega
    have hkne3 : k ≠ 3 := by
      intro hk
      have htop : Subgroup.center G = ⊤ :=
        Subgroup.eq_top_of_card_eq _ (by rw [hZk, hk, hcard])
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab (Subgroup.mem_center_iff.mp (by rw [htop]; exact Subgroup.mem_top a) b).symm
    have hkne2 : k ≠ 2 := by
      intro hk
      have hquot : Nat.card (G ⧸ Subgroup.center G) = p := by
        have hL := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G)
        rw [hcard, hZk, hk] at hL
        have hL2 : Nat.card (G ⧸ Subgroup.center G) * p ^ 2 = p * p ^ 2 := by
          rw [← hL]; ring
        exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 2) hL2
      haveI : IsCyclic (G ⧸ Subgroup.center G) := isCyclic_of_prime_card hquot
      have hcomm := isMulCommutative_of_isCyclic_quotient_center_self G
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab (hcomm.is_comm.comm a b)
    have hk2 : k = 1 := by omega
    rw [hZk, hk2, pow_one]
  -- Step 3: relate the commuting-pair Finset to the centralizer subgroup.
  have hcard_cent : ∀ x : G, Nat.card (Subgroup.centralizer ({x} : Set G)) =
      (univ.filter (fun y : G => y * x = x * y)).card := by
    intro x
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    exact eq_comm
  -- central elements: full centralizer of order `p³`
  have hcent_central : ∀ x : G, x ∈ Subgroup.center G →
      (univ.filter (fun y : G => y * x = x * y)).card = p ^ 3 := by
    intro x hx
    have hall : (univ.filter (fun y : G => y * x = x * y)) = univ :=
      Finset.filter_true_of_mem (fun y _ => Subgroup.mem_center_iff.mp hx y)
    rw [hall, Finset.card_univ, hcardF]
  -- non-central elements: centralizer of order `p²`
  have hcent_noncentral : ∀ x : G, x ∉ Subgroup.center G →
      (univ.filter (fun y : G => y * x = x * y)).card = p ^ 2 := by
    intro x hxZ
    rw [← hcard_cent x]
    have hxC : x ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff.mp hg]
    have hZC : Subgroup.center G ≤ Subgroup.centralizer ({x} : Set G) :=
      Subgroup.center_le_centralizer _
    have hCdvd : Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ p ^ 3 :=
      hcard ▸ Subgroup.card_subgroup_dvd_card _
    obtain ⟨m, hm3, hCm⟩ := (Nat.dvd_prime_pow hp).mp hCdvd
    have hle : p ≤ p ^ m := by
      have := Subgroup.card_le_of_le hZC
      rwa [hZcard, hCm] at this
    have hm1 : 1 ≤ m := by
      by_contra h
      push Not at h
      interval_cases m
      rw [pow_zero] at hle
      omega
    have hmne1 : m ≠ 1 := by
      intro hm
      have hcle : Nat.card (Subgroup.centralizer ({x} : Set G)) ≤ Nat.card (Subgroup.center G) := by
        rw [hCm, hZcard, hm, pow_one]
      have hZeqC : Subgroup.center G = Subgroup.centralizer ({x} : Set G) :=
        Subgroup.eq_of_le_of_card_ge hZC hcle
      exact hxZ (by rw [hZeqC]; exact hxC)
    have hmne3 : m ≠ 3 := by
      intro hm
      apply hxZ
      have hCtop : Subgroup.centralizer ({x} : Set G) = ⊤ :=
        Subgroup.eq_top_of_card_eq _ (by rw [hCm, hm, hcard])
      rw [Subgroup.mem_center_iff]
      intro g
      have hgC : g ∈ Subgroup.centralizer ({x} : Set G) := hCtop ▸ Subgroup.mem_top g
      rw [Subgroup.mem_centralizer_iff] at hgC
      exact (hgC x (Set.mem_singleton x)).symm
    have hm2 : m = 2 := by omega
    rw [hCm, hm2]
  -- Step 4: evaluate the pair-count sum by splitting central / non-central.
  have hkey := card_p2_subgroups_mul_eq_pairs (G := G) hexp
  have hZfin : (univ.filter (fun x : G => x ∈ Subgroup.center G)).card = p := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact hZcard
  have hsum : ∑ x ∈ univ.filter (fun x : G => x ≠ 1),
      ((univ.filter (fun y : G => y * x = x * y)).card - p) =
      (p - 1) * (p ^ 3 - p) + (p ^ 3 - p) * (p ^ 2 - p) := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (univ.filter (fun x : G => x ≠ 1)) (fun x => x ∈ Subgroup.center G)]
    have hc1 : ∀ x ∈ (univ.filter (fun x : G => x ≠ 1)).filter
        (fun x => x ∈ Subgroup.center G),
        ((univ.filter (fun y : G => y * x = x * y)).card - p) = p ^ 3 - p := by
      intro x hx
      rw [hcent_central x (Finset.mem_filter.mp hx).2]
    have hc2 : ∀ x ∈ (univ.filter (fun x : G => x ≠ 1)).filter
        (fun x => ¬ x ∈ Subgroup.center G),
        ((univ.filter (fun y : G => y * x = x * y)).card - p) = p ^ 2 - p := by
      intro x hx
      rw [hcent_noncentral x (Finset.mem_filter.mp hx).2]
    rw [Finset.sum_congr rfl hc1, Finset.sum_congr rfl hc2,
      Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
    have hZstar : ((univ.filter (fun x : G => x ≠ 1)).filter
        (fun x => x ∈ Subgroup.center G)).card = p - 1 := by
      have hswap : ((univ.filter (fun x : G => x ≠ 1)).filter
          (fun x => x ∈ Subgroup.center G)) =
          (univ.filter (fun x : G => x ∈ Subgroup.center G)).erase 1 := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      rw [hswap, Finset.card_erase_of_mem (by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact (Subgroup.center G).one_mem), hZfin]
    have htot : (univ.filter (fun x : G => x ≠ 1)).card = p ^ 3 - 1 := by
      have h1 : (univ.filter (fun x : G => x ≠ 1)) = univ.erase 1 := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
      rw [h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcardF]
    have hNZ : ((univ.filter (fun x : G => x ≠ 1)).filter
        (fun x => ¬ x ∈ Subgroup.center G)).card = p ^ 3 - p := by
      have hadd := Finset.card_filter_add_card_filter_not
        (s := univ.filter (fun x : G => x ≠ 1)) (fun x => x ∈ Subgroup.center G)
      rw [hZstar, htot] at hadd
      have hpp : p ≤ p ^ 3 := Nat.le_self_pow (by norm_num) p
      have hp0 : 1 ≤ p := hp.pos
      omega
    rw [hZstar, hNZ]
  rw [hsum] at hkey
  -- Step 5: cancel the positive factor `(p²−1)(p²−p)`.
  have hpos : 0 < (p ^ 2 - 1) * (p ^ 2 - p) := by
    have h1 : 1 < p ^ 2 := by nlinarith [hp1]
    have h2 : p < p ^ 2 := by nlinarith [hp1]
    exact Nat.mul_pos (by omega) (by omega)
  have hfin := hkey.trans (heis_factor_mul_eq (le_of_lt hp1)).symm
  exact Nat.eq_of_mul_eq_mul_right hpos hfin

end LeanDring.P4
