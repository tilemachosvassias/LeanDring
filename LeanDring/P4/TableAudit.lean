/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import Mathlib.GroupTheory.Sylow

/-!
# The GJG10 table audit, as theorems: row (xi) is impossible

The GJG10 subgroup-count table claims the
nonabelian group (xi) of order `p⁴` has exactly **one** subgroup of order
`p³`. This is impossible — not merely refuted by computation:

* `isCyclic_of_unique_subgroup_card_pow`: a finite group of order `pⁿ`
  with a unique subgroup of order `pⁿ⁻¹` is **cyclic**. (Every proper
  subgroup extends to one of order `pⁿ⁻¹` by the Sylow chain; if that
  subgroup is unique, every non-generator lies in it.)
* `not_unique_subgroup_card_of_not_isCyclic`: contrapositive — a noncyclic
  group of order `pⁿ` has at least two subgroups of order `pⁿ⁻¹`.
* `p4_nonabelian_two_maximal`: the audit statement — a **nonabelian** group
  of order `p⁴` has two distinct subgroups of order `p³`; the corrected
  table value is `≥ 2` (in fact `p+1`, computationally).

So the count `1` in row (xi) cannot hold for any nonabelian group of order
`p⁴`, for **every** prime `p` — a proof, not a computation.
-/

namespace LeanDring

namespace P4

/-- **A finite group of order `pⁿ` with a unique subgroup of order `pⁿ⁻¹`
is cyclic.** -/
theorem isCyclic_of_unique_subgroup_card_pow {G : Type*} [Group G] [Finite G]
    {p n : ℕ} (hp : p.Prime) (hn : 0 < n) (hcard : Nat.card G = p ^ n)
    (huniq : ∀ M M' : Subgroup G, Nat.card M = p ^ (n - 1) →
      Nat.card M' = p ^ (n - 1) → M = M') :
    IsCyclic G := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨M₀, hM₀⟩ := Sylow.exists_subgroup_card_pow_prime p
    (n := n - 1) (by rw [hcard]; exact pow_dvd_pow p (by omega))
  by_contra hnc
  -- every element lies in the unique order-`pⁿ⁻¹` subgroup
  have hmem : ∀ g : G, g ∈ M₀ := by
    intro g
    have hdvd : Nat.card (Subgroup.zpowers g) ∣ p ^ n := by
      rw [← hcard]
      exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨i, hi, hcyc⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hne : Subgroup.zpowers g ≠ ⊤ := by
      intro htop
      refine hnc ⟨⟨g, fun x => ?_⟩⟩
      have hx : x ∈ Subgroup.zpowers g := htop.symm ▸ Subgroup.mem_top x
      exact hx
    have hilt : i ≤ n - 1 := by
      by_contra hgt
      have hin : i = n := by omega
      refine hne (Subgroup.eq_top_of_card_eq _ ?_)
      rw [hcyc, hin, hcard]
    obtain ⟨K, hKcard, hKle⟩ := Sylow.exists_subgroup_card_pow_prime_le p
      (by rw [hcard]; exact pow_dvd_pow p (by omega))
      (Subgroup.zpowers g) hcyc hilt
    have hKM : K = M₀ := huniq K M₀ hKcard hM₀
    exact hKM ▸ hKle (Subgroup.mem_zpowers g)
  -- hence `M₀ = ⊤`, contradicting its cardinality
  have htop : M₀ = ⊤ := by
    rw [Subgroup.eq_top_iff']
    exact hmem
  rw [htop] at hM₀
  have hcards : Nat.card G = p ^ (n - 1) := by
    rw [← hM₀]
    exact (Nat.card_congr Subgroup.topEquiv.toEquiv).symm
  rw [hcard] at hcards
  have := Nat.pow_right_injective hp.two_le hcards
  omega

/-- Contrapositive: a **noncyclic** group of order `pⁿ` has at least two
distinct subgroups of order `pⁿ⁻¹`. -/
theorem not_unique_subgroup_card_of_not_isCyclic {G : Type*} [Group G] [Finite G]
    {p n : ℕ} (hp : p.Prime) (hn : 0 < n) (hcard : Nat.card G = p ^ n)
    (hnc : ¬IsCyclic G) :
    ∃ M M' : Subgroup G, Nat.card M = p ^ (n - 1) ∧
      Nat.card M' = p ^ (n - 1) ∧ M ≠ M' := by
  by_contra h
  push Not at h
  exact hnc (isCyclic_of_unique_subgroup_card_pow hp hn hcard
    fun M M' hM hM' => h M M' hM hM')

/-- **The audit theorem (GJG10 row (xi) is impossible)**: a nonabelian
group of order `p⁴` has at least two distinct subgroups of order `p³` —
for every prime `p`. The table's claimed count `1` cannot occur. -/
theorem p4_nonabelian_two_maximal {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card G = p ^ 4)
    (hna : ∃ a b : G, a * b ≠ b * a) :
    ∃ M M' : Subgroup G, Nat.card M = p ^ 3 ∧ Nat.card M' = p ^ 3 ∧ M ≠ M' := by
  have hnc : ¬IsCyclic G := by
    intro hc
    obtain ⟨a, b, hab⟩ := hna
    letI := hc.commGroup
    exact hab (mul_comm a b)
  exact not_unique_subgroup_card_of_not_isCyclic hp (by norm_num) hcard hnc

end P4

end LeanDring
