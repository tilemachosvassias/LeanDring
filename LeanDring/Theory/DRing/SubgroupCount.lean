/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import Mathlib.GroupTheory.Sylow

/-!
# Counting subgroups of prime order: the double-counting brick

`card_orderOf_eq_prime`: in any finite group,
`#{g : orderOf g = p} = #{H : |H| = p} · (p − 1)` — each order-`p` subgroup
contains exactly `p − 1` elements of order `p`, and every such element
generates exactly one such subgroup.

This is the stage-2 engine for proving the `p⁴` subgroup-count table from
concrete group models: once `Ω₁(G) ≅ (C_p)³` is established for group
(xii), `#{order-p elements} = p³ − 1` gives
`#{order-p subgroups} = p² + p + 1` — as a theorem, generically in `p`.
-/

namespace LeanDring

namespace P4

open Subgroup Finset

variable {G : Type*} [Group G] {p : ℕ}

/-- A non-identity element of a subgroup of prime order `p` has order `p`. -/
theorem orderOf_eq_prime_of_mem {H : Subgroup G} (hp : p.Prime)
    (hH : Nat.card H = p) {y : G} (hy : y ∈ H) (hy1 : y ≠ 1) :
    orderOf y = p := by
  have hfin : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; exact hp.ne_zero)
  have h1 : orderOf (⟨y, hy⟩ : H) ∣ p := by
    rw [← hH]
    exact orderOf_dvd_natCard _
  have h2 : orderOf y = orderOf (⟨y, hy⟩ : H) :=
    orderOf_injective H.subtype H.subtype_injective ⟨y, hy⟩
  rw [h2]
  rcases (Nat.dvd_prime hp).mp h1 with h | h
  · exfalso
    apply hy1
    have hone : (⟨y, hy⟩ : H) = 1 := orderOf_eq_one_iff.mp h
    simpa using congrArg Subtype.val hone
  · exact h

/-- A non-identity element of a subgroup of prime order generates it. -/
theorem zpowers_eq_of_mem {H : Subgroup G} (hp : p.Prime)
    (hH : Nat.card H = p) {y : G} (hy : y ∈ H) (hy1 : y ≠ 1) :
    Subgroup.zpowers y = H := by
  have hfin : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; exact hp.ne_zero)
  have hle : Subgroup.zpowers y ≤ H := Subgroup.zpowers_le.mpr hy
  have hcard : Nat.card (Subgroup.zpowers y) = Nat.card H := by
    rw [Nat.card_zpowers, orderOf_eq_prime_of_mem hp hH hy hy1, hH]
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)

variable [Fintype G]

/-- **The double-counting identity**: in a finite group,
`#{g : orderOf g = p} = #{H : Nat.card H = p} · (p − 1)`. -/
theorem card_orderOf_eq_prime (hp : p.Prime) :
    (univ.filter fun g : G => orderOf g = p).card =
      Nat.card {H : Subgroup G // Nat.card H = p} * (p - 1) := by
  classical
  haveI : Fintype (Subgroup G) := Fintype.ofFinite _
  set T : Finset (Subgroup G) := univ.filter (fun H => Nat.card H = p) with hT
  -- fiber the order-`p` elements by the subgroup they generate
  have hmapsto : ∀ g ∈ univ.filter (fun g : G => orderOf g = p),
      Subgroup.zpowers g ∈ T := by
    intro g hg
    rw [hT, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Nat.card_zpowers, (Finset.mem_filter.mp hg).2]
  rw [Finset.card_eq_sum_card_fiberwise hmapsto]
  -- each fiber is `H` minus the identity
  have hfiber : ∀ H ∈ T,
      ((univ.filter fun g : G => orderOf g = p).filter
        fun g => Subgroup.zpowers g = H).card = p - 1 := by
    intro H hH
    have hHp : Nat.card H = p := (Finset.mem_filter.mp hH).2
    have hset : ((univ.filter fun g : G => orderOf g = p).filter
        fun g => Subgroup.zpowers g = H) = (H : Set G).toFinset.erase 1 := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase, Set.mem_toFinset, SetLike.mem_coe]
      constructor
      · rintro ⟨ho, hz⟩
        refine ⟨?_, hz ▸ Subgroup.mem_zpowers g⟩
        intro h1
        rw [h1, orderOf_one] at ho
        have h2 := hp.one_lt
        omega
      · rintro ⟨h1, hmem⟩
        exact ⟨orderOf_eq_prime_of_mem hp hHp hmem h1,
          zpowers_eq_of_mem hp hHp hmem h1⟩
    rw [hset, Finset.card_erase_of_mem (by simp),
      Set.toFinset_card]
    rw [← Nat.card_eq_fintype_card]
    simp only [SetLike.coe_sort_coe]
    rw [hHp]
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul]
  congr 1
  -- `#T = Nat.card` of the subtype
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

end P4

end LeanDring
