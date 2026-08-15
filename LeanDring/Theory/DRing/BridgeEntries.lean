/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.Induced
import Mathlib.Algebra.Group.Subgroup.Finite

-- The `[Fintype _]` binders below are unused in several *statements* but are
-- load-bearing in their *proofs* (instance synthesis for cardinality and basis
-- constructions), so they cannot be `omit`ted.  The linter's suggested rewrite
-- to `[Finite _]` + `Fintype.ofFinite` is a genuine refactor, not a cleanup.
set_option linter.unusedFintypeInType false

/-!
# The species table knows the subgroup orders: entry-extraction lemmas

The bridge "species-table isomorphism ⇒ equal subgroup counts per order"
(in the style of [Hue09]) reduces to reading off group data from individual
table entries. This file proves the two readings:

* `species_bot_one_basisElt` — the **augmentation entry**:
  `φ_{1,1}[K,1] = |G/K| = |G|/|K|`, so a table correspondence preserves
  subgroup **orders**;
* `species_self_one_basisElt` — the **diagonal entry**:
  `φ_{K,1}[K,1] = #(G/K)^K`, and `card_fixedPoints_coset` identifies
  `#(G/K)^K · |K| = |N(K)|`, so the pair of entries determines the
  **conjugacy-class size** `|G|/|N(K)| = φ_{1,1}[K,1] / φ_{K,1}[K,1]`.

Together: subgroup counts per order are functions of the mark sub-table
of the species table — the transport step of the block correspondence.
-/

namespace LeanDring

open MulAction Finset

universe u

variable {G : Type u} [Group G] [Fintype G]

namespace DRing

open MonGSet

/-- **The augmentation entry**: `φ_{1,1}[K,1] = |G/K|`. -/
theorem species_bot_one_basisElt (K : Subgroup G) :
    species (⊥ : Subgroup G) 1 (basisElt K (1 : K →* ℂˣ)) =
      (Nat.card (G ⧸ K) : ℂ) := by
  classical
  rw [species_basisElt]
  have hval : ∀ q : fixedPoints (⊥ : Subgroup G)
      (induced K (1 : K →* ℂˣ) : MonGSet G ℂˣ).carrier,
      (((1 : K →* ℂˣ) ⟨q.1.out⁻¹ * ((1 : (⊥ : Subgroup G)) : G) * q.1.out,
        sectionConj_mem K ⊥ 1 q.1 (q.2 1)⟩ : ℂˣ) : ℂ) = 1 := by
    intro q
    rw [MonoidHom.one_apply]
    rfl
  rw [Finset.sum_congr rfl fun q _ => hval q, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  -- every coset is `⊥`-fixed
  have hall : ∀ x : (induced K (1 : K →* ℂˣ) : MonGSet G ℂˣ).carrier,
      x ∈ fixedPoints (⊥ : Subgroup G)
        (induced K (1 : K →* ℂˣ) : MonGSet G ℂˣ).carrier := by
    intro x k
    have hk : (k : G) = 1 := Subgroup.mem_bot.mp k.2
    change (k : G) • x = x
    rw [hk, one_smul]
  rw [Finset.card_univ, Fintype.card_congr (Equiv.subtypeUnivEquiv hall)]
  have hcard : Fintype.card
      ((induced K (1 : K →* ℂˣ) : MonGSet G ℂˣ).carrier) =
      Nat.card (G ⧸ K) := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [hcard]

/-- **The diagonal entry**: `φ_{K,1}[K,1] = #{K-fixed cosets in G/K}`. -/
theorem species_self_one_basisElt (K : Subgroup G) :
    species K 1 (basisElt K (1 : K →* ℂˣ)) =
      (Nat.card (fixedPoints K (G ⧸ K)) : ℂ) := by
  classical
  rw [species_basisElt]
  have hval : ∀ q : fixedPoints K
      (induced K (1 : K →* ℂˣ) : MonGSet G ℂˣ).carrier,
      (((1 : K →* ℂˣ) ⟨q.1.out⁻¹ * ((1 : K) : G) * q.1.out,
        sectionConj_mem K K 1 q.1 (q.2 1)⟩ : ℂˣ) : ℂ) = 1 := by
    intro q
    rw [MonoidHom.one_apply]
    rfl
  rw [Finset.sum_congr rfl fun q _ => hval q, Finset.sum_const,
    nsmul_eq_mul, mul_one, Finset.card_univ, ← Nat.card_eq_fintype_card]
  rfl

end DRing

-- `[Fintype G]` is unused in the type but load-bearing in the proof
-- (instance synthesis for the fixed-point cardinality); keep it.
/-- **Fixed cosets and the normalizer**: `#(G/K)^K · |K| = |N(K)|`. -/
theorem card_fixedPoints_coset (K : Subgroup G) :
    Nat.card (fixedPoints K (G ⧸ K)) * Nat.card K =
      Nat.card (Subgroup.normalizer (K : Set G)) := by
  classical
  -- the fixed cosets are exactly the normalizer cosets
  have hfix : ∀ g : G, ((g : G ⧸ K) ∈ fixedPoints K (G ⧸ K)) ↔
      g ∈ Subgroup.normalizer (K : Set G) := by
    intro g
    constructor
    · intro hg
      have hconj : ∀ k ∈ K, g⁻¹ * k * g ∈ K := by
        intro k hk
        have h1 := hg ⟨k⁻¹, K.inv_mem hk⟩
        have h2 : ((k⁻¹ * g : G) : G ⧸ K) = (g : G ⧸ K) := h1
        have h3 := (QuotientGroup.eq).mp h2
        rwa [mul_inv_rev, inv_inv] at h3
      have hginv : g⁻¹ ∈ Subgroup.normalizer (K : Set G) := by
        refine Subgroup.mem_normalizer_fintype ?_
        intro k hk
        have h4 := hconj k hk
        simpa [inv_inv] using h4
      simpa using Subgroup.inv_mem _ hginv
    · intro hg k
      change ((k : G) * g : G ⧸ K) = (g : G ⧸ K)
      refine (QuotientGroup.eq).mpr ?_
      have h1 : g⁻¹ * (k : G)⁻¹ * g ∈ K := by
        rw [Subgroup.mem_normalizer_iff] at hg
        refine (hg (g⁻¹ * (k : G)⁻¹ * g)).mpr ?_
        have h2 : g * (g⁻¹ * (k : G)⁻¹ * g) * g⁻¹ = (k : G)⁻¹ := by group
        rw [h2]
        exact K.inv_mem k.2
      rw [mul_inv_rev]
      exact h1
  -- fixed points ≃ `N(K) ⧸ K`
  set N := Subgroup.normalizer (K : Set G) with hN
  set K' := K.subgroupOf N with hK'
  have hmemK' : ∀ n : N, n ∈ K' ↔ (n : G) ∈ K := fun n =>
    Subgroup.mem_subgroupOf
  let F : N ⧸ K' → fixedPoints K (G ⧸ K) := fun q =>
    ⟨(((q.out : N) : G) : G ⧸ K), (hfix _).mpr (q.out).2⟩
  have hFinj : Function.Injective F := by
    intro q q' hqq
    have h1 : (((q.out : N) : G) : G ⧸ K) = (((q'.out : N) : G) : G ⧸ K) :=
      congrArg Subtype.val hqq
    have h2 : ((q.out : N) : G)⁻¹ * ((q'.out : N) : G) ∈ K :=
      (QuotientGroup.eq).mp h1
    have h3 : (q.out)⁻¹ * q'.out ∈ K' := by
      rw [hmemK']
      exact h2
    have h4 : (q.out : N ⧸ K') = (q'.out : N ⧸ K') :=
      (QuotientGroup.eq).mpr h3
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h4
  have hFsurj : Function.Surjective F := by
    intro x
    have hx1 : ((x.1.out : G) : G ⧸ K) = x.1 := QuotientGroup.out_eq' _
    have hxfix : ((x.1.out : G) : G ⧸ K) ∈ fixedPoints K (G ⧸ K) := by
      rw [hx1]
      exact x.2
    have hgN : x.1.out ∈ N := (hfix _).mp hxfix
    refine ⟨((⟨x.1.out, hgN⟩ : N) : N ⧸ K'), ?_⟩
    refine Subtype.ext ?_
    change ((((((⟨x.1.out, hgN⟩ : N) : N ⧸ K')).out : N) : G) : G ⧸ K) = x.1
    have h5 : (((((⟨x.1.out, hgN⟩ : N) : N ⧸ K')).out : N) : N ⧸ K') =
        ((⟨x.1.out, hgN⟩ : N) : N ⧸ K') := QuotientGroup.out_eq' _
    have h6 : ((((⟨x.1.out, hgN⟩ : N) : N ⧸ K')).out)⁻¹ *
        (⟨x.1.out, hgN⟩ : N) ∈ K' := (QuotientGroup.eq).mp h5
    have h7 : ((((((⟨x.1.out, hgN⟩ : N) : N ⧸ K')).out : N) : G))⁻¹ *
        x.1.out ∈ K := by
      rw [hmemK'] at h6
      exact h6
    have h8 : ((((((⟨x.1.out, hgN⟩ : N) : N ⧸ K')).out : N) : G) : G ⧸ K) =
        ((x.1.out : G) : G ⧸ K) := (QuotientGroup.eq).mpr h7
    rw [h8, hx1]
  have hcardeq : Nat.card (fixedPoints K (G ⧸ K)) = Nat.card (N ⧸ K') :=
    (Nat.card_eq_of_bijective F ⟨hFinj, hFsurj⟩).symm
  have hKK' : Nat.card K' = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup K'
  rw [hcardeq, ← hKK', hmul]

end LeanDring
