/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SubgroupInventory.Twin1.AllSubgroupsProofs
import Mathlib.Order.Preorder.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Completeness of the 676-subgroup inventory

`LeanDring.P5.Certificate.SubgroupInventory.Twin1.AllSubgroups` certifies the 676
bases as well-formed `Cgs` (`allSubs`), and
`LeanDring.P5.Certificate.SubgroupInventory.Twin1.AllSubgroupsProofs` certifies
them pairwise distinct and records the two completeness anchors
`bot_mem_allSubs`, `top_mem_allSubs`. This file reduces **completeness** of the
inventory:

  `allSubs_complete : ∀ K, ∃ c ∈ allSubs, c.toSubgroup = K`

— every subgroup of `Coordinate 1` is presented by some member of `allSubs` — to
a single closure property of the inventory.

## The reduction

The completeness argument is a downward strong induction on subgroup order, glued
to a **covering step**: from any subgroup `H` already in the inventory, every
proper subgroup `K < H` descends into a strictly smaller subgroup that is *also*
in the inventory. Concretely:

* `card_lt` — a strictly smaller subgroup has strictly smaller order (finiteness);
* `exists_maxProper` — every proper `K < H` lies under a **maximal proper**
  subgroup `M` of `H` (`M < H` with nothing strictly between `M` and `H`); this
  is pure finite-lattice theory (`Set.Finite.exists_maximal`), no group input;
* `key` / `allSubs_complete_of_covering` — the downward strong induction that turns
  a covering hypothesis into full completeness, starting from `top_mem_allSubs`;
* `covering_of_maximalsClosed` — the covering hypothesis follows from the single
  group-theoretic fact `MaximalsClosed`.

## From `MaximalsClosed` to `NormalIndexFiveClosed`

`MaximalsClosed` says: *every maximal proper subgroup of an inventory member is
itself in the inventory.* The last section below proves, unconditionally, the
standard `p`-group structure of such a maximal subgroup `M < H` (`H` any subgroup of
`Coordinate 1`, hence a `5`-group): `M` is **normal in `H`** (`normal_of_maximal`),
of **index `5`** (`relIndex_eq_five_of_maximal`), and **contains the Frattini
subgroup** of `H` (`frattini_le_of_maximal`). Via `normal_of_isCoatom_pgroup` /
`card_quotient_eq_prime` this uses only Mathlib's nilpotency-of-`p`-groups,
correspondence theorem, and Cauchy's theorem — no `native_decide`, no new axioms.

Consequently `MaximalsClosed` reduces to the strictly narrower
`NormalIndexFiveClosed` (`maximalsClosed_of_normalIndexFiveClosed`): closure of the
inventory only under passage to **normal index-`5`** subgroups — the preimages of the
hyperplanes of each Frattini quotient `H⧸Φ(H)`. That residual fact needs
per-subgroup hyperplane-exhaustiveness data (the count `(5^r-1)/4` and `Φ`-witness
words), which is supplied and kernel-checked in
`LeanDring.P5.Certificate.SubgroupInventory.Twin1.FrattiniCert` and
`...Twin1.FratDischarge`; those files turn the conditional statements below into
the unconditional `allSubs_complete`.
-/

namespace LeanDring.P5Presentation

open Cgs

/-- `H` is presented by some member of the certified inventory `allSubs`. -/
def InInv (H : Subgroup (Coordinate 1)) : Prop := ∃ c ∈ allSubs, c.toSubgroup = H

/-- The two anchors as `InInv` facts. -/
theorem top_InInv : InInv (⊤ : Subgroup (Coordinate 1)) := top_mem_allSubs
theorem bot_InInv : InInv (⊥ : Subgroup (Coordinate 1)) := bot_mem_allSubs

/-! ## Finiteness: a strict subgroup inclusion strictly drops the order -/

/-- A strictly smaller subgroup of the (finite) group has strictly smaller order. -/
theorem card_lt {M H : Subgroup (Coordinate 1)} (h : M < H) :
    Nat.card M < Nat.card H := by
  have hss : (M : Set (Coordinate 1)) ⊂ (H : Set (Coordinate 1)) :=
    SetLike.coe_ssubset_coe.mpr h
  have hlt := Set.Finite.card_lt_card (Set.toFinite (H : Set (Coordinate 1))) hss
  simpa only [SetLike.coe_sort_coe] using hlt

/-! ## The finite-lattice covering step (no group theory) -/

/-- **Every proper subgroup lies under a maximal proper subgroup.** For `K < H`
there is an `M` with `K ≤ M < H` and nothing strictly between `M` and `H`. This is
purely the fact that the finite poset of subgroups between `K` and `H` has a
maximal element. -/
theorem exists_maxProper {K H : Subgroup (Coordinate 1)} (hKH : K < H) :
    ∃ M, K ≤ M ∧ M < H ∧ ∀ N, M < N → N < H → False := by
  set s : Set (Subgroup (Coordinate 1)) := {N | K ≤ N ∧ N < H} with hs
  have hfin : s.Finite := Set.toFinite s
  obtain ⟨M, hMmax⟩ := hfin.exists_maximal ⟨K, ⟨le_refl K, hKH⟩⟩
  obtain ⟨hKM, hMH⟩ := hMmax.1
  refine ⟨M, hKM, hMH, ?_⟩
  intro N hMN hNH
  have hNmem : N ∈ s := ⟨le_trans hKM (le_of_lt hMN), hNH⟩
  have hNM : N ≤ M := hMmax.2 hNmem (le_of_lt hMN)
  exact absurd hNM (not_le_of_gt hMN)

/-! ## The covering hypothesis and the completeness induction -/

/-- The covering property: inside the inventory, every proper descent lands under a
strictly smaller inventory member. -/
def Covering : Prop :=
  ∀ H : Subgroup (Coordinate 1), InInv H → ∀ K, K < H → ∃ M, InInv M ∧ K ≤ M ∧ M < H

/-- **Downward strong induction.** Under `Covering`, every subgroup below an
inventory member is itself in the inventory. -/
theorem key (cov : Covering) :
    ∀ n, ∀ H : Subgroup (Coordinate 1), Nat.card H = n → InInv H →
      ∀ K, K ≤ H → InInv K := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro H hn hH K hKH
    rcases eq_or_lt_of_le hKH with rfl | hlt
    · exact hH
    · obtain ⟨M, hM, hKM, hMH⟩ := cov H hH K hlt
      exact ih (Nat.card M) (hn ▸ card_lt hMH) M rfl hM K hKM

/-- **Completeness, conditional on `Covering`.** -/
theorem allSubs_complete_of_covering (cov : Covering) :
    ∀ K : Subgroup (Coordinate 1), ∃ c ∈ allSubs, c.toSubgroup = K := fun K =>
  key cov (Nat.card (⊤ : Subgroup (Coordinate 1))) ⊤ rfl top_InInv K le_top

/-! ## Reducing `Covering` to the single Frattini-completeness fact -/

/-- The closure property the completeness argument needs: every maximal proper
subgroup of an inventory member is itself in the inventory. -/
def MaximalsClosed : Prop :=
  ∀ H : Subgroup (Coordinate 1), InInv H → ∀ M, M < H →
    (∀ N, M < N → N < H → False) → InInv M

/-- `MaximalsClosed` implies `Covering`: pick a maximal proper subgroup above the
proper `K` (`exists_maxProper`), which `MaximalsClosed` puts in the inventory. -/
theorem covering_of_maximalsClosed (mc : MaximalsClosed) : Covering := by
  intro H hH K hKH
  obtain ⟨M, hKM, hMH, hMmax⟩ := exists_maxProper hKH
  exact ⟨M, mc H hH M hMH hMmax, hKM, hMH⟩

/-- **Completeness of the 676-subgroup inventory**, conditional on the single
Frattini-completeness fact `MaximalsClosed`. Every subgroup of `Coordinate 1` is
presented by one of the certified `Cgs` in `allSubs`. -/
theorem allSubs_complete_of_maximalsClosed (mc : MaximalsClosed) :
    ∀ K : Subgroup (Coordinate 1), ∃ c ∈ allSubs, c.toSubgroup = K :=
  allSubs_complete_of_covering (covering_of_maximalsClosed mc)

/-! ## The p-group structure of a maximal subgroup

The *shape* of a maximal proper subgroup of a finite `5`-group is standard: it is
**normal of index `5`** and **contains the Frattini subgroup**. This section
proves that structure unconditionally and uses it to reduce `MaximalsClosed` to
the strictly narrower fact `NormalIndexFiveClosed` — closure of the inventory
under passage to *normal index-`5`* subgroups (equivalently, to the hyperplanes of
each Frattini quotient). The residual hyperplane-exhaustiveness fact (the
per-subgroup `Φ`-witness data and the count `(5^r-1)/4`) is not proved here, so
the statements in this file stay conditional. -/

section PGroupMaximal

open Subgroup

variable {G : Type*} [_root_.Group G]

/-- **A coatom of a finite `p`-group is normal.** (Nilpotent groups satisfy the
normalizer condition, so every maximal subgroup is self-normalizing only if it is
the whole group.) -/
theorem normal_of_isCoatom_pgroup [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) {K : Subgroup G} (hK : IsCoatom K) : K.Normal :=
  ((_root_.Group.isNilpotent_of_finite_tfae (G := G)).out 0 2 rfl rfl).mp hG.isNilpotent K hK

/-- The quotient of a group by a coatom is nontrivial. -/
theorem nontrivial_quotient_of_isCoatom {K : Subgroup G} [K.Normal]
    (hK : IsCoatom K) : Nontrivial (G ⧸ K) := by
  obtain ⟨x, _hxtop, hxK⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hK.1)
  exact ⟨⟨QuotientGroup.mk x, 1, fun h => hxK ((QuotientGroup.eq_one_iff x).mp h)⟩⟩

/-- By the correspondence theorem, the subgroup lattice of the quotient by a coatom
`K` is `{⊥, ⊤}` — i.e. a simple order. -/
theorem isSimpleOrder_quotient_of_isCoatom {K : Subgroup G} [K.Normal]
    (hK : IsCoatom K) : IsSimpleOrder (Subgroup (G ⧸ K)) := by
  haveI : Nontrivial (G ⧸ K) := nontrivial_quotient_of_isCoatom hK
  haveI : Nontrivial (Subgroup (G ⧸ K)) := Subgroup.nontrivial_iff.mpr inferInstance
  have hcomapinj : Function.Injective (comap (QuotientGroup.mk' K)) :=
    comap_injective (QuotientGroup.mk'_surjective K)
  refine ⟨fun a => ?_⟩
  have hK_le : K ≤ comap (QuotientGroup.mk' K) a := by
    have hkc := (QuotientGroup.mk' K).ker_le_comap a
    rwa [QuotientGroup.ker_mk'] at hkc
  rcases eq_or_lt_of_le hK_le with h | h
  · left; apply hcomapinj
    change comap (QuotientGroup.mk' K) a = (QuotientGroup.mk' K).ker
    rw [QuotientGroup.ker_mk']; exact h.symm
  · right; apply hcomapinj
    rw [comap_top]; exact hK.2 _ h

/-- **A coatom of a finite `p`-group has index `p`.** The quotient is a nontrivial
`p`-group whose subgroup lattice is simple, hence cyclic of order `p`. -/
theorem card_quotient_eq_prime [Finite G] {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G)
    {K : Subgroup G} [K.Normal] (hK : IsCoatom K) :
    Nat.card (G ⧸ K) = p := by
  haveI : Nontrivial (G ⧸ K) := nontrivial_quotient_of_isCoatom hK
  have hsimple : IsSimpleOrder (Subgroup (G ⧸ K)) := isSimpleOrder_quotient_of_isCoatom hK
  have hQ : IsPGroup p (G ⧸ K) := hG.to_quotient K
  obtain ⟨m, hm0, hm⟩ := hQ.nontrivial_iff_card.mp inferInstance
  have hdvd : p ∣ Nat.card (G ⧸ K) := by
    rw [hm]; exact dvd_pow_self p hm0.ne'
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hgne : g ≠ 1 := by
    intro hg1
    rw [hg1] at hg
    exact (Fact.out (p := p.Prime)).ne_one (by rw [← hg, orderOf_one])
  have htop : Subgroup.zpowers g = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left (Subgroup.zpowers_ne_bot.mpr hgne)
  have hcard : Nat.card (G ⧸ K) = Nat.card (Subgroup.zpowers g) := by
    rw [htop, Subgroup.card_top]
  rw [hcard, Nat.card_zpowers, hg]

end PGroupMaximal

/-! ### Specialisation to `Coordinate 1` -/

section Coordinate1Maximal

open Subgroup

set_option maxRecDepth 100000

/-- `5` is prime — the working prime for the order-`5^5` group. -/
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- **Every subgroup of `Coordinate 1` is a `5`-group.** Its order divides
`|Coordinate 1| = 5^5`, hence is a power of `5`. -/
theorem isPGroup_subgroup (H : Subgroup (Coordinate 1)) : IsPGroup 5 (H : Type _) := by
  have hdvd : Nat.card H ∣ Nat.card (Coordinate 1) := Subgroup.card_subgroup_dvd_card H
  have hcard1 : Nat.card (Coordinate 1) = 3125 := by rw [Nat.card_eq_fintype_card]; rfl
  rw [hcard1, show (3125 : ℕ) = 5 ^ 5 from by norm_num] at hdvd
  obtain ⟨k, _hk, hkeq⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp hdvd
  exact IsPGroup.of_card hkeq

/-- **A maximal proper subgroup, viewed inside `H`, is a coatom.** For `M < H` with
nothing strictly between `M` and `H`, the relative subgroup `M.subgroupOf H` is a
coatom of `Subgroup ↥H`. -/
theorem isCoatom_subgroupOf {H M : Subgroup (Coordinate 1)} (hMH : M < H)
    (hmax : ∀ N, M < N → N < H → False) : IsCoatom (M.subgroupOf H) := by
  have hinj : Function.Injective (Subgroup.map H.subtype) :=
    Subgroup.map_injective H.subtype_injective
  have hMeq : (M.subgroupOf H).map H.subtype = M := Subgroup.map_subgroupOf_eq_of_le hMH.le
  constructor
  · rw [ne_eq, Subgroup.subgroupOf_eq_top]
    exact fun hle => hMH.ne (le_antisymm hMH.le hle)
  · intro b hb
    have hMle : M ≤ b.map H.subtype :=
      hMeq ▸ (Subgroup.map_subtype_le_map_subtype).mpr hb.le
    have hMne : M ≠ b.map H.subtype := by
      intro he
      exact (ne_of_lt hb) (hinj (by rw [hMeq]; exact he))
    have hMlt : M < b.map H.subtype := lt_of_le_of_ne hMle hMne
    have htop : (⊤ : Subgroup (H : Type _)).map H.subtype = H := by
      rw [← MonoidHom.range_eq_map]; exact H.range_subtype
    rcases eq_or_lt_of_le (Subgroup.map_subtype_le b) with heq | hlt
    · apply hinj; rw [htop]; exact heq
    · exact (hmax _ hMlt hlt).elim

/-- **Normality.** A maximal proper subgroup `M < H` of a subgroup of
`Coordinate 1` is normal in `H`. -/
theorem normal_of_maximal {H M : Subgroup (Coordinate 1)} (hMH : M < H)
    (hmax : ∀ N, M < N → N < H → False) : (M.subgroupOf H).Normal :=
  normal_of_isCoatom_pgroup (isPGroup_subgroup H) (isCoatom_subgroupOf hMH hmax)

/-- **Index `5`.** A maximal proper subgroup `M < H` has relative index
`[H : M] = 5`. -/
theorem relIndex_eq_five_of_maximal {H M : Subgroup (Coordinate 1)} (hMH : M < H)
    (hmax : ∀ N, M < N → N < H → False) : M.relIndex H = 5 := by
  haveI : (M.subgroupOf H).Normal := normal_of_maximal hMH hmax
  change (M.subgroupOf H).index = 5
  rw [Subgroup.index_eq_card]
  exact card_quotient_eq_prime (isPGroup_subgroup H) (isCoatom_subgroupOf hMH hmax)

/-- **Frattini containment.** A maximal proper subgroup `M < H` contains
the Frattini subgroup of `H` (the intersection of `H`'s maximal subgroups). -/
theorem frattini_le_of_maximal {H M : Subgroup (Coordinate 1)} (hMH : M < H)
    (hmax : ∀ N, M < N → N < H → False) :
    frattini (H : Type _) ≤ M.subgroupOf H :=
  frattini_le_coatom (isCoatom_subgroupOf hMH hmax)

/-! ### Reduction of `MaximalsClosed` to normal index-`5` completeness -/

/-- **The sharpened obligation.** Closure of the inventory under passage to
*normal index-`5`* subgroups. Every maximal proper subgroup is of this form, so
this is a strictly weaker hypothesis than `MaximalsClosed`: it only ranges
over the (normal, index-`5`) subgroups — the preimages of the hyperplanes of each
Frattini quotient. -/
def NormalIndexFiveClosed : Prop :=
  ∀ H : Subgroup (Coordinate 1), InInv H → ∀ M, M < H →
    (M.subgroupOf H).Normal → M.relIndex H = 5 → InInv M

/-- `NormalIndexFiveClosed` implies `MaximalsClosed`: every maximal proper subgroup
is normal of index `5`, so it is covered. -/
theorem maximalsClosed_of_normalIndexFiveClosed (h : NormalIndexFiveClosed) :
    MaximalsClosed := fun H hH M hMH hmax =>
  h H hH M hMH (normal_of_maximal hMH hmax) (relIndex_eq_five_of_maximal hMH hmax)

/-- **Completeness, conditional on the sharpened `NormalIndexFiveClosed`.** -/
theorem allSubs_complete_of_normalIndexFiveClosed (h : NormalIndexFiveClosed) :
    ∀ K : Subgroup (Coordinate 1), ∃ c ∈ allSubs, c.toSubgroup = K :=
  allSubs_complete_of_maximalsClosed (maximalsClosed_of_normalIndexFiveClosed h)

end Coordinate1Maximal

end LeanDring.P5Presentation
