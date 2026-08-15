/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SubgroupInventory.Twin2.AllSubgroupsProofs
import LeanDring.P5.Certificate.SubgroupInventory.Twin1.Complete

/-!
# Completeness scaffold for the q=2 (SmallGroup(3125,69)) inventory (twin q=2)

The q=2 twin of `LeanDring/P5/Certificate/SubgroupInventory/Twin1/Complete.lean`. The generic
`p`-group lemmas
(`normal_of_isCoatom_pgroup`, `card_quotient_eq_prime`, …) are reused verbatim from
`LeanDring/P5/Certificate/SubgroupInventory/Twin1/Complete.lean` (they are stated for an abstract
finite group). This file re-instantiates
the `Coordinate 2`-specific layer: `InInv`, `Covering`, `key`, `MaximalsClosed`,
`NormalIndexFiveClosed`, and Step 1 (the p-group structure of a maximal subgroup).
-/

namespace LeanDring.P5Presentation

namespace Q2

open Cgs Subgroup

/-- `H` is presented by some member of the certified inventory `allSubs`. -/
def InInv (H : Subgroup (Coordinate 2)) : Prop := ∃ c ∈ allSubs, c.toSubgroup = H

theorem top_InInv : InInv (⊤ : Subgroup (Coordinate 2)) := top_mem_allSubs
theorem bot_InInv : InInv (⊥ : Subgroup (Coordinate 2)) := bot_mem_allSubs

/-! ## Finiteness -/

theorem card_lt {M H : Subgroup (Coordinate 2)} (h : M < H) :
    Nat.card M < Nat.card H := by
  have hss : (M : Set (Coordinate 2)) ⊂ (H : Set (Coordinate 2)) :=
    SetLike.coe_ssubset_coe.mpr h
  have hlt := Set.Finite.card_lt_card (Set.toFinite (H : Set (Coordinate 2))) hss
  simpa only [SetLike.coe_sort_coe] using hlt

/-! ## The finite-lattice covering step -/

theorem exists_maxProper {K H : Subgroup (Coordinate 2)} (hKH : K < H) :
    ∃ M, K ≤ M ∧ M < H ∧ ∀ N, M < N → N < H → False := by
  set s : Set (Subgroup (Coordinate 2)) := {N | K ≤ N ∧ N < H} with hs
  have hfin : s.Finite := Set.toFinite s
  obtain ⟨M, hMmax⟩ := hfin.exists_maximal ⟨K, ⟨le_refl K, hKH⟩⟩
  obtain ⟨hKM, hMH⟩ := hMmax.1
  refine ⟨M, hKM, hMH, ?_⟩
  intro N hMN hNH
  have hNmem : N ∈ s := ⟨le_trans hKM (le_of_lt hMN), hNH⟩
  have hNM : N ≤ M := hMmax.2 hNmem (le_of_lt hMN)
  exact absurd hNM (not_le_of_gt hMN)

/-! ## The covering hypothesis and the completeness induction -/

def Covering : Prop :=
  ∀ H : Subgroup (Coordinate 2), InInv H → ∀ K, K < H → ∃ M, InInv M ∧ K ≤ M ∧ M < H

theorem key (cov : Covering) :
    ∀ n, ∀ H : Subgroup (Coordinate 2), Nat.card H = n → InInv H →
      ∀ K, K ≤ H → InInv K := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro H hn hH K hKH
    rcases eq_or_lt_of_le hKH with rfl | hlt
    · exact hH
    · obtain ⟨M, hM, hKM, hMH⟩ := cov H hH K hlt
      exact ih (Nat.card M) (hn ▸ card_lt hMH) M rfl hM K hKM

theorem allSubs_complete_of_covering (cov : Covering) :
    ∀ K : Subgroup (Coordinate 2), ∃ c ∈ allSubs, c.toSubgroup = K := fun K =>
  key cov (Nat.card (⊤ : Subgroup (Coordinate 2))) ⊤ rfl top_InInv K le_top

/-! ## Reducing `Covering` to the single Frattini-completeness fact -/

def MaximalsClosed : Prop :=
  ∀ H : Subgroup (Coordinate 2), InInv H → ∀ M, M < H →
    (∀ N, M < N → N < H → False) → InInv M

theorem covering_of_maximalsClosed (mc : MaximalsClosed) : Covering := by
  intro H hH K hKH
  obtain ⟨M, hKM, hMH, hMmax⟩ := exists_maxProper hKH
  exact ⟨M, mc H hH M hMH hMmax, hKM, hMH⟩

theorem allSubs_complete_of_maximalsClosed (mc : MaximalsClosed) :
    ∀ K : Subgroup (Coordinate 2), ∃ c ∈ allSubs, c.toSubgroup = K :=
  allSubs_complete_of_covering (covering_of_maximalsClosed mc)

/-! ## Step 1 — the p-group structure of a maximal subgroup (specialised to `Coordinate 2`) -/

section Coordinate2Maximal

set_option maxRecDepth 100000

/-- **Every subgroup of `Coordinate 2` is a `5`-group.** -/
theorem isPGroup_subgroup (H : Subgroup (Coordinate 2)) : IsPGroup 5 (H : Type _) := by
  have hdvd : Nat.card H ∣ Nat.card (Coordinate 2) := Subgroup.card_subgroup_dvd_card H
  have hcard1 : Nat.card (Coordinate 2) = 3125 := by rw [Nat.card_eq_fintype_card]; rfl
  rw [hcard1, show (3125 : ℕ) = 5 ^ 5 from by norm_num] at hdvd
  obtain ⟨k, _hk, hkeq⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp hdvd
  exact IsPGroup.of_card hkeq

theorem isCoatom_subgroupOf {H M : Subgroup (Coordinate 2)} (hMH : M < H)
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

theorem normal_of_maximal {H M : Subgroup (Coordinate 2)} (hMH : M < H)
    (hmax : ∀ N, M < N → N < H → False) : (M.subgroupOf H).Normal :=
  normal_of_isCoatom_pgroup (isPGroup_subgroup H) (isCoatom_subgroupOf hMH hmax)

theorem relIndex_eq_five_of_maximal {H M : Subgroup (Coordinate 2)} (hMH : M < H)
    (hmax : ∀ N, M < N → N < H → False) : M.relIndex H = 5 := by
  haveI : (M.subgroupOf H).Normal := normal_of_maximal hMH hmax
  change (M.subgroupOf H).index = 5
  rw [Subgroup.index_eq_card]
  exact card_quotient_eq_prime (isPGroup_subgroup H) (isCoatom_subgroupOf hMH hmax)

theorem frattini_le_of_maximal {H M : Subgroup (Coordinate 2)} (hMH : M < H)
    (hmax : ∀ N, M < N → N < H → False) :
    _root_.frattini (H : Type _) ≤ M.subgroupOf H :=
  frattini_le_coatom (isCoatom_subgroupOf hMH hmax)

/-! ### Reduction of `MaximalsClosed` to normal index-`5` completeness -/

def NormalIndexFiveClosed : Prop :=
  ∀ H : Subgroup (Coordinate 2), InInv H → ∀ M, M < H →
    (M.subgroupOf H).Normal → M.relIndex H = 5 → InInv M

theorem maximalsClosed_of_normalIndexFiveClosed (h : NormalIndexFiveClosed) :
    MaximalsClosed := fun H hH M hMH hmax =>
  h H hH M hMH (normal_of_maximal hMH hmax) (relIndex_eq_five_of_maximal hMH hmax)

theorem allSubs_complete_of_normalIndexFiveClosed (h : NormalIndexFiveClosed) :
    ∀ K : Subgroup (Coordinate 2), ∃ c ∈ allSubs, c.toSubgroup = K :=
  allSubs_complete_of_maximalsClosed (maximalsClosed_of_normalIndexFiveClosed h)

end Coordinate2Maximal

end Q2

end LeanDring.P5Presentation
