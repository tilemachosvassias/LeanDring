/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Even.Descent

/-!
# The profile contract: fibre-separating transported invariants force
# recognition

**EVEN-ORDER LAYER.** No `sorry`, three standard axioms.

This file is the formal interface for the class-level (extraspecial)
programme.  To prove shadow recognition for a class, it suffices to
construct a **profile**: an invariant of integer points that

1. every lattice identification transports (`htrans` — canonicity, the
   L1 mechanism), and
2. separates points exactly up to fibres (`hlevel` — the An5″
   mathematics: the web/valuation data determines the fibre partition).

* `mem_linkSubgroup_iff_lattice` / `linkSubgroup_of_identifies` —
  **L1 strengthened**: the linkage subgroup is computed by the ghost
  lattice alone, hence preserved by *every* lattice identification —
  not only those induced by ring isomorphisms.  This discharges the
  transport half (`htrans`) for every profile built from linkage data
  (pairwise linkage, arity sums, web valuations): the extraspecial work
  only owes the separation half.
* `shadowDescends_of_profile` — **the contract**: a fibre-separating
  transported profile on both sides forces the descent pair for the
  identification.
* `burnsideNonempty_of_profile` — the payoff form: for finite 2-groups,
  profile ⟹ `B(G) ≅ B(H)`.  The extraspecial target is now literally:
  build the web profile and prove it separates fibres.
-/

namespace LeanDring

namespace Even

open MonRing

universe u v

/-- Linkage is a lattice invariant: the linkage subgroup of a pair of
points is computed by the ghost lattice alone. -/
theorem mem_linkSubgroup_iff_lattice {D : Type*} [CommRing D]
    {φ ψ : IntPoint D} {n : ℤ} :
    n ∈ linkSubgroup φ ψ ↔ ∃ v ∈ (ghost D).range, v φ - v ψ = n := by
  rw [mem_linkSubgroup]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨ghost D x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨v, ⟨x, rfl⟩, h⟩
    exact ⟨x, h⟩

/-- **L1, strengthened to arbitrary lattice identifications**: every
lattice identification — whether or not it comes from a ring
isomorphism — preserves all pairwise linkage subgroups.  Profiles built
from linkage data are therefore automatically transported. -/
theorem linkSubgroup_of_identifies {D : Type*} [CommRing D]
    {D' : Type*} [CommRing D'] {e : IntPoint D' ≃ IntPoint D}
    (he : IdentifiesLattices e) (φ' ψ' : IntPoint D') :
    linkSubgroup (e φ') (e ψ') = linkSubgroup φ' ψ' := by
  ext n
  rw [mem_linkSubgroup_iff_lattice, mem_linkSubgroup_iff_lattice]
  constructor
  · rintro ⟨v, hv, h⟩
    refine ⟨v ∘ ⇑e, ?_, h⟩
    exact mem_ghostLattice_iff_mem_range.mp
      ((he v).mpr (mem_ghostLattice_iff_mem_range.mpr hv))
  · rintro ⟨w, hw, h⟩
    have hcomp : (w ∘ ⇑e.symm) ∘ ⇑e = w := by
      funext p
      simp
    refine ⟨w ∘ ⇑e.symm, ?_, ?_⟩
    · refine mem_ghostLattice_iff_mem_range.mp ((he _).mp ?_)
      rw [hcomp]
      exact mem_ghostLattice_iff_mem_range.mpr hw
    · show (w ∘ ⇑e.symm) (e φ') - (w ∘ ⇑e.symm) (e ψ') = n
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
      exact h

/-- **The profile contract**: an invariant of integer points that the
identification transports (`htrans`) and whose level sets are exactly
the fibres on both sides (`hlevel`, `hlevel'`) forces the descent pair.
To prove class recognition, construct such a profile: transport is free
for linkage-built profiles (`linkSubgroup_of_identifies`); separation
is the class-specific mathematics (the webs). -/
theorem shadowDescends_of_profile {G : Type u} [Group G]
    {H : Type v} [Group H]
    (e : IntPoint (DRing H) ≃ IntPoint (DRing G))
    {Ω : Type*} (I : IntPoint (DRing G) → Ω) (I' : IntPoint (DRing H) → Ω)
    (htrans : ∀ φ' : IntPoint (DRing H), I (e φ') = I' φ')
    (hlevel : ∀ φ ψ : IntPoint (DRing G),
      burnsideShadow φ = burnsideShadow ψ ↔ I φ = I ψ)
    (hlevel' : ∀ φ' ψ' : IntPoint (DRing H),
      burnsideShadow φ' = burnsideShadow ψ' ↔ I' φ' = I' ψ') :
    (∀ φ' : IntPoint (DRing H),
        burnsideShadow (e (burnsideShadow φ')) = burnsideShadow (e φ')) ∧
      ∀ φ : IntPoint (DRing G),
        burnsideShadow (e.symm (burnsideShadow φ)) =
          burnsideShadow (e.symm φ) := by
  have hIsymm : ∀ χ : IntPoint (DRing G), I' (e.symm χ) = I χ := by
    intro χ
    rw [← htrans (e.symm χ), Equiv.apply_symm_apply]
  constructor
  · refine (shadowDescends_iff_congr ⇑e).mpr ?_
    intro φ' ψ' h
    rw [hlevel, htrans, htrans, ← hlevel']
    exact h
  · refine (shadowDescends_iff_congr ⇑e.symm).mpr ?_
    intro φ ψ h
    rw [hlevel', hIsymm, hIsymm, ← hlevel]
    exact h

/-- **The payoff form of the contract**: for finite 2-groups, a
fibre-separating transported profile across a lattice identification
yields `B(G) ≅ B(H)`.  The extraspecial formal target is exactly to
supply `I, I'` (from the FW-webs) with `hlevel` (An5″). -/
theorem burnsideNonempty_of_profile {G : Type u} {H : Type v}
    [Group G] [Group H] [Finite G] [Finite H]
    (hG : IsPGroup 2 G) (hH : IsPGroup 2 H)
    (e : IntPoint (DRing H) ≃ IntPoint (DRing G))
    (he : IdentifiesLattices e)
    {Ω : Type*} (I : IntPoint (DRing G) → Ω) (I' : IntPoint (DRing H) → Ω)
    (htrans : ∀ φ' : IntPoint (DRing H), I (e φ') = I' φ')
    (hlevel : ∀ φ ψ : IntPoint (DRing G),
      burnsideShadow φ = burnsideShadow ψ ↔ I φ = I ψ)
    (hlevel' : ∀ φ' ψ' : IntPoint (DRing H),
      burnsideShadow φ' = burnsideShadow ψ' ↔ I' φ' = I' ψ') :
    Nonempty (BurnsideRing G ≃+* BurnsideRing H) := by
  obtain ⟨hd1, hd2⟩ :=
    shadowDescends_of_profile e I I' htrans hlevel hlevel'
  obtain ⟨nG, hnG⟩ := IsPGroup.iff_card.mp hG
  obtain ⟨nH, hnH⟩ := IsPGroup.iff_card.mp hH
  have hexpG : ∀ g : G, g ^ 2 ^ nG = 1 := fun g => by
    rw [← hnG]
    exact pow_card_eq_one'
  have hexpH : ∀ g : H, g ^ 2 ^ nH = 1 := fun g => by
    rw [← hnH]
    exact pow_card_eq_one'
  exact burnsideNonempty_of_exists_sliceIdentification hG hH e he
    ((sliceCondition_iff_shadowDescends hexpG hexpH e he).mpr ⟨hd1, hd2⟩)

end Even

end LeanDring
