/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Even.Shadow

/-!
# Slice recognition IS shadow recognition: the open question in fibre form

**EVEN-ORDER LAYER.** No `sorry`, three standard axioms.

The capstone's slice condition quantifies over ghost *vectors*. This
file proves it is equivalent to a purely combinatorial condition on the
*point map*: the identification must descend to Burnside-shadow classes,
in both directions.

* `burnsideShadow_eq_iff` — two integer points have the same shadow iff
 they agree on the Burnside copy `η(B)`. Since every species
  `(K, λ)` restricts to `η(B)` as `mark_K` — independently of the
  decoration `λ` (`species_comp_eta`) — the shadow classes are exactly
 the **fibres** of the shadow decomposition (F0), with no species
  classification needed to define them.
* `sliceCondition_iff_shadowDescends` — **the main theorem**: for finite
  2-groups, a lattice identification satisfies the capstone's slice
  condition iff it and its inverse descend to shadow classes:
 `P ∘ e ∘ P' = P ∘ e` and `P' ∘ e⁻¹ ∘ P = P' ∘ e⁻¹`. The slice
  condition — an analytic-looking statement about symmetric lattice
  vectors — is exactly **fibre-respecting-ness (TIR) of the species
  matching**, formally.
* `ShadowRecognition` / `twoGroupDtoB_of_shadowRecognition` — the final
  reduction restated in fibre form: the 2-group `D ⇒ B` target follows
  from every D-ring isomorphism admitting a shadow-descending lattice
 identification. This is the An5″/TIR orbit question verbatim, and it
  is now a statement about finite dynamics: an idempotent `P` on a
  finite point set on each side, and a bijection asked to intertwine
  the two idempotents after a gauge.
-/

namespace LeanDring

namespace Even

open MonRing

universe u v

variable {G : Type u} [Group G]

@[simp] theorem burnsideShadow_apply_eta (φ : IntPoint (DRing G))
    (b : BurnsideRing G) :
    burnsideShadow φ (eta b) = φ (eta b) := by
  change φ (eta (MonRing.forget (eta b))) = φ (eta b)
  rw [forget_eta]

/-- Two integer points have the same Burnside shadow iff they agree on
the Burnside copy `η(B)` — shadow classes are the fibres. -/
theorem burnsideShadow_eq_iff {φ₁ φ₂ : IntPoint (DRing G)} :
    burnsideShadow φ₁ = burnsideShadow φ₂ ↔
      ∀ b : BurnsideRing G, φ₁ (eta b) = φ₂ (eta b) := by
  constructor
  · intro h b
    have h1 := DFunLike.congr_fun h (eta b)
    simpa using h1
  · intro h
    ext x
    change φ₁ (eta (MonRing.forget x)) = φ₂ (eta (MonRing.forget x))
    exact h _

/-- Burnside ghost vectors are ψ²-symmetric. -/
theorem ghost_eta_fixed (b : BurnsideRing G) :
    ghost (DRing G) (eta b) ∘ pointPush (psi 2 : DRing G →+* DRing G) =
      ghost (DRing G) (eta b) :=
  (mem_fixedSubring.mp (ghost_mem_fixedSubring (psi_eta 2 b))).2

/-- Every ψ²-symmetric ghost vector is a Burnside ghost vector
(`marksOntoSlice` surjectivity, unpackaged). -/
theorem exists_ghost_eta_of_fixed {m : ℕ} (hG : ∀ g : G, g ^ 2 ^ m = 1)
    {v : IntPoint (DRing G) → ℤ} (hrange : v ∈ (ghost (DRing G)).range)
    (hsym : v ∘ pointPush (psi 2 : DRing G →+* DRing G) = v) :
    ∃ b : BurnsideRing G, ghost (DRing G) (eta b) = v := by
  obtain ⟨b, hb⟩ := burnsideToSlice_surjective hG
    ⟨v, mem_fixedSubring.mpr ⟨hrange, hsym⟩⟩
  exact ⟨b, congrArg Subtype.val hb⟩

/-- **Slice recognition is shadow recognition (TIR), formally**: a
lattice identification between the D-rings of two finite 2-groups
satisfies the capstone's slice condition iff it and its inverse descend
to Burnside-shadow classes. The open even-order hypothesis is exactly
fibre-respecting-ness of the species matching. -/
theorem sliceCondition_iff_shadowDescends
    {G : Type u} {H : Type v} [Group G] [Group H]
    {mG : ℕ} (hG : ∀ g : G, g ^ 2 ^ mG = 1)
    {mH : ℕ} (hH : ∀ g : H, g ^ 2 ^ mH = 1)
    (e : IntPoint (DRing H) ≃ IntPoint (DRing G))
    (he : IdentifiesLattices e) :
    (∀ v : IntPoint (DRing G) → ℤ, v ∈ (ghost (DRing G)).range →
      (v ∘ pointPush (psi 2 : DRing G →+* DRing G) = v ↔
        (v ∘ ⇑e) ∘ pointPush (psi 2 : DRing H →+* DRing H) = v ∘ ⇑e)) ↔
      ((∀ φ' : IntPoint (DRing H),
          burnsideShadow (e (burnsideShadow φ')) = burnsideShadow (e φ')) ∧
        ∀ φ : IntPoint (DRing G),
          burnsideShadow (e.symm (burnsideShadow φ)) =
            burnsideShadow (e.symm φ)) := by
  constructor
  · intro hslice
    constructor
    · intro φ'
      rw [burnsideShadow_eq_iff]
      intro b
      have hv : ghost (DRing G) (eta b) ∈ (ghost (DRing G)).range :=
        ⟨eta b, rfl⟩
      have h2 := (hslice _ hv).mp (ghost_eta_fixed b)
      have h3 := (sliceFix_iff_comp_shadow hH _).mp h2
      exact congrFun h3 φ'
    · intro φ
      rw [burnsideShadow_eq_iff]
      intro b'
      have hwrange : ghost (DRing H) (eta b') ∈ (ghost (DRing H)).range :=
        ⟨eta b', rfl⟩
      have hvcomp : (ghost (DRing H) (eta b') ∘ ⇑e.symm) ∘ ⇑e =
          ghost (DRing H) (eta b') := by
        funext p
        simp
      have hvrange : ghost (DRing H) (eta b') ∘ ⇑e.symm ∈
          (ghost (DRing G)).range := by
        refine mem_ghostLattice_iff_mem_range.mp
          ((he (ghost (DRing H) (eta b') ∘ ⇑e.symm)).mp ?_)
        rw [hvcomp]
        exact mem_ghostLattice_iff_mem_range.mpr hwrange
      have hsymm : (ghost (DRing H) (eta b') ∘ ⇑e.symm) ∘
          pointPush (psi 2 : DRing G →+* DRing G) =
            ghost (DRing H) (eta b') ∘ ⇑e.symm := by
        refine (hslice _ hvrange).mpr ?_
        rw [hvcomp]
        exact ghost_eta_fixed b'
      have h3 := (sliceFix_iff_comp_shadow hG _).mp hsymm
      exact congrFun h3 φ
  · rintro ⟨hdesc, hdesc'⟩ v hvrange
    constructor
    · intro hsym
      obtain ⟨b, rfl⟩ := exists_ghost_eta_of_fixed hG hvrange hsym
      refine (sliceFix_iff_comp_shadow hH _).mpr ?_
      funext φ'
      exact burnsideShadow_eq_iff.mp (hdesc φ') b
    · intro hsym'
      have hwrange : v ∘ ⇑e ∈ (ghost (DRing H)).range :=
        mem_ghostLattice_iff_mem_range.mp
          ((he v).mpr (mem_ghostLattice_iff_mem_range.mpr hvrange))
      obtain ⟨b', hb'⟩ := exists_ghost_eta_of_fixed hH hwrange hsym'
      have hveq : v = ghost (DRing H) (eta b') ∘ ⇑e.symm := by
        rw [hb']
        funext p
        simp
      rw [hveq]
      refine (sliceFix_iff_comp_shadow hG _).mpr ?_
      funext φ
      exact burnsideShadow_eq_iff.mp (hdesc' φ) b'

/-- **The residual open question, fibre form**: every D-ring isomorphism
of finite 2-groups admits a shadow-descending lattice identification.
Equivalent to `SliceRecognition` by the main theorem; this is the
An5″/TIR orbit question as a statement about finite idempotent
dynamics. -/
def ShadowRecognition : Prop :=
  ∀ (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H],
    IsPGroup 2 G → IsPGroup 2 H →
    ∀ _Φ : DRing G ≃+* DRing H,
      ∃ e : IntPoint (DRing H) ≃ IntPoint (DRing G),
        IdentifiesLattices e ∧
        (∀ φ' : IntPoint (DRing H),
          burnsideShadow (e (burnsideShadow φ')) = burnsideShadow (e φ')) ∧
        ∀ φ : IntPoint (DRing G),
          burnsideShadow (e.symm (burnsideShadow φ)) =
            burnsideShadow (e.symm φ)

/-- **The final reduction, fibre form**: shadow recognition implies the
open 2-group target. -/
theorem twoGroupDtoB_of_shadowRecognition (hrec : ShadowRecognition.{u}) :
    TwoGroupDtoB.{u} := by
  intro G H _ _ _ _ hG hH hD
  obtain ⟨Φ⟩ := hD
  obtain ⟨e, he, hd1, hd2⟩ := hrec G H hG hH Φ
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
