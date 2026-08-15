/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.FreeBasis

/-!
# The certificate bridge: species-compatible bijections give `D(G) ≅ D(G′)`

**The mathematical core of the species-table certificate**: if a bijection `σ`
of basis classes is *species-compatible* — every species column of `G′` pulls
back along `σ` to a species column of `G` — then the `ℤ`-linear extension of
`σ` along the two `[K, λ]`-bases is automatically a **ring isomorphism**
`D(G) ≃+* D(G′)`.

Multiplicativity costs nothing extra: both `F(xy)` and `F(x)F(y)` have the
same species table (species are ring homomorphisms and pull back along `F`
by compatibility), and species tables are complete (`species_injective`).

This is the theorem that turns a species-table matching for
`SmallGroup(3125,68)` and `SmallGroup(3125,69)` into the statement
`D(G₁) ≅ D(G₂)`; what remains for the 5⁵ certificate is finite data checking.
-/

namespace LeanDring

namespace DRing

open MonGSet

universe u

variable {G G' : Type u} [Group G] [Group G'] [Fintype G] [Fintype G']

@[simp] theorem basisOfCharPairClass_apply (c : CharPairClass G ℂˣ) :
    basisOfCharPairClass c = classElt c :=
  Module.Basis.mk_apply _ _ _

section Bridge

variable (σ : CharPairClass G ℂˣ ≃ CharPairClass G' ℂˣ)

/-- The `ℤ`-linear extension of a class bijection along the two bases. -/
noncomputable def bridgeLin : DRing G ≃ₗ[ℤ] DRing G' :=
  (basisOfCharPairClass (G := G)).equiv (basisOfCharPairClass (G := G')) σ

@[simp] theorem bridgeLin_classElt (c : CharPairClass G ℂˣ) :
    bridgeLin σ (classElt c) = classElt (σ c) := by
  rw [← basisOfCharPairClass_apply, bridgeLin,
    Module.Basis.equiv_apply, basisOfCharPairClass_apply]

variable (hcompat : ∀ (H' : Subgroup G') (h' : H'), ∃ (H : Subgroup G) (h : H),
    ∀ c : CharPairClass G ℂˣ, species H' h' (classElt (σ c)) = species H h (classElt c))

include hcompat

/-- Species pull back along the bridge: every species column of `G′`
becomes a species column of `G` on all of `D(G)`. -/
theorem bridge_species (H' : Subgroup G') (h' : H') :
    ∃ (H : Subgroup G) (h : H), ∀ x : DRing G,
      species H' h' (bridgeLin σ x) = species H h x := by
  obtain ⟨H, h, hc⟩ := hcompat H' h'
  refine ⟨H, h, ?_⟩
  have heq : (AddMonoidHom.toIntLinearMap (species H' h' : DRing G' →+ ℂ)).comp
      (bridgeLin σ).toLinearMap =
      AddMonoidHom.toIntLinearMap (species H h : DRing G →+ ℂ) := by
    refine (basisOfCharPairClass (G := G)).ext fun c => ?_
    change species H' h' (bridgeLin σ (basisOfCharPairClass c)) =
      species H h (basisOfCharPairClass c)
    rw [basisOfCharPairClass_apply, bridgeLin_classElt]
    exact hc c
  intro x
  exact LinearMap.congr_fun heq x

/-- Multiplicativity on basis pairs, by comparing species tables. -/
theorem bridge_mul_basis (c₁ c₂ : CharPairClass G ℂˣ) :
    bridgeLin σ (classElt c₁ * classElt c₂) =
      bridgeLin σ (classElt c₁) * bridgeLin σ (classElt c₂) := by
  apply species_injective
  funext H' h'
  obtain ⟨H, h, hlin⟩ := bridge_species σ hcompat H' h'
  change species H' h' (bridgeLin σ (classElt c₁ * classElt c₂)) =
    species H' h' (bridgeLin σ (classElt c₁) * bridgeLin σ (classElt c₂))
  calc species H' h' (bridgeLin σ (classElt c₁ * classElt c₂))
      = species H h (classElt c₁ * classElt c₂) := hlin _
    _ = species H h (classElt c₁) * species H h (classElt c₂) := map_mul _ _ _
    _ = species H' h' (bridgeLin σ (classElt c₁)) *
        species H' h' (bridgeLin σ (classElt c₂)) := by rw [hlin, hlin]
    _ = species H' h' (bridgeLin σ (classElt c₁) * bridgeLin σ (classElt c₂)) :=
        (map_mul _ _ _).symm

/-- Multiplicativity everywhere, by two rounds of basis extension. -/
theorem bridge_mul (x y : DRing G) :
    bridgeLin σ (x * y) = bridgeLin σ x * bridgeLin σ y := by
  -- first extend in the left argument, against a basis right factor
  have hleft : ∀ (c₂ : CharPairClass G ℂˣ) (x : DRing G),
      bridgeLin σ (x * classElt c₂) = bridgeLin σ x * bridgeLin σ (classElt c₂) := by
    intro c₂
    have heq : (bridgeLin σ).toLinearMap.comp (LinearMap.mulRight ℤ (classElt c₂)) =
        (LinearMap.mulRight ℤ (bridgeLin σ (classElt c₂))).comp
          (bridgeLin σ).toLinearMap := by
      refine (basisOfCharPairClass (G := G)).ext fun c₁ => ?_
      change bridgeLin σ (basisOfCharPairClass c₁ * classElt c₂) =
        bridgeLin σ (basisOfCharPairClass c₁) * bridgeLin σ (classElt c₂)
      rw [basisOfCharPairClass_apply]
      exact bridge_mul_basis σ hcompat c₁ c₂
    intro x
    exact LinearMap.congr_fun heq x
  -- then extend in the right argument
  have heq : (bridgeLin σ).toLinearMap.comp (LinearMap.mulLeft ℤ x) =
      (LinearMap.mulLeft ℤ (bridgeLin σ x)).comp (bridgeLin σ).toLinearMap := by
    refine (basisOfCharPairClass (G := G)).ext fun c₂ => ?_
    change bridgeLin σ (x * basisOfCharPairClass c₂) =
      bridgeLin σ x * bridgeLin σ (basisOfCharPairClass c₂)
    rw [basisOfCharPairClass_apply]
    exact hleft c₂ x
  exact LinearMap.congr_fun heq y

/-- **The certificate bridge theorem**: a species-compatible class
bijection induces a ring isomorphism `D(G) ≃+* D(G′)`. -/
noncomputable def equivOfSpeciesMatch : DRing G ≃+* DRing G' :=
  { (bridgeLin σ).toEquiv with
    map_mul' := bridge_mul σ hcompat
    map_add' := (bridgeLin σ).map_add }

/-- Certificate-facing form: species-matched groups have isomorphic
D-rings. -/
theorem nonempty_dringEquiv_of_speciesMatch :
    Nonempty (DRing G ≃+* DRing G') :=
  ⟨equivOfSpeciesMatch σ hcompat⟩

end Bridge

end DRing

end LeanDring
