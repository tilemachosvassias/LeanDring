/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.Species

/-!
# Species are conjugation-invariant: `φ_{H^g, h^g} = φ_{H,h}`

Conjugating the index pair does not change the species: translation by `g`
maps `H`-fixed points bijectively to `gHg⁻¹`-fixed points, and the weight
cocycle transports `μ(ghg⁻¹, g•x) = μ(h, x)` (the same computation as the
pair-conjugation law of the census). Hence the species table of `D(G)` is
indexed by *conjugacy classes* of pairs `(H, h)` — the certificate for a
species-table matching only needs one column per class
(`DRing.species_conj`).
-/

namespace LeanDring

open MulAction

universe u v

variable {G : Type u} [Group G] {A : Type v} [CommGroup A]

namespace MonGSet

/-- Weight transport along conjugation at a fixed point:
`μ(gkg⁻¹, g•x) = μ(k, x)`. -/
theorem weight_conj_smul (X : MonGSet G A) (g k : G) (x : X.carrier)
    (hfix : k • x = x) :
    X.weight (g * k * g⁻¹) (g • x) = X.weight k x := by
  have h1 : X.weight (g * k) x = X.weight g x * X.weight k x := by
    rw [X.weight_mul g k x, hfix]
  have h2 := X.weight_mul (g * k * g⁻¹) g x
  rw [show g * k * g⁻¹ * g = g * k by group] at h2
  have h3 : X.weight k x * X.weight g x =
      X.weight (g * k * g⁻¹) (g • x) * X.weight g x :=
    (mul_comm _ _).trans (h1.symm.trans h2)
  exact (mul_right_cancel h3.symm)

/-- Translation by `g` maps `H`-fixed points to `gHg⁻¹`-fixed points. -/
noncomputable def fixedPointsConjEquiv (X : MonGSet G A) (H : Subgroup G) (g : G) :
    fixedPoints H X.carrier ≃
      fixedPoints (H.map (MulAut.conj g).toMonoidHom) X.carrier where
  toFun x := ⟨g • x.1, by
    rintro ⟨k, hk⟩
    obtain ⟨k₀, hk₀, rfl⟩ := Subgroup.mem_map.mp hk
    change (MulAut.conj g) k₀ • (g • x.1) = g • x.1
    rw [MulAut.conj_apply, mul_smul, mul_smul, inv_smul_smul,
      show k₀ • x.1 = x.1 from x.2 ⟨k₀, hk₀⟩]⟩
  invFun y := ⟨g⁻¹ • y.1, by
    rintro ⟨k, hk⟩
    have hin : g * k * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
    have := y.2 ⟨g * k * g⁻¹, hin⟩
    change (g * k * g⁻¹) • y.1 = y.1 at this
    change k • g⁻¹ • y.1 = g⁻¹ • y.1
    calc k • g⁻¹ • y.1 = g⁻¹ • (g * k * g⁻¹) • y.1 := by
          rw [smul_smul, smul_smul]
          congr 1
          group
      _ = g⁻¹ • y.1 := by rw [this]⟩
  left_inv x := Subtype.ext (inv_smul_smul g x.1)
  right_inv y := Subtype.ext (smul_inv_smul g y.1)

/-- **Species are conjugation-invariant** (semiring level). -/
theorem speciesSum_conj {R : Type*} [CommRing R] (χ : A →* R) (H : Subgroup G)
    (h : H) (g : G) (X : MonGSet G A) :
    speciesSum χ (H.map (MulAut.conj g).toMonoidHom)
      ⟨g * h * g⁻¹, Subgroup.mem_map.mpr ⟨h, h.2, rfl⟩⟩ X =
      speciesSum χ H h X := by
  refine Fintype.sum_equiv (fixedPointsConjEquiv X H g).symm _ _ fun y => ?_
  refine congrArg χ ?_
  have hfix : (h : G) • (g⁻¹ • y.1) = g⁻¹ • y.1 :=
    ((fixedPointsConjEquiv X H g).symm y).2 h
  have hw := weight_conj_smul X g (h : G) (g⁻¹ • y.1) hfix
  rw [smul_inv_smul] at hw
  exact hw

end MonGSet

namespace DRing

open MonGSet MonRing

variable {G : Type u} [Group G]

/-- **The species table is conjugation-indexed**:
`φ_{gHg⁻¹, ghg⁻¹} = φ_{H, h}` on all of `D(G)`. A species-table
certificate therefore only needs one column per conjugacy class of pairs
`(H, h)`. -/
theorem species_conj (H : Subgroup G) (h : H) (g : G) (x : DRing G) :
    species (H.map (MulAut.conj g).toMonoidHom)
      ⟨g * h * g⁻¹, Subgroup.mem_map.mpr ⟨h, h.2, rfl⟩⟩ x =
      species H h x := by
  obtain ⟨p⟩ := x
  change (speciesHom (Units.coeHom ℂ) _ _ p.1 : ℂ) - speciesHom (Units.coeHom ℂ) _ _ p.2 =
    (speciesHom (Units.coeHom ℂ) H h p.1 : ℂ) - speciesHom (Units.coeHom ℂ) H h p.2
  obtain ⟨X⟩ := p.1
  obtain ⟨Y⟩ := p.2
  change (speciesSum (Units.coeHom ℂ) _ _ X : ℂ) - speciesSum (Units.coeHom ℂ) _ _ Y =
    (speciesSum (Units.coeHom ℂ) H h X : ℂ) - speciesSum (Units.coeHom ℂ) H h Y
  rw [speciesSum_conj, speciesSum_conj]

end DRing

end LeanDring
