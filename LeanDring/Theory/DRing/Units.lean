/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.Classification

/-!
# Character units of `D(G)` (Müller §2.6, the `±Ĝ` part)

Every linear character `λ : G →* ℂˣ` gives a one-point monomial `G`-set
`charMon λ` (the class `[G, λ]`), and `λ ↦ [G, λ]` is an **injective**
group homomorphism `Ĝ →* D(G)ˣ` (`DRing.unitsHom`,
`DRing.unitsHom_injective`) with species `φ_{H,h}[G,λ] = λ(h)` and torsion
`[G,λ]^N = 1` for `N = exp G`. Together with `-1` this realizes the `±Ĝ`
part of Müller's torsion-unit theorem (Satz 2.6.3:
`UT(D(G)) = ±Ĝ · ∏(1 + nilpotent-graded parts)`; the graded factorization
via his Lemma 2.6.1 is future work).
-/

namespace LeanDring

open MulAction

universe u v

variable {G : Type u} [Group G] {A : Type v} [CommGroup A]

namespace MonGSet

/-- The one-point monomial `G`-set `[G, λ]` attached to a linear character:
the weight of `g` is `λ(g)`. -/
def charMon (l : G →* A) : MonGSet G A where
  carrier := PUnit
  weight g _ := l g
  weight_mul g h _ := map_mul l g h

theorem charMon_one_isIso : IsIso (charMon (1 : G →* A)) point :=
  isIso_of_weight_eq (Equiv.refl _) (fun _ _ => rfl) (fun _ _ => rfl)

/-- `[G, λ] × [G, λ′] ≅ [G, λλ′]`: characters multiply. -/
theorem charMon_mul_isIso (l l' : G →* A) :
    IsIso ((charMon l).prod (charMon l')) (charMon (l * l')) :=
  isIso_of_weight_eq (Equiv.prodPUnit PUnit) (fun _ _ => rfl) (fun _ _ => rfl)

end MonGSet

namespace DRing

open MonGSet MonRing

variable {G : Type u} [Group G]

/-- The class `[G, λ]` of a linear character in `D(G)`. -/
noncomputable def charElt (l : G →* ℂˣ) : DRing G :=
  GrothendieckRing.of (Skel.mk (charMon l))

@[simp] theorem charElt_one : charElt (1 : G →* ℂˣ) = 1 := by
  have h : Skel.mk (charMon (1 : G →* ℂˣ)) = Skel.mk point :=
    Quotient.sound charMon_one_isIso
  rw [charElt, h]
  rfl

@[simp] theorem charElt_mul (l l' : G →* ℂˣ) :
    charElt l * charElt l' = charElt (l * l') := by
  rw [charElt, charElt, charElt, ← GrothendieckRing.of_mul]
  exact congrArg GrothendieckRing.of (Quotient.sound (charMon_mul_isIso l l'))

/-- `λ ↦ [G, λ]` as a monoid homomorphism into `D(G)`. -/
noncomputable def charHom : (G →* ℂˣ) →* DRing G where
  toFun := charElt
  map_one' := charElt_one
  map_mul' l l' := (charElt_mul l l').symm

/-- **The character units** (Müller §2.6, the `Ĝ` part):
`λ ↦ [G, λ]` as a group homomorphism `Ĝ →* D(G)ˣ` — every linear character
is a unit of the D-ring. -/
noncomputable def unitsHom : (G →* ℂˣ) →* (DRing G)ˣ :=
  charHom.toHomUnits

@[simp] theorem unitsHom_coe (l : G →* ℂˣ) : (unitsHom l : DRing G) = charElt l := rfl

/-- **Species of character units**: `φ_{H,h}[G, λ] = λ(h)`. -/
theorem species_charElt (H : Subgroup G) (h : H) (l : G →* ℂˣ) :
    species H h (charElt l) = (l h : ℂ) := by
  have h1 : species H h (charElt l) =
      speciesSum (Units.coeHom ℂ) H h (charMon l) :=
    GrothendieckRing.lift_of _ _
  rw [h1, speciesSum]
  have hu : Unique (fixedPoints H (charMon l : MonGSet G ℂˣ).carrier) :=
    { default := ⟨PUnit.unit, fun _ => rfl⟩
      uniq := fun _ => Subtype.ext rfl }
  rw [Fintype.sum_unique]
  rfl

/-- **Injectivity**: distinct characters give distinct units — `Ĝ` embeds
in `D(G)ˣ`. -/
theorem unitsHom_injective : Function.Injective (unitsHom (G := G)) := by
  intro l l' h
  have helt : charElt l = charElt l' := by
    have := congrArg (Units.val) h
    simpa using this
  ext g
  -- compare species at `(⊤, g)`
  have hs := congrArg (species ⊤ ⟨g, trivial⟩) helt
  rw [species_charElt, species_charElt] at hs
  exact hs

/-- **Torsion** (with `-1`, the `±Ĝ` part of Müller Satz 2.6.3): the
character units are torsion of exponent dividing any `N` annihilating `G`. -/
theorem charElt_pow_eq_one {N : ℕ} (hN : ∀ g : G, g ^ N = 1) (l : G →* ℂˣ) :
    charElt l ^ N = 1 := by
  have hpow : charElt l ^ N = charElt (l ^ N) := (map_pow charHom l N).symm
  rw [hpow]
  have hl : l ^ N = 1 := by
    refine MonoidHom.ext fun g => ?_
    rw [MonoidHom.pow_apply, ← map_pow, hN g, map_one, MonoidHom.one_apply]
  rw [hl, charElt_one]

end DRing

/-! ## The `Ĝ`-twist action on the basis: `[G,λ]·[K,μ] = [K, μ·λ|_K]` -/

namespace MonGSet

variable {G : Type u} [Group G] {A : Type v} [CommGroup A] [Fintype G]

/-- **The character twist of a basis element**:
`[G, λ] × [K, μ] ≅ [K, μ · λ|_K]`, via the gauge `φ(q) = λ(s(q))⁻¹`. This is
the action of `Ĝ ⊆ D(G)ˣ` on the `[K, μ]` basis. -/
theorem charMon_prod_induced (l : G →* A) (K : Subgroup G) (m : K →* A) :
    IsIso ((charMon l).prod (induced K m))
      (induced K (m * l.comp K.subtype)) := by
  refine ⟨Equiv.punitProd _, fun p => (l p.2.out)⁻¹, fun g p => rfl, fun g p => ?_⟩
  -- unfold both weights at the common conjugated-representative argument
  change (m * l.comp K.subtype)
      ⟨(g • p.2).out⁻¹ * g * p.2.out, induced_mem K g p.2⟩ * (l p.2.out)⁻¹ =
    (l (g • p.2).out)⁻¹ * (l g *
      m ⟨(g • p.2).out⁻¹ * g * p.2.out, induced_mem K g p.2⟩)
  rw [MonoidHom.mul_apply]
  have hres : (l.comp K.subtype)
      ⟨(g • p.2).out⁻¹ * g * p.2.out, induced_mem K g p.2⟩ =
      (l (g • p.2).out)⁻¹ * l g * l p.2.out := by
    change l ((g • p.2).out⁻¹ * g * p.2.out) = _
    rw [map_mul, map_mul, map_inv]
  rw [hres]
  set a := m ⟨(g • p.2).out⁻¹ * g * p.2.out, induced_mem K g p.2⟩
  set b := l (g • p.2).out
  set c := l g
  set d := l p.2.out
  -- commutative-group bookkeeping: `a·(b⁻¹cd)·d⁻¹ = b⁻¹·(c·a)`
  calc a * (b⁻¹ * c * d) * d⁻¹
      = a * (b⁻¹ * c) * (d * d⁻¹) := by
        rw [← mul_assoc a (b⁻¹ * c) d, mul_assoc (a * (b⁻¹ * c)) d d⁻¹]
    _ = a * (b⁻¹ * c) := by rw [mul_inv_cancel, mul_one]
    _ = b⁻¹ * (c * a) := by rw [mul_comm a, mul_assoc]

end MonGSet

namespace DRing

variable {G : Type u} [Group G] [Fintype G]

open MonGSet

/-- **The `Ĝ`-action on the basis of `D(G)`**:
`[G, λ] · [K, μ] = [K, μ · λ|_K]` — character units permute the basis
elements by twisting the character. -/
theorem charElt_mul_basisElt (l : G →* ℂˣ) (K : Subgroup G) (m : K →* ℂˣ) :
    charElt l * basisElt K m = basisElt K (m * l.comp K.subtype) := by
  rw [charElt, basisElt, ← GrothendieckRing.of_mul]
  exact congrArg GrothendieckRing.of
    (Quotient.sound (charMon_prod_induced l K m))

end DRing

end LeanDring
