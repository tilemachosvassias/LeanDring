/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.Adams

/-!
# The basis elements `[K, λ]` of `D(G)` and Müller's species formula

The monomial `G`-set induced from a linear character `λ : K →* A` of a
subgroup `K ≤ G`: the coset space `G ⧸ K` with the weight cocycle
`μ(g, q) = λ(s(g•q)⁻¹ · g · s(q))` built from the canonical section
`s = Quotient.out`. These are the classes `[K, λ]` — the standard basis of
the fibered Burnside ring / D-ring.

Main results (sorry-free):

* `MonGSet.induced K l` — the monomial `G`-set `[K, λ]`;
  `toFinGSet_induced` — its underlying `G`-set is `G/K` (definitional).
* `MonGSet.induced_one_isIso` — `[K, 1] ≅ η(G/K)`: trivial character gives
  the plain coset space, so `DRing.basisElt_one` : `[K,1] = η[G/K]` in
  `D(G)`.
* `MonGSet.speciesSum_induced` / `DRing.species_basisElt` — **Müller's
  explicit species formula**:
  `φ_{H,h}[K,λ] = ∑_{q ∈ (G/K)^H} λ(s(q)⁻¹ · h · s(q))`,
  the sum over `H`-fixed cosets of the character evaluated at the
  conjugated representative.
-/

namespace LeanDring

open MulAction

universe u v

variable {G : Type u} [Group G] [Fintype G] {A : Type v} [CommGroup A]

namespace MonGSet

variable (K : Subgroup G)

omit [Fintype G] in
/-- The conjugated coset representative lands in `K`:
`s(g•q)⁻¹ · g · s(q) ∈ K`. -/
theorem induced_mem (g : G) (q : G ⧸ K) : (g • q).out⁻¹ * g * q.out ∈ K := by
  have h : (((g • q).out : G) : G ⧸ K) = ((g * q.out : G) : G ⧸ K) := by
    rw [QuotientGroup.out_eq']
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  have h2 := QuotientGroup.eq.mp h
  rwa [← mul_assoc] at h2

/-- **The basis element `[K, λ]`**: the monomial `G`-set induced from a
linear character `λ : K →* A` — cosets `G ⧸ K` with weight cocycle
`μ(g, q) = λ(s(g•q)⁻¹ · g · s(q))`, `s = Quotient.out`. -/
noncomputable def induced (l : K →* A) : MonGSet G A where
  carrier := G ⧸ K
  fintype := Fintype.ofFinite _
  action := inferInstance
  weight g q := l ⟨(g • q).out⁻¹ * g * q.out, induced_mem K g q⟩
  weight_mul g h q := by
    rw [← map_mul]
    refine congrArg l (Subtype.ext ?_)
    change ((g * h) • q).out⁻¹ * (g * h) * q.out =
      ((g • h • q).out⁻¹ * g * (h • q).out) * ((h • q).out⁻¹ * h * q.out)
    rw [mul_smul]
    group

/-- The underlying `G`-set of `[K, λ]` is the coset space `G/K`. -/
theorem toFinGSet_induced (l : K →* A) :
    (induced K l).toFinGSet = FinGSet.coset G K := rfl

/-- `[K, 1] ≅ η(G/K)`: the trivial character gives the plain coset space. -/
theorem induced_one_isIso :
    IsIso (induced K (1 : K →* A)) (ofFinGSet (FinGSet.coset G K)) :=
  isIso_of_weight_eq (Equiv.refl _) (fun _ _ => rfl) (fun _ _ => rfl)

omit [Fintype G] in
/-- For an `H`-fixed coset, the conjugated representative `s(q)⁻¹·h·s(q)`
lands in `K`. -/
theorem sectionConj_mem (H : Subgroup G) (h : H) (q : G ⧸ K)
    (hq : (h : G) • q = q) : q.out⁻¹ * h * q.out ∈ K := by
  have := induced_mem K (h : G) q
  rwa [hq] at this

/-- **Müller's species formula** (semiring level):
`φ_{H,h}[K,λ] = ∑_{q ∈ (G/K)^H} λ(s(q)⁻¹ · h · s(q))`. -/
theorem speciesSum_induced {R : Type*} [CommRing R] (χ : A →* R) (l : K →* A)
    (H : Subgroup G) (h : H) :
    speciesSum χ H h (induced K l) =
      ∑ q : fixedPoints H (induced K l : MonGSet G A).carrier,
        χ (l ⟨q.1.out⁻¹ * h * q.1.out, sectionConj_mem K H h q.1 (q.2 h)⟩) := by
  refine Finset.sum_congr rfl fun q _ => ?_
  refine congrArg χ (congrArg l (Subtype.ext ?_))
  change ((h : G) • q.1).out⁻¹ * h * q.1.out = q.1.out⁻¹ * h * q.1.out
  rw [show (h : G) • q.1 = q.1 from q.2 h]

end MonGSet

namespace DRing

open MonGSet MonRing

variable {G : Type u} [Group G] [Fintype G]

/-- **The basis element `[K, λ]` of the D-ring.** -/
noncomputable def basisElt (K : Subgroup G) (l : K →* ℂˣ) : DRing G :=
  GrothendieckRing.of (Skel.mk (induced K l))

/-- `[K, 1] = η[G/K]`: the trivial-character basis element is the image of
the Burnside basis element. -/
theorem basisElt_one (K : Subgroup G) :
    basisElt K (1 : K →* ℂˣ) =
      eta (GrothendieckRing.of (FinGSet.Skel.mk (FinGSet.coset G K))) := by
  rw [eta, GrothendieckRing.map_of]
  exact congrArg GrothendieckRing.of (Quotient.sound (induced_one_isIso K))

/-- **Müller's species formula** in `D(G)`:
`φ_{H,h}[K,λ] = ∑_{q ∈ (G/K)^H} λ(s(q)⁻¹ · h · s(q))`. -/
theorem species_basisElt (K : Subgroup G) (l : K →* ℂˣ) (H : Subgroup G) (h : H) :
    species H h (basisElt K l) =
      ∑ q : fixedPoints H (induced K l : MonGSet G ℂˣ).carrier,
        ((l ⟨q.1.out⁻¹ * h * q.1.out, sectionConj_mem K H h q.1 (q.2 h)⟩ : ℂˣ) : ℂ) := by
  have h1 : species H h (basisElt K l) =
      speciesSum (Units.coeHom ℂ) H h (induced K l) :=
    GrothendieckRing.lift_of _ _
  rw [h1, speciesSum_induced]
  rfl

end DRing

end LeanDring
