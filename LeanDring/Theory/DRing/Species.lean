/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.Monomial
import LeanDring.Theory.DRing.Marks
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Layer 5 of the D-ring formalization: species (Müller, Ch. 1–2)

The core observation (Müller, Diss. Jena 2008; Boltje–García): at an
`H`-fixed point `x` of a monomial `G`-set `(X, μ)`, the weight restricted to
`H`, `h ↦ μ(h, x)`, is a *homomorphism* `H →* A` — the cocycle identity
degenerates to multiplicativity because `H` fixes `x`. Summing its values at
a chosen `h ∈ H` over all `H`-fixed points yields the **species**

`φ_{H,h}(X, μ) = ∑_{x ∈ Fix_H(X)} χ(μ(h, x)) : B^A(G) →+* R`

(`χ : A →* R` interprets weights in a commutative ring, e.g. `ℂˣ ↪ ℂ`).
Species are ring homomorphisms; on the image of `η : B(G) → B^A(G)` the
species `φ_{H,h}` collapses to the mark `H` — the species table refines the
table of marks (`species_comp_eta`).

`DRing.species H h : D(G) →+* ℂ` is the classical species of the monomial
representation ring; Müller's species table is the collection of these over
pairs `(H, hH')`.
-/

namespace LeanDring

open MulAction

universe u v

variable {G : Type u} [Group G] {A : Type v} [CommGroup A]

namespace MonGSet

/-- Canonical (noncomputable) `Fintype` on fixed-point sets of a monomial
`G`-set, so that species sums elaborate with one fixed instance. -/
noncomputable instance (X : MonGSet G A) (H : Subgroup G) :
    Fintype (fixedPoints H X.carrier) :=
  Fintype.ofFinite _

/-- **Müller's degeneration**: at an `H`-fixed point, the weight cocycle
restricts to a homomorphism `H →* A`. -/
def fixedWeight (X : MonGSet G A) (H : Subgroup G)
    (x : fixedPoints H X.carrier) : H →* A where
  toFun h := X.weight h.1 x.1
  map_one' := X.weight_one x.1
  map_mul' h h' := by
    have hfix : h'.1 • x.1 = x.1 := x.2 h'
    change X.weight (h.1 * h'.1) x.1 = _
    rw [X.weight_mul h.1 h'.1 x.1, hfix]

/-! Fixed points of monomial disjoint unions / products — same equivalences
as for plain `G`-sets. -/

/-- Fixed points of a monomial disjoint union. -/
def fixedPointsSumEquivMon (H : Subgroup G) (X Y : MonGSet G A) :
    fixedPoints H (X.disjUnion Y).carrier ≃
      fixedPoints H X.carrier ⊕ fixedPoints H Y.carrier where
  toFun := fun z => match z with
    | ⟨.inl x, hx⟩ => .inl ⟨x, fun h => Sum.inl.inj (hx h)⟩
    | ⟨.inr y, hy⟩ => .inr ⟨y, fun h => Sum.inr.inj (hy h)⟩
  invFun := Sum.elim
    (fun x => ⟨.inl x.1, fun h => congrArg Sum.inl (x.2 h)⟩)
    (fun y => ⟨.inr y.1, fun h => congrArg Sum.inr (y.2 h)⟩)
  left_inv := by rintro ⟨x | y, _⟩ <;> rfl
  right_inv := by rintro (x | y) <;> rfl

/-- Fixed points of a monomial product. -/
def fixedPointsProdEquivMon (H : Subgroup G) (X Y : MonGSet G A) :
    fixedPoints H (X.prod Y).carrier ≃
      fixedPoints H X.carrier × fixedPoints H Y.carrier where
  toFun := fun p =>
    (⟨p.1.1, fun h => congrArg Prod.fst (p.2 h)⟩, ⟨p.1.2, fun h => congrArg Prod.snd (p.2 h)⟩)
  invFun := fun p => ⟨(p.1.1, p.2.1), fun h => Prod.ext (p.1.2 h) (p.2.2 h)⟩
  left_inv := by rintro ⟨⟨x, y⟩, _⟩; rfl
  right_inv := by rintro ⟨⟨x, _⟩, ⟨y, _⟩⟩; rfl

/-- Equivariant-with-gauge isomorphisms restrict to fixed points. -/
noncomputable def fixEquivOfIso (H : Subgroup G) {X Y : MonGSet G A}
    (e : X ≃ Y) (he : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    fixedPoints H X.carrier ≃ fixedPoints H Y.carrier :=
  e.subtypeEquiv fun x => by
    simp only [mem_fixedPoints]
    constructor
    · intro hx h
      rw [show h • e x = e (h • x) from (he h x).symm, hx h]
    · intro hex h
      apply e.injective
      change e ((h : G) • x) = e x
      rw [he h x]
      exact hex h


section Species

variable {R : Type*} [CommRing R]

/-- The species sum of a monomial `G`-set at `(H, h)`, weights interpreted
through `χ : A →* R`. -/
noncomputable def speciesSum (χ : A →* R) (H : Subgroup G) (h : H)
    (X : MonGSet G A) : R :=
  ∑ x : fixedPoints H X.carrier, χ (X.fixedWeight H x h)

/-- Species sums are iso-invariant: the gauge cancels at fixed points. -/
theorem speciesSum_congr (χ : A →* R) (H : Subgroup G) (h : H)
    {X Y : MonGSet G A} (hXY : IsIso X Y) :
    speciesSum χ H h X = speciesSum χ H h Y := by
  obtain ⟨e, φ, he, hw⟩ := hXY
  refine Fintype.sum_equiv (fixEquivOfIso H e he) _ _ fun x => ?_
  congr 1
  -- the gauge relation at the fixed point `x`: `h • x = x` kills the gauge
  have hfix : h.1 • x.1 = x.1 := x.2 h
  have := hw h.1 x.1
  rw [hfix] at this
  -- this : Y.weight h (e x) * φ x = φ x * X.weight h x
  have : Y.weight h.1 (e x.1) = X.weight h.1 x.1 := by
    have hcomm : Y.weight h.1 (e x.1) * φ x.1 = X.weight h.1 x.1 * φ x.1 := by
      rw [this, mul_comm]
    exact mul_right_cancel hcomm
  exact this.symm

@[simp] theorem speciesSum_disjUnion (χ : A →* R) (H : Subgroup G) (h : H)
    (X Y : MonGSet G A) :
    speciesSum χ H h (X.disjUnion Y) = speciesSum χ H h X + speciesSum χ H h Y := by
  classical
  rw [speciesSum, Fintype.sum_equiv (fixedPointsSumEquivMon H X Y)
    _ (Sum.elim (fun x => χ (X.fixedWeight H x h)) (fun y => χ (Y.fixedWeight H y h)))
    ?_, Fintype.sum_sum_type]
  · rfl
  · rintro ⟨x | y, hz⟩ <;> rfl

@[simp] theorem speciesSum_prod (χ : A →* R) (H : Subgroup G) (h : H)
    (X Y : MonGSet G A) :
    speciesSum χ H h (X.prod Y) = speciesSum χ H h X * speciesSum χ H h Y := by
  classical
  rw [speciesSum, Fintype.sum_equiv (fixedPointsProdEquivMon H X Y)
    _ (fun p => χ (X.fixedWeight H p.1 h) * χ (Y.fixedWeight H p.2 h)) ?_,
    Fintype.sum_prod_type]
  · dsimp only
    rw [← Fintype.sum_mul_sum]
    rfl
  · rintro ⟨⟨x, y⟩, hz⟩
    exact χ.map_mul _ _

@[simp] theorem speciesSum_empty (χ : A →* R) (H : Subgroup G) (h : H) :
    speciesSum χ H h (empty : MonGSet G A) = 0 := by
  have : IsEmpty (fixedPoints H (empty : MonGSet G A).carrier) :=
    ⟨fun z => z.1.elim⟩
  exact Fintype.sum_empty _

@[simp] theorem speciesSum_point (χ : A →* R) (H : Subgroup G) (h : H) :
    speciesSum χ H h (point : MonGSet G A) = 1 := by
  have : Unique (fixedPoints H (point : MonGSet G A).carrier) :=
    { default := ⟨PUnit.unit, fun _ => rfl⟩
      uniq := fun _ => Subtype.ext rfl }
  rw [speciesSum, Fintype.sum_unique]
  exact χ.map_one

/-- On trivial weights (the `η`-image), every species summand is `1`, so the
species sum is the number of fixed points — the mark. -/
theorem speciesSum_ofFinGSet (χ : A →* R) (H : Subgroup G) (h : H)
    (X : FinGSet G) :
    speciesSum χ H h (ofFinGSet X : MonGSet G A) = (FinGSet.fix H X : R) := by
  have hcard : FinGSet.fix H X =
      Fintype.card (fixedPoints H (ofFinGSet X : MonGSet G A).carrier) :=
    Nat.card_eq_fintype_card
      (α := fixedPoints H (ofFinGSet X : MonGSet G A).carrier)
  have hone : ∀ x : fixedPoints H (ofFinGSet X : MonGSet G A).carrier,
      χ ((ofFinGSet X : MonGSet G A).fixedWeight H x h) = 1 := fun x => χ.map_one
  rw [speciesSum, Finset.sum_congr rfl fun x _ => hone x, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, hcard]

end Species

end MonGSet

/-! ## Species as ring homomorphisms on `B^A(G)` and `D(G)` -/

namespace MonRing

open MonGSet

variable {R : Type*} [CommRing R]

/-- The `(H, h)`-species on the fibered Burnside semiring, as a semiring hom. -/
noncomputable def speciesHom (χ : A →* R) (H : Subgroup G) (h : H) :
    MonGSet.Skel G A →+* R where
  toFun := Quotient.lift (speciesSum χ H h) fun _ _ hXY => speciesSum_congr χ H h hXY
  map_zero' := speciesSum_empty χ H h
  map_one' := speciesSum_point χ H h
  map_add' a b := by
    refine Quotient.ind₂ (fun X Y => ?_) a b
    exact speciesSum_disjUnion χ H h X Y
  map_mul' a b := by
    refine Quotient.ind₂ (fun X Y => ?_) a b
    exact speciesSum_prod χ H h X Y

/-- **The species** `φ_{H,h} : B^A(G) →+* R`. -/
noncomputable def species (χ : A →* R) (H : Subgroup G) (h : H) :
    MonRing G A →+* R :=
  GrothendieckRing.lift (speciesHom χ H h)

/-- **Species refine marks**: on the canonical copy of `B(G)` inside
`B^A(G)`, every species `φ_{H,h}` restricts to the mark homomorphism at `H`
(Müller: the trivial-character column of the species table is the table of
marks). -/
theorem species_comp_eta (χ : A →* R) (H : Subgroup G) (h : H) :
    (species χ H h).comp (eta : BurnsideRing G →+* MonRing G A) =
      (Int.castRingHom R).comp (BurnsideRing.mark H) := by
  refine GrothendieckRing.hom_ext fun a => ?_
  obtain ⟨X⟩ := a
  change species χ H h (eta (GrothendieckRing.of (FinGSet.Skel.mk X))) =
    (Int.castRingHom R) (BurnsideRing.mark H (GrothendieckRing.of (FinGSet.Skel.mk X)))
  rw [eta, GrothendieckRing.map_of, species, GrothendieckRing.lift_of,
    BurnsideRing.mark_of]
  change speciesSum χ H h (ofFinGSet X) = ((FinGSet.fix H X : ℤ) : R)
  rw [speciesSum_ofFinGSet]
  push_cast
  rfl

end MonRing

namespace DRing

open MonGSet

/-- **The classical species of the D-ring** `φ_{H,h} : D(G) →+* ℂ`,
interpreting `ℂˣ`-weights in `ℂ`. Müller's species table of `G` is the
family of these over conjugacy classes of pairs `(H, hH')`. -/
noncomputable def species (H : Subgroup G) (h : H) : DRing G →+* ℂ :=
  MonRing.species (Units.coeHom ℂ) H h

/-- The species table refines the table of marks (trivial-weight column). -/
theorem species_comp_eta (H : Subgroup G) (h : H) :
    (species H h).comp (MonRing.eta : BurnsideRing G →+* DRing G) =
      (Int.castRingHom ℂ).comp (BurnsideRing.mark H) :=
  MonRing.species_comp_eta (Units.coeHom ℂ) H h

end DRing

end LeanDring
