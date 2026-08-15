/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.Burnside
import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Marks of finite `G`-sets

For each subgroup `H ≤ G`, the mark `fix H X = |Fix_H(X)|` counts `H`-fixed
points of a finite `G`-set `X`. It is additive in `⊔`, multiplicative in `×`,
and iso-invariant, hence descends to a ring homomorphism
`mark H : B(G) →+* ℤ` — the `H`-th coordinate of the mark homomorphism
`B(G) → ∏_{(H)} ℤ`.

Injectivity of the total mark map (marks separate iso classes) is proven in
`LeanDring.Theory.DRing.MarkInjectivity`, together with its corollaries
(cancellativity of `⊔`, injectivity of `of : Skel → B(G)`).
-/

namespace LeanDring

open MulAction

universe u

variable {G : Type u} [Group G]

namespace FinGSet

/-- The number of `H`-fixed points of a finite `G`-set. -/
noncomputable def fix (H : Subgroup G) (X : FinGSet G) : ℕ :=
  Nat.card (fixedPoints H X)

/-- Equivariant isomorphisms restrict to fixed points. -/
noncomputable def fixEquivOfIso (H : Subgroup G) {X Y : FinGSet G}
    (e : X ≃ Y) (he : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    fixedPoints H X ≃ fixedPoints H Y :=
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

theorem fix_congr (H : Subgroup G) {X Y : FinGSet G} (h : IsIso X Y) :
    fix H X = fix H Y := by
  obtain ⟨e, he⟩ := h
  exact Nat.card_congr (fixEquivOfIso H e he)

/-- Fixed points of a disjoint union: the two sides don't mix. -/
def fixedPointsSumEquiv (H : Subgroup G) (X Y : FinGSet G) :
    fixedPoints H (X.disjUnion Y) ≃ fixedPoints H X ⊕ fixedPoints H Y where
  toFun := fun z => match z with
    | ⟨.inl x, hx⟩ => .inl ⟨x, fun h => Sum.inl.inj (hx h)⟩
    | ⟨.inr y, hy⟩ => .inr ⟨y, fun h => Sum.inr.inj (hy h)⟩
  invFun := Sum.elim
    (fun x => ⟨.inl x.1, fun h => congrArg Sum.inl (x.2 h)⟩)
    (fun y => ⟨.inr y.1, fun h => congrArg Sum.inr (y.2 h)⟩)
  left_inv := by rintro ⟨x | y, _⟩ <;> rfl
  right_inv := by rintro (x | y) <;> rfl

/-- Fixed points of a product: computed coordinatewise. -/
def fixedPointsProdEquiv (H : Subgroup G) (X Y : FinGSet G) :
    fixedPoints H (X.prod Y) ≃ fixedPoints H X × fixedPoints H Y where
  toFun := fun p =>
    (⟨p.1.1, fun h => congrArg Prod.fst (p.2 h)⟩, ⟨p.1.2, fun h => congrArg Prod.snd (p.2 h)⟩)
  invFun := fun p => ⟨(p.1.1, p.2.1), fun h => Prod.ext (p.1.2 h) (p.2.2 h)⟩
  left_inv := by rintro ⟨⟨x, y⟩, _⟩; rfl
  right_inv := by rintro ⟨⟨x, _⟩, ⟨y, _⟩⟩; rfl

@[simp] theorem fix_disjUnion (H : Subgroup G) (X Y : FinGSet G) :
    fix H (X.disjUnion Y) = fix H X + fix H Y := by
  unfold fix
  rw [Nat.card_congr (fixedPointsSumEquiv H X Y), Nat.card_sum]

@[simp] theorem fix_prod (H : Subgroup G) (X Y : FinGSet G) :
    fix H (X.prod Y) = fix H X * fix H Y := by
  unfold fix
  rw [Nat.card_congr (fixedPointsProdEquiv H X Y), Nat.card_prod]

@[simp] theorem fix_empty (H : Subgroup G) : fix H (empty : FinGSet G) = 0 := by
  simp [fix, empty]

@[simp] theorem fix_point (H : Subgroup G) : fix H (point : FinGSet G) = 1 := by
  have : Unique (fixedPoints H (point : FinGSet G).carrier) :=
    { default := ⟨PUnit.unit, fun _ => rfl⟩
      uniq := fun _ => Subtype.ext rfl }
  exact Nat.card_unique

/-- The trivial subgroup fixes everything: `fix ⊥` is cardinality. -/
@[simp] theorem fix_bot (X : FinGSet G) : fix ⊥ X = Fintype.card X := by
  have : fixedPoints (⊥ : Subgroup G) X.carrier = Set.univ := by
    ext x
    simp only [mem_fixedPoints, Set.mem_univ, iff_true]
    rintro ⟨h, hh⟩
    obtain rfl : h = 1 := hh
    exact one_smul G x
  rw [fix, this, Nat.card_congr (Equiv.Set.univ _), Nat.card_eq_fintype_card]

/-! ### Transitive `G`-sets `G/H` (the basis of `B(G)`) -/

section Coset

variable (G) [Fintype G]

/-- The coset space `G ⧸ H` as a finite `G`-set — the basis elements of
`B(G)` run over these as `H` ranges over conjugacy classes of subgroups. -/
noncomputable def coset (H : Subgroup G) : FinGSet G :=
  { carrier := G ⧸ H
    fintype := Fintype.ofFinite _ }

@[simp] theorem card_coset (H : Subgroup G) : Fintype.card (coset G H) = H.index := by
  rw [← Nat.card_eq_fintype_card]; rfl

end Coset

end FinGSet

namespace FinGSet.Skel

/-- The `H`-mark descends to iso classes. -/
noncomputable def mark (H : Subgroup G) : Skel G → ℕ :=
  Quotient.lift (fix H) fun _ _ h => fix_congr H h

@[simp] theorem mark_mk (H : Subgroup G) (X : FinGSet G) : mark H (mk X) = fix H X := rfl

@[simp] theorem mark_zero (H : Subgroup G) : mark H (0 : Skel G) = 0 := fix_empty H
@[simp] theorem mark_one (H : Subgroup G) : mark H (1 : Skel G) = 1 := fix_point H

@[simp] theorem mark_add (H : Subgroup G) (a b : Skel G) :
    mark H (a + b) = mark H a + mark H b := by
  refine Quotient.ind₂ (fun X Y => ?_) a b
  exact fix_disjUnion H X Y

@[simp] theorem mark_mul (H : Subgroup G) (a b : Skel G) :
    mark H (a * b) = mark H a * mark H b := by
  refine Quotient.ind₂ (fun X Y => ?_) a b
  exact fix_prod H X Y

/-- The `H`-mark as a semiring homomorphism `Skel G →+* ℕ`. -/
noncomputable def markHom (H : Subgroup G) : Skel G →+* ℕ where
  toFun := mark H
  map_zero' := mark_zero H
  map_one' := mark_one H
  map_add' := mark_add H
  map_mul' := mark_mul H

end FinGSet.Skel

namespace BurnsideRing

open FinGSet

/-- The `H`-th mark homomorphism `B(G) →+* ℤ`, `[X] - [Y] ↦ |X^H| - |Y^H|`. -/
noncomputable def mark (H : Subgroup G) : BurnsideRing G →+* ℤ :=
  GrothendieckRing.lift ((Nat.castRingHom ℤ).comp (Skel.markHom H))

@[simp] theorem mark_of (H : Subgroup G) (a : Skel G) :
    mark H (of a) = (Skel.mark H a : ℤ) :=
  GrothendieckRing.lift_of _ a

/-- The mark at `⊥` is the augmentation (cardinality). -/
theorem mark_bot_eq_card : (mark ⊥ : BurnsideRing G →+* ℤ) = card := by
  refine GrothendieckRing.hom_ext fun a => ?_
  rw [mark_of, card_of]
  obtain ⟨X⟩ := a
  exact congrArg _ (fix_bot X)

end BurnsideRing

end LeanDring
