/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.GrothendieckRing
import Mathlib.Algebra.Group.Action.Sum
import Mathlib.Algebra.Group.Action.Prod
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Sum
import Mathlib.Tactic.Common
import Mathlib.Tactic.Ring

/-!
# Finite `G`-sets and the Burnside ring

The base of the D-ring formalization:

* `FinGSet G`: bundled finite `G`-sets, with disjoint union and product.
  `FinGSet.Skel G` is the type of isomorphism classes — the Burnside
  *semiring*.
* `BurnsideRing G`: the Grothendieck ring of `FinGSet.Skel G`, built as the
  pairs quotient `(a, b) ↦ "a - b"` with the cancellation-free relation
  `(a,b) ~ (c,d) ↔ ∃ k, a + d + k = c + b + k`.

Definitions are built from Mathlib primitives (`MulAction`, `Fintype`,
`Sum`/`Prod` actions) so they cannot quietly mean the wrong thing.
-/

namespace LeanDring

universe u v

variable (G : Type u) [Group G]

/-- Trivial action on an empty type. -/
instance : MulAction G PEmpty.{v + 1} where
  smul _ x := x.elim
  one_smul x := x.elim
  mul_smul _ _ x := x.elim

/-- Trivial action on a point. -/
instance : MulAction G PUnit.{v + 1} where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-! ## Finite `G`-sets -/

/-- A bundled finite `G`-set: a finite type with a `G`-action. -/
structure FinGSet where
  /-- The underlying type. -/
  carrier : Type u
  [fintype : Fintype carrier]
  [action : MulAction G carrier]

namespace FinGSet

instance : CoeSort (FinGSet G) (Type u) := ⟨carrier⟩

attribute [instance] fintype action

variable {G}

/-- Equivariant isomorphism of `G`-sets (as a `Prop`, for the setoid). -/
def IsIso (X Y : FinGSet G) : Prop :=
  ∃ e : X ≃ Y, ∀ (g : G) (x : X), e (g • x) = g • e x

theorem IsIso.refl (X : FinGSet G) : IsIso X X :=
  ⟨Equiv.refl X, fun _ _ => rfl⟩

theorem IsIso.symm {X Y : FinGSet G} : IsIso X Y → IsIso Y X := by
  rintro ⟨e, he⟩
  exact ⟨e.symm, fun g y => e.injective <| by simp [he]⟩

theorem IsIso.trans {X Y Z : FinGSet G} : IsIso X Y → IsIso Y Z → IsIso X Z := by
  rintro ⟨e, he⟩ ⟨f, hf⟩
  exact ⟨e.trans f, fun g x => by simp [he, hf]⟩

variable (G)

/-- The setoid of finite `G`-sets up to equivariant isomorphism. -/
instance isoSetoid : Setoid (FinGSet G) where
  r := IsIso
  iseqv := ⟨IsIso.refl, IsIso.symm, IsIso.trans⟩

variable {G}

/-- Disjoint union of finite `G`-sets. -/
def disjUnion (X Y : FinGSet G) : FinGSet G := ⟨X ⊕ Y⟩

/-- Product of finite `G`-sets (diagonal action). -/
def prod (X Y : FinGSet G) : FinGSet G := ⟨X × Y⟩

/-- The empty `G`-set. -/
def empty : FinGSet G := ⟨PEmpty⟩

/-- The one-point `G`-set (`G/G`). -/
def point : FinGSet G := ⟨PUnit⟩

theorem disjUnion_congr {X X' Y Y' : FinGSet G} (hX : IsIso X X') (hY : IsIso Y Y') :
    IsIso (X.disjUnion Y) (X'.disjUnion Y') := by
  obtain ⟨e, he⟩ := hX
  obtain ⟨f, hf⟩ := hY
  refine ⟨e.sumCongr f, ?_⟩
  rintro g (x | y)
  · exact congrArg Sum.inl (he g x)
  · exact congrArg Sum.inr (hf g y)

theorem prod_congr {X X' Y Y' : FinGSet G} (hX : IsIso X X') (hY : IsIso Y Y') :
    IsIso (X.prod Y) (X'.prod Y') := by
  obtain ⟨e, he⟩ := hX
  obtain ⟨f, hf⟩ := hY
  exact ⟨e.prodCongr f, fun g p => Prod.ext (he g p.1) (hf g p.2)⟩

/-! ## The skeleton (iso classes): the Burnside semiring -/

variable (G) in
/-- Iso classes of finite `G`-sets. Additive structure = disjoint union,
multiplicative structure = product: the Burnside *semiring*. -/
def Skel : Type (u + 1) := Quotient (isoSetoid G)

namespace Skel

/-- The iso class of a finite `G`-set. -/
def mk (X : FinGSet G) : Skel G := Quotient.mk _ X

instance : Zero (Skel G) := ⟨mk empty⟩
instance : One (Skel G) := ⟨mk point⟩

instance : Add (Skel G) :=
  ⟨Quotient.map₂ disjUnion fun _ _ h _ _ h' => disjUnion_congr h h'⟩

instance : Mul (Skel G) :=
  ⟨Quotient.map₂ prod fun _ _ h _ _ h' => prod_congr h h'⟩

@[simp] theorem mk_disjUnion (X Y : FinGSet G) : mk (X.disjUnion Y) = mk X + mk Y := rfl
@[simp] theorem mk_prod (X Y : FinGSet G) : mk (X.prod Y) = mk X * mk Y := rfl

instance : AddCommMonoid (Skel G) where
  add_assoc a b c := by
    induction a, b using Quotient.ind₂
    induction c using Quotient.ind
    exact Quotient.sound ⟨Equiv.sumAssoc _ _ _, by rintro g ((x | y) | z) <;> rfl⟩
  add_comm a b := by
    induction a, b using Quotient.ind₂
    exact Quotient.sound ⟨Equiv.sumComm _ _, by rintro g (x | y) <;> rfl⟩
  zero_add a := by
    induction a using Quotient.ind
    exact Quotient.sound ⟨Equiv.emptySum PEmpty _, by rintro g (x | x); exacts [x.elim, rfl]⟩
  add_zero a := by
    induction a using Quotient.ind
    exact Quotient.sound ⟨Equiv.sumEmpty _ PEmpty, by rintro g (x | x); exacts [rfl, x.elim]⟩
  nsmul := nsmulRec

instance : CommMonoid (Skel G) where
  mul_assoc a b c := by
    induction a, b using Quotient.ind₂
    induction c using Quotient.ind
    exact Quotient.sound ⟨Equiv.prodAssoc _ _ _, fun g p => rfl⟩
  mul_comm a b := by
    induction a, b using Quotient.ind₂
    exact Quotient.sound ⟨Equiv.prodComm _ _, fun g p => rfl⟩
  one_mul a := by
    induction a using Quotient.ind
    exact Quotient.sound ⟨Equiv.punitProd _, fun g p => rfl⟩
  mul_one a := by
    induction a using Quotient.ind
    exact Quotient.sound ⟨Equiv.prodPUnit _, fun g p => rfl⟩

/-- The Burnside semiring of iso classes of finite `G`-sets.
Distributivity is `X × (Y ⊔ Z) ≅ X × Y ⊔ X × Z`. -/
instance : CommSemiring (Skel G) where
  __ : AddCommMonoid (Skel G) := inferInstance
  __ : CommMonoid (Skel G) := inferInstance
  left_distrib a b c := by
    induction a, b using Quotient.ind₂
    induction c using Quotient.ind
    exact Quotient.sound ⟨Equiv.prodSumDistrib _ _ _, by rintro g ⟨x, y | z⟩ <;> rfl⟩
  right_distrib a b c := by
    induction a, b using Quotient.ind₂
    induction c using Quotient.ind
    exact Quotient.sound ⟨Equiv.sumProdDistrib _ _ _, by rintro g ⟨x | y, z⟩ <;> rfl⟩
  zero_mul a := by
    induction a using Quotient.ind
    exact Quotient.sound ⟨Equiv.pemptyProd _, fun g p => p.1.elim⟩
  mul_zero a := by
    induction a using Quotient.ind
    exact Quotient.sound ⟨Equiv.prodPEmpty _, fun g p => p.2.elim⟩

/-- Cardinality descends to iso classes. -/
def card : Skel G → ℕ :=
  Quotient.lift (fun X => Fintype.card X) fun _ _ ⟨e, _⟩ => Fintype.card_congr e

@[simp] theorem card_mk (X : FinGSet G) : card (mk X) = Fintype.card X := rfl

@[simp] theorem card_zero : card (0 : Skel G) = 0 := by
  simp [show (0 : Skel G) = mk empty from rfl, empty]

@[simp] theorem card_one : card (1 : Skel G) = 1 := by
  simp [show (1 : Skel G) = mk point from rfl, point]

@[simp] theorem card_add (a b : Skel G) : card (a + b) = card a + card b := by
  induction a, b using Quotient.ind₂
  exact Fintype.card_sum

@[simp] theorem card_mul (a b : Skel G) : card (a * b) = card a * card b := by
  induction a, b using Quotient.ind₂
  exact Fintype.card_prod _ _

end Skel

end FinGSet

/-! ## The Burnside ring `B(G)` -/

open FinGSet

variable {G}

/-- Cardinality as a semiring homomorphism `Skel G →+* ℕ`. -/
def FinGSet.Skel.cardHom : Skel G →+* ℕ where
  toFun := Skel.card
  map_zero' := Skel.card_zero
  map_one' := Skel.card_one
  map_add' := Skel.card_add
  map_mul' := Skel.card_mul

variable (G) in
/-- The Burnside ring `B(G)`: the Grothendieck ring of the semiring of iso
classes of finite `G`-sets. -/
abbrev BurnsideRing : Type (u + 1) := GrothendieckRing (Skel G)

namespace BurnsideRing

/-- The class `[X]` of (an iso class of) a finite `G`-set in `B(G)`. -/
abbrev of (a : Skel G) : BurnsideRing G := GrothendieckRing.of a

/-- The augmentation `B(G) → ℤ`, `[X] - [Y] ↦ |X| - |Y|`. -/
def card : BurnsideRing G →+* ℤ :=
  GrothendieckRing.lift ((Nat.castRingHom ℤ).comp Skel.cardHom)

@[simp] theorem card_of (a : Skel G) : card (of a) = (Skel.card a : ℤ) :=
  GrothendieckRing.lift_of _ a

/-! ### Sanity checks -/

/-- Over a trivial group every bijection is equivariant, so a `G`-set is
determined up to iso by its cardinality. -/
theorem _root_.LeanDring.FinGSet.Skel.card_injective_of_subsingleton [Subsingleton G] :
    Function.Injective (Skel.card : Skel G → ℕ) := by
  intro a b h
  obtain ⟨X⟩ := a
  obtain ⟨Y⟩ := b
  exact Quotient.sound ⟨Fintype.equivOfCardEq h,
    fun g x => by rw [Subsingleton.elim g 1, one_smul, one_smul]⟩

/-- Sanity: for the trivial group, `B(G) ≅ ℤ` via cardinality. -/
theorem card_bijective_of_subsingleton [Subsingleton G] :
    Function.Bijective (card : BurnsideRing G →+* ℤ) := by
  constructor
  · intro a b h
    obtain ⟨p⟩ := a
    obtain ⟨q⟩ := b
    change (Skel.card p.1 : ℤ) - Skel.card p.2 = (Skel.card q.1 : ℤ) - Skel.card q.2 at h
    refine Quotient.sound ⟨0, ?_⟩
    apply Skel.card_injective_of_subsingleton
    change Skel.card (p.1 + q.2 + 0) = Skel.card (q.1 + p.2 + 0)
    simp only [Skel.card_add, Skel.card_zero]
    omega
  · intro n
    refine ⟨GrothendieckRing.mk (n.toNat • 1) ((-n).toNat • 1), ?_⟩
    rw [card, GrothendieckRing.lift_mk]
    simp only [nsmul_eq_mul, mul_one, map_natCast]
    omega

end BurnsideRing

end LeanDring
