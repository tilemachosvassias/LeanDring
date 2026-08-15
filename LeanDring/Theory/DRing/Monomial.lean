/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.Burnside
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Group

/-!
# Layer 4 of the D-ring formalization: monomial `G`-sets and the ring `D(G)`

An `A`-weighted (monomial) `G`-set is a finite `G`-set `X` together with a
weight cocycle `μ : G → X → A` into a commutative group `A`, satisfying
`μ(gh, x) = μ(g, h•x) · μ(h, x)`. This encodes a monomial representation
`⊕_{x∈X} ℂ e_x`, `g·e_x = μ(g,x) e_{g•x}`, and is the `A`-fibered `G`-set
datum of the fibered Burnside ring framework (Dress; Boltje–García).

Isomorphisms are equivariant bijections *up to gauge*: an equivariant
`e : X ≃ Y` together with `φ : X → A` rescaling each line, subject to
`μ_Y(g, e x) · φ(x) = φ(g•x) · μ_X(g, x)`.

* `MonGSet G A` — bundled monomial `G`-sets; `⊔`, `×` (weights multiply).
* `MonGSet.Skel G A` — iso classes: the fibered Burnside *semiring*.
* `MonRing G A` — its Grothendieck ring, the `A`-fibered Burnside ring
  `B^A(G)`; `DRing G := MonRing G ℂˣ` is *the* D-ring `D(G)`.
* `MonRing.eta : B(G) →+* MonRing G A` — the canonical embedding `η`
  (trivial weights). Injectivity is *proven* via the weight-forgetting
  retraction `MonRing.forget` with `forget ∘ η = id`.
-/

namespace LeanDring

universe u v

variable (G : Type u) [Group G] (A : Type v) [CommGroup A]

/-! ## Monomial `G`-sets -/

/-- A bundled monomial (`A`-weighted) `G`-set: a finite `G`-set with a weight
cocycle `μ : G → X → A`, `μ(gh, x) = μ(g, h•x) · μ(h, x)`. -/
structure MonGSet where
  /-- The underlying type. -/
  carrier : Type u
  [fintype : Fintype carrier]
  [action : MulAction G carrier]
  /-- The weight cocycle. -/
  weight : G → carrier → A
  weight_mul : ∀ g h x, weight (g * h) x = weight g (h • x) * weight h x

namespace MonGSet

instance : CoeSort (MonGSet G A) (Type u) := ⟨carrier⟩

attribute [instance] fintype action

variable {G A}

@[simp] theorem weight_one (X : MonGSet G A) (x : X) : X.weight 1 x = 1 := by
  have h := X.weight_mul 1 1 x
  rw [one_mul, one_smul] at h
  exact mul_right_cancel (by rw [← h, one_mul])

/-- Isomorphism of monomial `G`-sets: an equivariant bijection `e` together
with a gauge `φ` rescaling each line, compatible with the weights. -/
def IsIso (X Y : MonGSet G A) : Prop :=
  ∃ (e : X ≃ Y) (φ : X → A), (∀ (g : G) (x : X), e (g • x) = g • e x) ∧
    (∀ (g : G) (x : X), Y.weight g (e x) * φ x = φ (g • x) * X.weight g x)

/-- A weight-preserving equivariant bijection is an isomorphism (gauge `1`). -/
theorem isIso_of_weight_eq {X Y : MonGSet G A} (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x)
    (hw : ∀ (g : G) (x : X), Y.weight g (e x) = X.weight g x) : IsIso X Y :=
  ⟨e, fun _ => 1, he, fun g x => by rw [mul_one, one_mul, hw]⟩

theorem IsIso.refl (X : MonGSet G A) : IsIso X X :=
  isIso_of_weight_eq (Equiv.refl X) (fun _ _ => rfl) (fun _ _ => rfl)

theorem IsIso.symm {X Y : MonGSet G A} : IsIso X Y → IsIso Y X := by
  rintro ⟨e, φ, he, hw⟩
  have he' : ∀ (g : G) (y : Y), e.symm (g • y) = g • e.symm y := fun g y =>
    e.injective <| by rw [he, e.apply_symm_apply, e.apply_symm_apply]
  refine ⟨e.symm, fun y => (φ (e.symm y))⁻¹, he', fun g y => ?_⟩
  have h := hw g (e.symm y)
  rw [e.apply_symm_apply, ← he' g y] at h
  -- h : Y.weight g y * φ (e.symm y) = φ (e.symm (g • y)) * X.weight g (e.symm y)
  calc X.weight g (e.symm y) * (φ (e.symm y))⁻¹
      = (φ (e.symm (g • y)))⁻¹ * (φ (e.symm (g • y)) * X.weight g (e.symm y)) *
        (φ (e.symm y))⁻¹ := by group
    _ = (φ (e.symm (g • y)))⁻¹ * (Y.weight g y * φ (e.symm y)) * (φ (e.symm y))⁻¹ := by
        rw [h]
    _ = (φ (e.symm (g • y)))⁻¹ * Y.weight g y := by group

theorem IsIso.trans {X Y Z : MonGSet G A} : IsIso X Y → IsIso Y Z → IsIso X Z := by
  rintro ⟨e, φ, he, hw⟩ ⟨f, ψ, hf, hv⟩
  refine ⟨e.trans f, fun x => ψ (e x) * φ x, fun g x => by simp [he, hf], fun g x => ?_⟩
  calc Z.weight g (f (e x)) * (ψ (e x) * φ x)
      = (Z.weight g (f (e x)) * ψ (e x)) * φ x := by rw [mul_assoc]
    _ = (ψ (g • e x) * Y.weight g (e x)) * φ x := by rw [hv]
    _ = ψ (g • e x) * (Y.weight g (e x) * φ x) := by rw [mul_assoc]
    _ = ψ (g • e x) * (φ (g • x) * X.weight g x) := by rw [hw]
    _ = (ψ (e (g • x)) * φ (g • x)) * X.weight g x := by rw [he, mul_assoc]

variable (G A)

/-- The setoid of monomial `G`-sets up to isomorphism. -/
instance isoSetoid : Setoid (MonGSet G A) where
  r := IsIso
  iseqv := ⟨IsIso.refl, IsIso.symm, IsIso.trans⟩

variable {G A}

/-- A plain finite `G`-set with trivial weights. -/
def ofFinGSet (X : FinGSet G) : MonGSet G A :=
  { carrier := X
    weight := fun _ _ => 1
    weight_mul := fun _ _ _ => (one_mul 1).symm }

/-- The underlying finite `G`-set (forget the weights). -/
def toFinGSet (X : MonGSet G A) : FinGSet G := ⟨X.carrier⟩

@[simp] theorem toFinGSet_ofFinGSet (X : FinGSet G) :
    (ofFinGSet (A := A) X).toFinGSet = X := rfl

/-- Disjoint union of monomial `G`-sets. -/
def disjUnion (X Y : MonGSet G A) : MonGSet G A where
  carrier := X ⊕ Y
  weight g := Sum.elim (X.weight g) (Y.weight g)
  weight_mul g h x := by
    rcases x with x | y
    · exact X.weight_mul g h x
    · exact Y.weight_mul g h y

/-- Product of monomial `G`-sets (diagonal action, weights multiply). -/
def prod (X Y : MonGSet G A) : MonGSet G A where
  carrier := X × Y
  weight g p := X.weight g p.1 * Y.weight g p.2
  weight_mul g h p := by
    rw [X.weight_mul g h p.1, Y.weight_mul g h p.2, mul_mul_mul_comm]
    rfl

/-- The empty monomial `G`-set. -/
def empty : MonGSet G A := ofFinGSet FinGSet.empty

/-- The one-point monomial `G`-set with trivial weight. -/
def point : MonGSet G A := ofFinGSet FinGSet.point

theorem disjUnion_congr {X X' Y Y' : MonGSet G A} (hX : IsIso X X') (hY : IsIso Y Y') :
    IsIso (X.disjUnion Y) (X'.disjUnion Y') := by
  obtain ⟨e, φ, he, hw⟩ := hX
  obtain ⟨f, ψ, hf, hv⟩ := hY
  refine ⟨e.sumCongr f, Sum.elim φ ψ, ?_, ?_⟩
  · rintro g (x | y)
    · exact congrArg Sum.inl (he g x)
    · exact congrArg Sum.inr (hf g y)
  · rintro g (x | y)
    · exact hw g x
    · exact hv g y

theorem prod_congr {X X' Y Y' : MonGSet G A} (hX : IsIso X X') (hY : IsIso Y Y') :
    IsIso (X.prod Y) (X'.prod Y') := by
  obtain ⟨e, φ, he, hw⟩ := hX
  obtain ⟨f, ψ, hf, hv⟩ := hY
  refine ⟨e.prodCongr f, fun p => φ p.1 * ψ p.2, ?_, ?_⟩
  · exact fun g p => Prod.ext (he g p.1) (hf g p.2)
  · intro g p
    calc (X'.weight g (e p.1) * Y'.weight g (f p.2)) * (φ p.1 * ψ p.2)
        = (X'.weight g (e p.1) * φ p.1) * (Y'.weight g (f p.2) * ψ p.2) := by
          rw [mul_mul_mul_comm]
      _ = (φ (g • p.1) * X.weight g p.1) * (ψ (g • p.2) * Y.weight g p.2) := by
          rw [hw, hv]
      _ = (φ (g • p.1) * ψ (g • p.2)) * (X.weight g p.1 * Y.weight g p.2) := by
          rw [mul_mul_mul_comm]

/-! ## The skeleton: the fibered Burnside semiring -/

variable (G A) in
/-- Iso classes of monomial `G`-sets: the `A`-fibered Burnside *semiring*. -/
def Skel := Quotient (isoSetoid G A)

namespace Skel

/-- The iso class of a monomial `G`-set. -/
def mk (X : MonGSet G A) : Skel G A := Quotient.mk _ X

instance : Zero (Skel G A) := ⟨mk empty⟩
instance : One (Skel G A) := ⟨mk point⟩

instance : Add (Skel G A) :=
  ⟨Quotient.map₂ disjUnion fun _ _ h _ _ h' => disjUnion_congr h h'⟩

instance : Mul (Skel G A) :=
  ⟨Quotient.map₂ prod fun _ _ h _ _ h' => prod_congr h h'⟩

@[simp] theorem mk_disjUnion (X Y : MonGSet G A) : mk (X.disjUnion Y) = mk X + mk Y := rfl
@[simp] theorem mk_prod (X Y : MonGSet G A) : mk (X.prod Y) = mk X * mk Y := rfl

instance : AddCommMonoid (Skel G A) where
  add_assoc a b c := by
    induction a, b using Quotient.ind₂
    induction c using Quotient.ind
    exact Quotient.sound <| isIso_of_weight_eq (Equiv.sumAssoc _ _ _)
      (by rintro g ((x | y) | z) <;> rfl) (by rintro g ((x | y) | z) <;> rfl)
  add_comm a b := by
    induction a, b using Quotient.ind₂
    exact Quotient.sound <| isIso_of_weight_eq (Equiv.sumComm _ _)
      (by rintro g (x | y) <;> rfl) (by rintro g (x | y) <;> rfl)
  zero_add a := by
    induction a using Quotient.ind
    exact Quotient.sound <| isIso_of_weight_eq (Equiv.emptySum PEmpty _)
      (by rintro g (x | x); exacts [x.elim, rfl]) (by rintro g (x | x); exacts [x.elim, rfl])
  add_zero a := by
    induction a using Quotient.ind
    exact Quotient.sound <| isIso_of_weight_eq (Equiv.sumEmpty _ PEmpty)
      (by rintro g (x | x); exacts [rfl, x.elim]) (by rintro g (x | x); exacts [rfl, x.elim])
  nsmul := nsmulRec

instance : CommMonoid (Skel G A) where
  mul_assoc a b c := by
    induction a, b using Quotient.ind₂
    induction c using Quotient.ind
    exact Quotient.sound <| isIso_of_weight_eq (Equiv.prodAssoc _ _ _)
      (fun g p => rfl) (fun g p => (mul_assoc _ _ _).symm)
  mul_comm a b := by
    induction a, b using Quotient.ind₂
    exact Quotient.sound <| isIso_of_weight_eq (Equiv.prodComm _ _)
      (fun g p => rfl) (fun g p => mul_comm _ _)
  one_mul a := by
    obtain ⟨X⟩ := a
    exact Quotient.sound <| isIso_of_weight_eq (Equiv.punitProd _)
      (fun g p => rfl) (fun g p => (one_mul (X.weight g p.2)).symm)
  mul_one a := by
    obtain ⟨X⟩ := a
    exact Quotient.sound <| isIso_of_weight_eq (Equiv.prodPUnit _)
      (fun g p => rfl) (fun g p => (mul_one (X.weight g p.1)).symm)

/-- The `A`-fibered Burnside semiring. -/
instance : CommSemiring (Skel G A) where
  __ : AddCommMonoid (Skel G A) := inferInstance
  __ : CommMonoid (Skel G A) := inferInstance
  left_distrib a b c := by
    induction a, b using Quotient.ind₂
    induction c using Quotient.ind
    exact Quotient.sound <| isIso_of_weight_eq (Equiv.prodSumDistrib _ _ _)
      (by rintro g ⟨x, y | z⟩ <;> rfl) (by rintro g ⟨x, y | z⟩ <;> rfl)
  right_distrib a b c := by
    induction a, b using Quotient.ind₂
    induction c using Quotient.ind
    exact Quotient.sound <| isIso_of_weight_eq (Equiv.sumProdDistrib _ _ _)
      (by rintro g ⟨x | y, z⟩ <;> rfl) (by rintro g ⟨x | y, z⟩ <;> rfl)
  zero_mul a := by
    induction a using Quotient.ind
    exact Quotient.sound <| isIso_of_weight_eq (Equiv.pemptyProd _)
      (fun g p => p.1.elim) (fun g p => p.1.elim)
  mul_zero a := by
    induction a using Quotient.ind
    exact Quotient.sound <| isIso_of_weight_eq (Equiv.prodPEmpty _)
      (fun g p => p.2.elim) (fun g p => p.2.elim)

/-- Attaching trivial weights, as a semiring hom from the Burnside semiring. -/
def ofFinHom : FinGSet.Skel G →+* Skel G A where
  toFun := Quotient.map ofFinGSet fun X Y => by
    rintro ⟨e, he⟩
    exact isIso_of_weight_eq e he fun _ _ => rfl
  map_zero' := rfl
  map_one' := rfl
  map_add' a b := by
    refine Quotient.ind₂ (fun X Y => ?_) a b
    exact Quotient.sound <| isIso_of_weight_eq (Equiv.refl _)
      (fun _ _ => rfl) (by rintro g (x | y) <;> rfl)
  map_mul' a b := by
    refine Quotient.ind₂ (fun X Y => ?_) a b
    exact Quotient.sound <| isIso_of_weight_eq (Equiv.refl _)
      (fun _ _ => rfl) (fun g p => one_mul (1 : A))

/-- Forgetting the weights, as a semiring hom to the Burnside semiring. -/
def forgetHom : Skel G A →+* FinGSet.Skel G where
  toFun := Quotient.map toFinGSet fun X Y => by
    rintro ⟨e, φ, he, hw⟩
    exact ⟨e, he⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' a b := by
    refine Quotient.ind₂ (fun X Y => ?_) a b
    rfl
  map_mul' a b := by
    refine Quotient.ind₂ (fun X Y => ?_) a b
    rfl

@[simp] theorem forgetHom_ofFinHom (a : FinGSet.Skel G) :
    forgetHom (ofFinHom (A := A) a) = a := by
  obtain ⟨X⟩ := a
  rfl

end Skel

end MonGSet

/-! ## Layer 4 proper: the fibered Burnside ring / D-ring -/

/-- The `A`-fibered Burnside ring `B^A(G)`: the Grothendieck ring of the
semiring of iso classes of monomial `G`-sets. -/
abbrev MonRing := GrothendieckRing (MonGSet.Skel G A)

/-- **The D-ring** `D(G)`: the `ℂˣ`-fibered Burnside ring — the ring of
monomial representations. -/
abbrev DRing := MonRing G ℂˣ

namespace MonRing

open MonGSet

variable {G A}

/-- The canonical embedding `η : B(G) → B^A(G)` (trivial weights). -/
def eta : BurnsideRing G →+* MonRing G A :=
  GrothendieckRing.map Skel.ofFinHom

/-- The weight-forgetting retraction `B^A(G) → B(G)`. -/
def forget : MonRing G A →+* BurnsideRing G :=
  GrothendieckRing.map Skel.forgetHom

@[simp] theorem forget_eta (x : BurnsideRing G) :
    forget (eta (A := A) x) = x := by
  rw [forget, eta, GrothendieckRing.map_map]
  have h : (Skel.forgetHom (G := G)).comp (Skel.ofFinHom (A := A)) =
      RingHom.id (FinGSet.Skel G) :=
    RingHom.ext fun a => Skel.forgetHom_ofFinHom a
  rw [h, GrothendieckRing.map_id]
  rfl

/-- **`η` is injective**: `B(G)` embeds in `B^A(G)` — split by `forget`. -/
theorem eta_injective :
    Function.Injective (eta : BurnsideRing G →+* MonRing G A) :=
  Function.LeftInverse.injective forget_eta

end MonRing

end LeanDring
