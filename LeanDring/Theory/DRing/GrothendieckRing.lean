/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Tactic.Common
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The Grothendieck ring of a commutative semiring

`GrothendieckRing S` is the ring completion of a commutative semiring `S`:
the quotient of pairs `(a, b)` (read `a - b`) by the cancellation-free
relation `(a,b) ~ (c,d) ↔ ∃ k, a + d + k = c + b + k`. Mathlib provides the
Grothendieck *group* of a commutative monoid (`Algebra.GrothendieckGroup`)
but not the ring structure, so we build it here once; both the Burnside ring
`B(G)` and the monomial ring `D(G)` are instances.

Main definitions:
* `GrothendieckRing.ofHom : S →+* GrothendieckRing S` — the canonical map,
  injective as soon as `S` is additively cancellative (`of_injective`).
* `GrothendieckRing.lift : (S →+* R) → (GrothendieckRing S →+* R)` — the
  universal property, for `R` any commutative ring.
* `GrothendieckRing.map : (S →+* T) → (GrothendieckRing S →+* GrothendieckRing T)`.
-/

namespace LeanDring

variable (S : Type*) [CommSemiring S]

/-- The Grothendieck relation on pairs `(a, b)` (read: `a - b`):
`(a, b) ~ (c, d) ↔ ∃ k, a + d + k = c + b + k`. The `∃ k` slack makes this an
equivalence relation without assuming cancellation. -/
def GrothendieckRel (p q : S × S) : Prop :=
  ∃ k : S, p.1 + q.2 + k = q.1 + p.2 + k

variable {S} in
theorem GrothendieckRel.trans' {p q r : S × S} :
    GrothendieckRel S p q → GrothendieckRel S q r → GrothendieckRel S p r := by
  rintro ⟨k, hk⟩ ⟨l, hl⟩
  refine ⟨q.2 + q.1 + k + l, ?_⟩
  calc p.1 + r.2 + (q.2 + q.1 + k + l)
      = (p.1 + q.2 + k) + (q.1 + r.2 + l) := by ring
    _ = (q.1 + p.2 + k) + (r.1 + q.2 + l) := by rw [hk, hl]
    _ = r.1 + p.2 + (q.2 + q.1 + k + l) := by ring

/-- The Grothendieck setoid on pairs. -/
instance grothendieckSetoid : Setoid (S × S) where
  r := GrothendieckRel S
  iseqv := ⟨fun _ => ⟨0, rfl⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, GrothendieckRel.trans'⟩

/-- The Grothendieck ring (ring completion) of a commutative semiring. -/
def GrothendieckRing : Type _ := Quotient (grothendieckSetoid S)

namespace GrothendieckRing

variable {S}

/-- The element `a - b` of the Grothendieck ring. -/
def mk (a b : S) : GrothendieckRing S := Quotient.mk _ (a, b)

/-- The canonical image of `a : S`. -/
def of (a : S) : GrothendieckRing S := mk a 0

instance : Zero (GrothendieckRing S) := ⟨of 0⟩
instance : One (GrothendieckRing S) := ⟨of 1⟩

instance : Add (GrothendieckRing S) :=
  ⟨Quotient.map₂ (fun p q => (p.1 + q.1, p.2 + q.2)) fun p p' hp q q' hq => by
    obtain ⟨k, hk⟩ := hp
    obtain ⟨l, hl⟩ := hq
    refine ⟨k + l, ?_⟩
    calc p.1 + q.1 + (p'.2 + q'.2) + (k + l)
        = (p.1 + p'.2 + k) + (q.1 + q'.2 + l) := by ring
      _ = (p'.1 + p.2 + k) + (q'.1 + q.2 + l) := by rw [hk, hl]
      _ = p'.1 + q'.1 + (p.2 + q.2) + (k + l) := by ring⟩

instance : Neg (GrothendieckRing S) :=
  ⟨Quotient.map (fun p => (p.2, p.1)) fun p q => by
    rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    calc p.2 + q.1 + k = q.1 + p.2 + k := by ring
      _ = p.1 + q.2 + k := hk.symm
      _ = q.2 + p.1 + k := by ring⟩

/-- `(a - b)(c - d) = (ac + bd) - (ad + bc)`. Well-definedness: vary each
factor separately (transitivity), multiplying the witness through. -/
instance : Mul (GrothendieckRing S) :=
  ⟨Quotient.map₂ (fun p q => (p.1 * q.1 + p.2 * q.2, p.1 * q.2 + p.2 * q.1))
    fun p p' hp q q' hq => by
      obtain ⟨k, hk⟩ := hp
      obtain ⟨l, hl⟩ := hq
      refine GrothendieckRel.trans'
        (q := (p'.1 * q.1 + p'.2 * q.2, p'.1 * q.2 + p'.2 * q.1)) ⟨k * (q.1 + q.2), ?_⟩
        ⟨l * (p'.1 + p'.2), ?_⟩
      · calc p.1 * q.1 + p.2 * q.2 + (p'.1 * q.2 + p'.2 * q.1) + k * (q.1 + q.2)
            = (p.1 + p'.2 + k) * q.1 + (p'.1 + p.2 + k) * q.2 := by ring
          _ = (p'.1 + p.2 + k) * q.1 + (p.1 + p'.2 + k) * q.2 := by rw [hk]
          _ = p'.1 * q.1 + p'.2 * q.2 + (p.1 * q.2 + p.2 * q.1) + k * (q.1 + q.2) := by ring
      · calc p'.1 * q.1 + p'.2 * q.2 + (p'.1 * q'.2 + p'.2 * q'.1) + l * (p'.1 + p'.2)
            = p'.1 * (q.1 + q'.2 + l) + p'.2 * (q'.1 + q.2 + l) := by ring
          _ = p'.1 * (q'.1 + q.2 + l) + p'.2 * (q.1 + q'.2 + l) := by rw [hl]
          _ = p'.1 * q'.1 + p'.2 * q'.2 + (p'.1 * q.2 + p'.2 * q.1) + l * (p'.1 + p'.2) := by
              ring⟩

@[simp] theorem mk_add_mk (a b c d : S) : mk a b + mk c d = mk (a + c) (b + d) := rfl
@[simp] theorem neg_mk (a b : S) : -mk a b = mk b a := rfl
@[simp] theorem mk_mul_mk (a b c d : S) :
    mk a b * mk c d = mk (a * c + b * d) (a * d + b * c) := rfl

theorem mk_eq_mk {a b c d : S} : mk a b = mk c d ↔ ∃ k, a + d + k = c + b + k :=
  ⟨Quotient.exact, fun h => Quotient.sound h⟩

/-- All ring laws reduce, componentwise on representative pairs, to semiring
identities in `S`, which `ring` discharges. -/
instance : CommRing (GrothendieckRing S) where
  add_assoc a b c := by
    induction a, b using Quotient.ind₂; induction c using Quotient.ind
    exact congrArg (Quotient.mk _) (Prod.ext (by ring) (by ring))
  add_comm a b := by
    induction a, b using Quotient.ind₂
    exact congrArg (Quotient.mk _) (Prod.ext (by ring) (by ring))
  zero_add a := by
    induction a using Quotient.ind
    exact congrArg (Quotient.mk _) (Prod.ext (by ring) (by ring))
  add_zero a := by
    induction a using Quotient.ind
    exact congrArg (Quotient.mk _) (Prod.ext (by ring) (by ring))
  neg_add_cancel a := by
    induction a using Quotient.ind
    exact Quotient.sound ⟨0, by ring⟩
  mul_assoc a b c := by
    induction a, b using Quotient.ind₂; induction c using Quotient.ind
    exact congrArg (Quotient.mk _) (Prod.ext (by ring) (by ring))
  mul_comm a b := by
    induction a, b using Quotient.ind₂
    exact congrArg (Quotient.mk _) (Prod.ext (by ring) (by ring))
  one_mul a := by
    induction a using Quotient.ind
    exact congrArg (Quotient.mk _) (Prod.ext (by ring) (by ring))
  mul_one a := by
    induction a using Quotient.ind
    exact congrArg (Quotient.mk _) (Prod.ext (by ring) (by ring))
  left_distrib a b c := by
    induction a, b using Quotient.ind₂; induction c using Quotient.ind
    exact congrArg (Quotient.mk _) (Prod.ext (by ring) (by ring))
  right_distrib a b c := by
    induction a, b using Quotient.ind₂; induction c using Quotient.ind
    exact congrArg (Quotient.mk _) (Prod.ext (by ring) (by ring))
  zero_mul a := by
    induction a using Quotient.ind
    exact congrArg (Quotient.mk _) (Prod.ext (by ring) (by ring))
  mul_zero a := by
    induction a using Quotient.ind
    exact congrArg (Quotient.mk _) (Prod.ext (by ring) (by ring))
  nsmul := nsmulRec
  zsmul := zsmulRec

@[simp] theorem mk_sub_mk (a b c d : S) : mk a b - mk c d = mk (a + d) (b + c) := by
  change mk a b + -mk c d = _
  rw [neg_mk, mk_add_mk]

/-- The canonical map, as a ring homomorphism. -/
def ofHom : S →+* GrothendieckRing S where
  toFun := of
  map_zero' := rfl
  map_one' := rfl
  map_add' a b := by
    change mk (a + b) 0 = mk a 0 + mk b 0
    rw [mk_add_mk, add_zero]
  map_mul' a b := by
    change mk (a * b) 0 = mk a 0 * mk b 0
    rw [mk_mul_mk]
    exact congrArg (Quotient.mk _) (Prod.ext (by ring) (by ring))

@[simp] theorem ofHom_apply (a : S) : ofHom a = of a := rfl
@[simp] theorem of_zero : (of 0 : GrothendieckRing S) = 0 := rfl
@[simp] theorem of_one : (of 1 : GrothendieckRing S) = 1 := rfl
@[simp] theorem of_add (a b : S) : (of (a + b) : GrothendieckRing S) = of a + of b :=
  ofHom.map_add a b
@[simp] theorem of_mul (a b : S) : (of (a * b) : GrothendieckRing S) = of a * of b :=
  ofHom.map_mul a b

theorem mk_eq_of_sub_of (a b : S) : mk a b = of a - of b := by
  rw [of, of, mk_sub_mk, add_zero, zero_add]

/-- `of` is injective as soon as `S` is additively cancellative (hypothesis
supplied explicitly to avoid a typeclass detour). -/
theorem of_injective (hc : ∀ a b c : S, a + c = b + c → a = b) :
    Function.Injective (of : S → GrothendieckRing S) := by
  intro a b h
  obtain ⟨k, hk⟩ := mk_eq_mk.mp h
  rw [add_zero, add_zero] at hk
  exact hc a b k hk

section Lift

variable {R : Type*} [CommRing R]

/-- Universal property: a semiring hom `S →+* R` into a commutative ring
extends uniquely to the Grothendieck ring, via `a - b ↦ f a - f b`. -/
def lift (f : S →+* R) : GrothendieckRing S →+* R where
  toFun := Quotient.lift (fun p => f p.1 - f p.2) fun p q => by
    rintro ⟨k, hk⟩
    have h := congrArg f hk
    simp only [map_add] at h
    linear_combination h
  map_zero' := by
    change f 0 - f 0 = 0
    simp
  map_one' := by
    change f 1 - f 0 = 1
    simp
  map_add' a b := by
    refine Quotient.ind₂ (fun p q => ?_) a b
    change f (p.1 + q.1) - f (p.2 + q.2) = (f p.1 - f p.2) + (f q.1 - f q.2)
    simp only [map_add]
    ring
  map_mul' a b := by
    refine Quotient.ind₂ (fun p q => ?_) a b
    change f (p.1 * q.1 + p.2 * q.2) - f (p.1 * q.2 + p.2 * q.1) =
      (f p.1 - f p.2) * (f q.1 - f q.2)
    simp only [map_add, map_mul]
    ring

@[simp] theorem lift_mk (f : S →+* R) (a b : S) : lift f (mk a b) = f a - f b := rfl

@[simp] theorem lift_of (f : S →+* R) (a : S) : lift f (of a) = f a := by
  change f a - f 0 = f a
  simp

/-- Ring homomorphisms out of the Grothendieck ring agree iff they agree on
the image of `of`. -/
theorem hom_ext {f g : GrothendieckRing S →+* R} (h : ∀ a : S, f (of a) = g (of a)) :
    f = g := by
  ext x
  obtain ⟨p⟩ := x
  change f (mk p.1 p.2) = g (mk p.1 p.2)
  rw [mk_eq_of_sub_of, map_sub, map_sub, h, h]

end Lift

section Map

variable {T : Type*} [CommSemiring T]

/-- Functoriality: a semiring hom `S →+* T` induces a ring hom on
Grothendieck rings. -/
def map (f : S →+* T) : GrothendieckRing S →+* GrothendieckRing T :=
  lift (ofHom.comp f)

@[simp] theorem map_of (f : S →+* T) (a : S) : map f (of a) = of (f a) := by
  simp [map]

@[simp] theorem map_mk (f : S →+* T) (a b : S) : map f (mk a b) = mk (f a) (f b) := by
  rw [map, lift_mk, mk_eq_of_sub_of (f a) (f b)]
  rfl

theorem map_id : map (RingHom.id S) = RingHom.id (GrothendieckRing S) :=
  hom_ext fun a => by simp

theorem map_map {U : Type*} [CommSemiring U] (g : T →+* U) (f : S →+* T)
    (x : GrothendieckRing S) : map g (map f x) = map (g.comp f) x := by
  obtain ⟨p⟩ := x
  change map g (map f (mk p.1 p.2)) = map (g.comp f) (mk p.1 p.2)
  simp

end Map

end GrothendieckRing

end LeanDring
