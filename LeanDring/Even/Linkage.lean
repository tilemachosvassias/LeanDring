/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Ring.Pi

/-!
# Linkage canonicity (L1) and the intrinsic fused-rational quotient (AL0),
# formalized against arbitrary ring isomorphisms

**EVEN-ORDER LAYER.** No `sorry`, three standard axioms.

This is the native-Lean formalization of the *canonicity half* of the
linkage program (the L1/L2 separation and the AL0 abelian law), stated
for an arbitrary commutative ring `D` so that **every statement is
transported by construction**: the failure mode "canonical ≠ preserved by an abstract ring
isomorphism" is unrepresentable here, because the only data available is a ring
isomorphism `Φ: D ≃+* D'`.

Specialized to `D = D(G)`, the integer points `D →+* ℤ` are exactly the
fused-rational species (AL0; for odd order they are exactly the marks —
`OddOrder.AllIntegerPointsAreMarks`), and:

* `intPointEquiv` — a ring isomorphism induces a bijection of integer
  points (contravariantly, by precomposition);
* `linkSubgroup φ ψ` — the linkage subgroup `(φ − ψ)(D) ⊆ ℤ`; its 2-adic
 valuation is the linkage exponent `ℓ(p,q)`;
* `linkSubgroup_intPointEquiv` / `exists_linkPreserving_bijection` —
  **L1 canonicity**: the induced bijection preserves every linkage
  subgroup on the nose, so the pair-linkage data is a ring-isomorphism
  invariant — any mismatch refutes `D ≅ D'`;
* `sumLinkSubgroup` — higher-arity linkage `ℓ(S)` (the An4 beacon
  invariant), same canonicity;
* `ratKernel` / `DF` / `dfCongr` — **AL0**: the common kernel of all
  integer points is intrinsic, so the fused-rational quotient `D_F` is an
  intrinsic quotient of `D` and every ring isomorphism descends;
* `ghost` / `dfEquivGhostRange` — `D_F` is the ghost lattice: the image of
  `D` in `∏_{φ} ℤ`, the object all linkage computations live on;
* `ghostRangeAutoOfPreserving` — **the L1 mechanism**: a permutation of
  the integer points whose reindexing preserves the ghost lattice induces
  a ring automorphism of the lattice ("lattice-preserving coordinate
  permutations are automatically ring automorphisms", the load-bearing
  step of Criterion T).

## Criterion T proper

For a full lattice `L ⊆ ℤ^F` of 2-power index, a coordinate transposition
`τ_{pq}` preserves `L` iff `ℓ(p,q) ≥ ℓ∨(p,q)` where `ℓ∨` is the dual
linkage read off the rows of `S⁻¹` (Criterion T, hand-proven and
audited). The forward mechanism is
`ghostRangeAutoOfPreserving`; the valuation criterion needs the dual
lattice `L^∨ ⊆ ℚ^F`, and is proved in `LeanDring/Even/CriterionT.lean`
(`swap_preserves_iff`) — there with no index, finiteness or rank
hypothesis at all.
-/

namespace LeanDring

namespace Even

variable {D : Type*} [CommRing D] {D' : Type*} [CommRing D']

/-- An **integer point** of `D`: a ring homomorphism `D →+* ℤ`. For
`D = D(G)` these are exactly the fused-rational species (AL0). -/
abbrev IntPoint (D : Type*) [CommRing D] : Type _ := D →+* ℤ

/-- A ring isomorphism induces a bijection of integer points, by
precomposition (contravariant). -/
def intPointEquiv (Φ : D ≃+* D') : IntPoint D' ≃ IntPoint D where
  toFun φ := φ.comp (Φ : D →+* D')
  invFun ψ := ψ.comp (Φ.symm : D' →+* D)
  left_inv φ := by ext y; simp
  right_inv ψ := by ext x; simp

@[simp] theorem intPointEquiv_apply (Φ : D ≃+* D') (φ : IntPoint D')
    (x : D) : intPointEquiv Φ φ x = φ (Φ x) := rfl

/-- The difference of two integer points, as an additive map `D →+ ℤ`. -/
def diffHom (φ ψ : IntPoint D) : D →+ ℤ :=
  φ.toAddMonoidHom - ψ.toAddMonoidHom

@[simp] theorem diffHom_apply (φ ψ : IntPoint D) (x : D) :
    diffHom φ ψ x = φ x - ψ x := rfl

/-- The **linkage subgroup** of a pair of integer points: the subgroup
`(φ − ψ)(D) ⊆ ℤ`. Its 2-adic valuation is the linkage exponent
`ℓ(p,q) = v₂(gcd_x (φ(x) − ψ(x)))`; keeping
the subgroup itself avoids choosing a generator. -/
def linkSubgroup (φ ψ : IntPoint D) : AddSubgroup ℤ :=
  (diffHom φ ψ).range

theorem mem_linkSubgroup {φ ψ : IntPoint D} {n : ℤ} :
    n ∈ linkSubgroup φ ψ ↔ ∃ x : D, φ x - ψ x = n := by
  simp [linkSubgroup, AddMonoidHom.mem_range]

/-- Linkage is symmetric in the pair. -/
theorem linkSubgroup_comm (φ ψ : IntPoint D) :
    linkSubgroup φ ψ = linkSubgroup ψ φ := by
  ext n
  rw [mem_linkSubgroup, mem_linkSubgroup]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨-x, by rw [map_neg, map_neg]; ring⟩
  · rintro ⟨x, rfl⟩
    exact ⟨-x, by rw [map_neg, map_neg]; ring⟩

/-- **L1 canonicity, pointwise form**: the bijection of integer points
induced by a ring isomorphism preserves every linkage subgroup on the
nose. No basis, no transport hypothesis — the statement survives any
abstract ring isomorphism by construction. -/
theorem linkSubgroup_intPointEquiv (Φ : D ≃+* D') (φ ψ : IntPoint D') :
    linkSubgroup (intPointEquiv Φ φ) (intPointEquiv Φ ψ) =
      linkSubgroup φ ψ := by
  ext n
  rw [mem_linkSubgroup, mem_linkSubgroup]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Φ x, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨Φ.symm y, by simp⟩

/-- **The separation principle** (L1 packaged): a ring isomorphism induces
a bijection of integer points preserving all pairwise linkage — so any
mismatch in the pair-linkage data of `D` and `D'` refutes `D ≅ D'`. This
is the formal license behind the linkage separations
(`B(64,13) ≇ B(64,14)`, `D_F(64,13) ≇ D_F(64,14)`, the (128,96/97)
resolution). -/
theorem exists_linkPreserving_bijection (Φ : D ≃+* D') :
    ∃ e : IntPoint D' ≃ IntPoint D,
      ∀ φ ψ : IntPoint D', linkSubgroup (e φ) (e ψ) = linkSubgroup φ ψ :=
  ⟨intPointEquiv Φ, linkSubgroup_intPointEquiv Φ⟩

/-- The sum of a finite set of integer points, as an additive map. -/
def sumHom (s : Finset (IntPoint D)) : D →+ ℤ where
  toFun x := ∑ φ ∈ s, φ x
  map_zero' := by simp
  map_add' x y := by
    simp only [map_add]
    exact Finset.sum_add_distrib

@[simp] theorem sumHom_apply (s : Finset (IntPoint D)) (x : D) :
    sumHom s x = ∑ φ ∈ s, φ x := rfl

/-- **Higher-arity linkage** `ℓ(S)`: the subgroup of values of the
coordinate sum over `S` (the An4 beacon invariant). -/
def sumLinkSubgroup (s : Finset (IntPoint D)) : AddSubgroup ℤ :=
  (sumHom s).range

/-- Higher-arity linkage is transported by the induced bijection of
integer points — same canonicity mechanism as L1. -/
theorem sumLinkSubgroup_map (Φ : D ≃+* D') (s : Finset (IntPoint D')) :
    sumLinkSubgroup (s.map (intPointEquiv Φ).toEmbedding) =
      sumLinkSubgroup s := by
  ext n
  simp only [sumLinkSubgroup, AddMonoidHom.mem_range, sumHom_apply,
    Finset.sum_map, Equiv.coe_toEmbedding, intPointEquiv_apply]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Φ x, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨Φ.symm y, by simp⟩

/-- The **fused-rational kernel**: the common kernel of all integer
points. AL0: this ideal is defined from the abstract ring alone. -/
def ratKernel (D : Type*) [CommRing D] : Ideal D :=
  ⨅ φ : IntPoint D, RingHom.ker φ

theorem mem_ratKernel {x : D} :
    x ∈ ratKernel D ↔ ∀ φ : IntPoint D, φ x = 0 := by
  simp [ratKernel, RingHom.mem_ker]

/-- **AL0, transport (comap form)**: the fused-rational kernel is
intrinsic. -/
theorem ratKernel_comap (Φ : D ≃+* D') :
    (ratKernel D').comap (Φ : D →+* D') = ratKernel D := by
  ext x
  rw [Ideal.mem_comap, mem_ratKernel, mem_ratKernel]
  constructor
  · intro h φ
    have h1 := h (φ.comp (Φ.symm : D' →+* D))
    simpa using h1
  · intro h φ'
    exact h (φ'.comp (Φ : D →+* D'))

/-- **AL0, transport (map form)**. -/
theorem ratKernel_map (Φ : D ≃+* D') :
    (ratKernel D).map (Φ : D →+* D') = ratKernel D' := by
  rw [← ratKernel_comap Φ]
  exact Ideal.map_comap_of_surjective _ Φ.surjective _

/-- The **fused-rational quotient** `D_F` — an intrinsic quotient of `D`
(AL0). For `D = D(G)` this is the fused-rational
species quotient. -/
abbrev DF (D : Type*) [CommRing D] := D ⧸ ratKernel D

/-- **AL0, packaged**: every ring isomorphism descends to the
fused-rational quotients. -/
noncomputable def dfCongr (Φ : D ≃+* D') : DF D ≃+* DF D' :=
  Ideal.quotientEquiv _ _ Φ (ratKernel_map Φ).symm

/-- The **total integer ghost map**: `D → ∏_{φ} ℤ`, evaluation at every
integer point. -/
def ghost (D : Type*) [CommRing D] : D →+* (IntPoint D → ℤ) :=
  RingHom.pi fun φ => φ

@[simp] theorem ghost_apply (x : D) (φ : IntPoint D) :
    ghost D x φ = φ x := rfl

theorem ker_ghost (D : Type*) [CommRing D] :
    RingHom.ker (ghost D) = ratKernel D := by
  ext x
  rw [RingHom.mem_ker, mem_ratKernel]
  constructor
  · intro h φ
    exact congrFun h φ
  · intro h
    funext φ
    exact h φ

/-- `D_F` **is the ghost lattice**: the fused-rational quotient embeds as
the image of `D` in `∏_{φ} ℤ` — the object all linkage computations live
on. -/
noncomputable def dfEquivGhostRange (D : Type*) [CommRing D] :
    DF D ≃+* (ghost D).range :=
  (Ideal.quotEquivOfEq (ker_ghost D).symm).trans
    (RingHom.quotientKerEquivRange (ghost D))

/-- Reindexing the ghost coordinate space along a permutation of the
integer points. -/
def reindex (e : IntPoint D ≃ IntPoint D) :
    (IntPoint D → ℤ) ≃+* (IntPoint D → ℤ) where
  toFun f := f ∘ e.symm
  invFun f := f ∘ e
  left_inv f := by ext φ; simp
  right_inv f := by ext φ; simp
  map_add' f g := rfl
  map_mul' f g := rfl

@[simp] theorem reindex_apply (e : IntPoint D ≃ IntPoint D)
    (f : IntPoint D → ℤ) (φ : IntPoint D) :
    reindex e f φ = f (e.symm φ) := rfl

/-- **The L1 mechanism** ("lattice-preserving coordinate permutations are
automatically ring automorphisms", the load-bearing step of Criterion T):
a permutation of the integer points whose reindexing maps the ghost
lattice onto itself induces a ring automorphism of the lattice, hence of
`D_F`. -/
noncomputable def ghostRangeAutoOfPreserving (e : IntPoint D ≃ IntPoint D)
    (hpres : ((ghost D).range).map (reindex e : _ →+* _) = (ghost D).range) :
    (ghost D).range ≃+* (ghost D).range :=
  (Subring.equivMapOfInjective ((ghost D).range) (reindex e : _ →+* _)
      (reindex e).injective).trans
    (RingEquiv.subringCongr hpres)

end Even

end LeanDring
