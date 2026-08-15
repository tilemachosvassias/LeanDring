/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.Idempotents

-- Several statements below do not mention the section's `[Fintype _]` /
-- group binders, but their proofs need them for instance synthesis, so the
-- binders cannot be `omit`ted.  The linters' suggested rewrite to `[Finite _]`
-- plus `Fintype.ofFinite` is a genuine refactor, not a cleanup.
set_option linter.unusedSectionVars false

/-!
# Towards Müller Satz 2.8.4: the idempotent core of tensor cancellation

**EVEN-ORDER LAYER.** Inside the root module's build closure and audit:
no `sorry`, three standard axioms. The results here are
verified *implications*; their hypotheses are named `Prop`s (see §7.6 of
the paper).

Müller's Satz 2.8.4 states: if `A₁, A₂, B₁, B₂` are commutative rings, finitely
generated and free as `ℤ`-modules, with `A₁, A₂` having `ℤ`-bases containing
`1`, and if there is a subring `R ⊆ ℂ` such that `R ⊗ Aᵢ` has only the
idempotents `0, 1` and `R ⊗ Bᵢ` is "semisimple", then `A₁ ⊗ B₁ ≅ A₂ ⊗ B₂`
implies `B₁ ≅ B₂`.  It is the cancellation step of Satz 2.8.5, hence of
Theorem MC1 (`LeanDring/Even/CentralSylowTwo.lean`).

## A clarification of the hypothesis (paper: Proposition ``cancellation'',
## with the remark that follows it)

Müller writes `R ⊗ Bᵢ` *halbeinfach* and then immediately uses
`R ⊗ Bᵢ = ⨁ⱼ R eⱼ`.  Over `R = ℤ[ξ]_𝔭` those are different statements, and
the second is the one the proof needs: a commutative ring that is semisimple
is a finite product of *fields*, and a field finite over a domain `R` forces
`R` to be a field — which `ℤ[ξ]_𝔭` is not.  What Satz 2.2.7 actually supplies
is that the primitive idempotents of `D_R(H)` and `D_{ℚ(ξ)}(H)` agree, i.e.
that `R ⊗ Bᵢ` is *split by idempotents*: free with a basis of orthogonal
idempotents summing to `1`, equivalently `R ⊗ Bᵢ ≃ₐ[R] (ι → R)`.  That is the
hypothesis used below, and it is what the application in Satz 2.8.5 provides.

## What this file proves

The first half of the argument, in full and abstractly:

* `isIdempotentElem_pi_iff` — the idempotents of `ι → S` are the pointwise
  `0/1` families, when `S` has only the idempotents `0` and `1`;
* `idempotentEquivSet` — hence they biject with `Set ι`;
* `card_eq_of_algEquiv_pi` — **the `n = m` step of Satz 2.8.4**: if
  `(ι → S₁) ≃+* (κ → S₂)` with both `Sᵢ` idempotent-trivial, then
  `ι` and `κ` have the same cardinality.  Müller derives this by matching
  *primitive* idempotents; counting all of them avoids primitivity entirely;
* `algEquivPiOfTensor` — the identification
  `S ⊗[R] (ι → R) ≃ₐ[R] (ι → S)` that puts the hypothesis of Satz 2.8.4 into
  that shape, via `Algebra.TensorProduct.piRight`;
* `IsPrimitiveIdem`, `IsPrimitiveIdem.map`, `isPrimitiveIdem_pi_iff` — the
  atoms of the idempotent lattice, their transport along an arbitrary ring
  isomorphism, and their identification in `ι → S` as the coordinate
  indicators.  Together these are Müller's "`α̂` matches the primitive
  idempotents `ψ(eᵢ)` with the `ψ̃(ẽᵢ)`", proved rather than asserted.

## What remains

Three steps, in order of expected difficulty:

1. the `R`-span of the primitive idempotents of `ι → S` is the image of
   `ψ`, i.e. the copy of `R ⊗ B` inside `R ⊗ A ⊗ B` — routine;
2. the `ℤ`-descent: if the image of `x ∈ A₂ ⊗ B₂` in `R ⊗ A₂ ⊗ B₂` lies in
   the `R`-span of `{1 ⊗ 1 ⊗ b̃ⱼ}`, then `x` lies in the `ℤ`-span of
   `{1 ⊗ b̃ⱼ}`.  This is where the `ℤ`-basis of `A₂` containing `1` is used,
   and it needs `Basis.baseChange` plumbing over the tensor basis;
3. assembling `β = δ̃⁻¹ ∘ α ∘ δ` and its inverse into a ring isomorphism.

Until these are done Satz 2.8.4 is not available, and
`LeanDring/Even/CentralSylowTwo.lean` continues to type it as a hypothesis.

No `sorry`, no custom axiom.
-/

namespace LeanDring

namespace Even

universe u v w

open scoped TensorProduct

section IdempotentTrivial

variable {S : Type u} [CommRing S]

/-- A ring has *trivial idempotents* if `0` and `1` are its only ones.  For
`S = R ⊗ D(P)` with `P` a `p`-group and `R` local at `p` this is Müller's
Satz 2.2.7. -/
def HasTrivialIdempotents (S : Type u) [CommRing S] : Prop :=
  ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1

variable {ι : Type v}

/-- Idempotents of a product are pointwise idempotents. -/
theorem isIdempotentElem_pi_iff (f : ι → S) :
    IsIdempotentElem f ↔ ∀ i, IsIdempotentElem (f i) := by
  constructor
  · intro h i
    exact congrFun h i
  · intro h
    funext i
    exact h i

/-- With trivial idempotents in `S`, an idempotent of `ι → S` is exactly the
indicator function of a subset of `ι`. -/
theorem isIdempotentElem_pi_iff_of_trivial (hS : HasTrivialIdempotents S)
    (f : ι → S) :
    IsIdempotentElem f ↔ ∀ i, f i = 0 ∨ f i = 1 := by
  rw [isIdempotentElem_pi_iff]
  exact forall_congr' fun i => ⟨fun h => hS _ h, fun h => by
    rcases h with h | h <;> simp [IsIdempotentElem, h]⟩

variable [Nontrivial S]

open scoped Classical in
/-- **The idempotents of `ι → S` biject with the subsets of `ι`**. -/
noncomputable def idempotentEquivSet (hS : HasTrivialIdempotents S) :
    {f : ι → S // IsIdempotentElem f} ≃ Set ι where
  toFun f := {i | f.1 i = 1}
  invFun s := ⟨fun i => if i ∈ s then 1 else 0, by
    refine (isIdempotentElem_pi_iff_of_trivial hS _).mpr fun i => ?_
    by_cases h : i ∈ s <;> simp [h]⟩
  left_inv := by
    rintro ⟨f, hf⟩
    ext i
    by_cases h : f i = 1
    · simp [h]
    · have := ((isIdempotentElem_pi_iff_of_trivial hS f).mp hf i).resolve_right h
      simp [this]
  right_inv := by
    intro s
    ext i
    by_cases h : i ∈ s <;> simp [h, zero_ne_one]

end IdempotentTrivial

section Transport

variable {R : Type u} [CommRing R]
variable {S₁ : Type v} [CommRing S₁] [Algebra R S₁] [Nontrivial S₁]
variable {S₂ : Type w} [CommRing S₂] [Algebra R S₂] [Nontrivial S₂]
variable {ι κ : Type} [Finite ι] [Finite κ]

/-- A ring isomorphism carries idempotents to idempotents, bijectively. -/
noncomputable def idempotentCongr {X Y : Type*} [CommRing X] [CommRing Y]
    (Φ : X ≃+* Y) :
    {x : X // IsIdempotentElem x} ≃ {y : Y // IsIdempotentElem y} where
  toFun x := ⟨Φ x.1, by
    have := x.2
    unfold IsIdempotentElem at this ⊢
    rw [← map_mul, this]⟩
  invFun y := ⟨Φ.symm y.1, by
    have := y.2
    unfold IsIdempotentElem at this ⊢
    rw [← map_mul, this]⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp

/-- **The `n = m` step of Satz 2.8.4 [PROVEN]**.  If two split algebras over
idempotent-trivial coefficient rings are isomorphic as rings, their index sets
have the same size.

Müller argues through primitive idempotents; counting *all* idempotents —
`2^{|ι|}` of them on each side — is shorter and avoids having to characterize
primitivity ring-theoretically. -/
theorem card_eq_of_algEquiv_pi (h₁ : HasTrivialIdempotents S₁)
    (h₂ : HasTrivialIdempotents S₂) (Φ : (ι → S₁) ≃+* (κ → S₂)) :
    Nat.card ι = Nat.card κ := by
  have e : Set ι ≃ Set κ :=
    ((idempotentEquivSet (ι := ι) h₁).symm.trans (idempotentCongr Φ)).trans
      (idempotentEquivSet (ι := κ) h₂)
  have hcard : Nat.card (Set ι) = Nat.card (Set κ) := Nat.card_congr e
  haveI : Fintype ι := Fintype.ofFinite ι
  haveI : Fintype κ := Fintype.ofFinite κ
  rw [Nat.card_eq_fintype_card (α := Set ι), Nat.card_eq_fintype_card (α := Set κ),
    Fintype.card_set, Fintype.card_set] at hcard
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Nat.pow_right_injective (le_refl 2) hcard

end Transport


/-! ## Primitive idempotents, and their transport -/

section Primitive

variable {X : Type u} [CommRing X]

/-- `e` is a *primitive* idempotent: nonzero, and not properly dominated by a
nonzero idempotent.  The relation `f * e = f` is the Boolean order `f ≤ e`,
so this is "atom of the idempotent lattice", stated equationally — which is
what makes it transportable along any ring isomorphism. -/
def IsPrimitiveIdem (e : X) : Prop :=
  IsIdempotentElem e ∧ e ≠ 0 ∧ ∀ f : X, IsIdempotentElem f → f * e = f → f = 0 ∨ f = e

/-- **[PROVEN]** Primitivity is a ring-theoretic property: it transports along
any ring isomorphism.  This replaces the appeal to "the primitive idempotents
correspond" in Müller's proof. -/
theorem IsPrimitiveIdem.map {Y : Type v} [CommRing Y] (Φ : X ≃+* Y) {e : X}
    (he : IsPrimitiveIdem e) : IsPrimitiveIdem (Φ e) := by
  obtain ⟨hidem, hne, hmin⟩ := he
  refine ⟨?_, ?_, ?_⟩
  · unfold IsIdempotentElem at hidem ⊢
    rw [← map_mul, hidem]
  · intro h
    apply hne
    have := congrArg Φ.symm h
    simpa using this
  · intro f hf hfe
    have hf' : IsIdempotentElem (Φ.symm f) := by
      unfold IsIdempotentElem at hf ⊢
      rw [← map_mul, hf]
    have : Φ.symm f * e = Φ.symm f := by
      have := congrArg Φ.symm hfe
      simpa using this
    rcases hmin _ hf' this with h | h
    · exact Or.inl (by simpa using congrArg Φ h)
    · exact Or.inr (by simpa using congrArg Φ h)

end Primitive

section PrimitivePi


variable {S : Type u} [CommRing S] [Nontrivial S] {ι : Type} [DecidableEq ι]

/-- The coordinate indicator at `i`. -/
def coordIdem (i : ι) : ι → S := fun j => if j = i then 1 else 0

theorem isIdempotentElem_coordIdem (i : ι) : IsIdempotentElem (coordIdem (S := S) i) := by
  funext j
  by_cases h : j = i <;> simp [coordIdem, h]

/-- **[PROVEN]** In `ι → S` with `S` idempotent-trivial, the primitive
idempotents are exactly the coordinate indicators.  This is the statement
Müller uses to identify `1 ⊗ eᵢ` as the primitive idempotents of
`(R ⊗ A) ⊗_R (R ⊗ B)`. -/
theorem isPrimitiveIdem_pi_iff (hS : HasTrivialIdempotents S) (f : ι → S) :
    IsPrimitiveIdem f ↔ ∃ i, f = coordIdem i := by
  constructor
  · rintro ⟨hidem, hne, hmin⟩
    have hval := (isIdempotentElem_pi_iff_of_trivial hS f).mp hidem
    obtain ⟨i, hi⟩ : ∃ i, f i = 1 := by
      by_contra hcon
      have h : ∀ i, f i ≠ 1 := fun i hi => hcon ⟨i, hi⟩
      exact hne (funext fun i => (hval i).resolve_right (h i))
    refine ⟨i, ?_⟩
    have hle : coordIdem (S := S) i * f = coordIdem i := by
      funext j
      by_cases hj : j = i <;> simp [coordIdem, hj, hi]
    rcases hmin (coordIdem i) (isIdempotentElem_coordIdem i) hle with h | h
    · exact absurd (congrFun h i) (by simp [coordIdem, one_ne_zero])
    · exact h.symm
  · rintro ⟨i, rfl⟩
    refine ⟨isIdempotentElem_coordIdem i, ?_, ?_⟩
    · intro h
      exact one_ne_zero (α := S) (by simpa [coordIdem] using congrFun h i)
    · intro g hg hgi
      have hval := (isIdempotentElem_pi_iff_of_trivial hS g).mp hg
      by_cases hgi1 : g i = 1
      · right
        funext j
        by_cases hj : j = i
        · simp [coordIdem, hj, hgi1]
        · have := congrFun hgi j
          simp [coordIdem, hj] at this
          simp [coordIdem, hj, this]
      · left
        funext j
        by_cases hj : j = i
        · subst hj
          exact (hval j).resolve_right hgi1
        · have := congrFun hgi j
          simp [coordIdem, hj] at this
          simp [this]

end PrimitivePi

section Split

variable (R : Type u) [CommRing R]
variable (S : Type v) [CommRing S] [Algebra R S]
variable (ι : Type) [Fintype ι] [DecidableEq ι]

/-- The shape change of Satz 2.8.4's proof: base change of a split algebra is
split.  `S ⊗[R] (ι → R) ≃ₐ[R] (ι → S)`, so the hypothesis
`R ⊗ Bᵢ ≃ₐ[R] (ι → R)` turns `(R ⊗ Aᵢ) ⊗_R (R ⊗ Bᵢ)` into `ι → (R ⊗ Aᵢ)`,
where the previous section applies. -/
noncomputable def algEquivPiOfTensor : S ⊗[R] (ι → R) ≃ₐ[R] (ι → S) :=
  (Algebra.TensorProduct.piRight R R S (fun _ : ι => R)).trans
    (AlgEquiv.piCongrRight fun _ => Algebra.TensorProduct.rid R R S)

end Split

end Even

end LeanDring

/-! ## Axiom audit -/

#print axioms LeanDring.Even.isIdempotentElem_pi_iff_of_trivial
#print axioms LeanDring.Even.idempotentEquivSet
#print axioms LeanDring.Even.card_eq_of_algEquiv_pi
#print axioms LeanDring.Even.IsPrimitiveIdem.map
#print axioms LeanDring.Even.isPrimitiveIdem_pi_iff
#print axioms LeanDring.Even.algEquivPiOfTensor
