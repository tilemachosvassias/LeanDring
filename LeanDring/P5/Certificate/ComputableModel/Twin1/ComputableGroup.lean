/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Presentation.Presentation
import Mathlib.Algebra.Group.MinimalAxioms

/-!
# A kernel-computable group on the order-`5^5` coordinate space

`LeanDring/P5/Certificate/Presentation/Presentation.lean` supplies, for `q ∈ {1,2}` (the
presentations of
`SmallGroup(3125,68)` and `(3125,69)`), a certified bijective normal form
`normalForm q : Coordinates → Group q` together with the five executable
right-multiplication steps `step q i` (each proven to agree with multiplication
by the pc generator `gen q i`, `normalForm_step`).

Here we assemble those steps into a **computable** group structure on
`Coordinates`, installed on a type synonym `Coordinate q` (to keep its instances
disjoint from the ambient `Fin 5`-product instances):

* `mulC q x y` right-multiplies `x` by the pc word spelling `y` — the composite
  of the five iterated steps — and
  `normalForm_mulC : normalForm q (mulC q x y) = normalForm q x * normalForm q y`.
* `invC q x` is the descending inverse sweep, and
  `normalForm_invC : normalForm q (invC q x) = (normalForm q x)⁻¹`.
* `instance Group (Coordinate q)` (for `q = 1, 2`), built by `Group.ofLeftAxioms`
  from the three group laws, each proved by **transport** along the injective
  `normalForm` — `mulC` remains the literal (kernel-reducible) multiplication.
* `normalFormMulEquiv q hq : Coordinate q ≃* Group q`.
* `DecidableEq` / `Fintype (Coordinate q)`, inherited from the coordinate space,
  making membership, products and inverses kernel-decidable.

Nothing here is `noncomputable` except the `MulEquiv` (which packages the
`noncomputable` normal-form bijection); the group operations themselves reduce
in the kernel, as the closing `decide` smoke tests witness.
-/

namespace LeanDring.P5Presentation

/-! ## Iterating a single step -/

/-- Iterating the `i`-th collection step `n` times right-multiplies by
`gen q i ^ n`. -/
theorem normalForm_iterate_step (q : ℕ) (i : Gen) (n : ℕ) (x : Coordinates) :
    normalForm q ((step q i)^[n] x) = normalForm q x * gen q i ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', normalForm_step, ih, mul_assoc, ← pow_succ]

/-- Iterating the `i`-th inverse step `n` times right-multiplies by
`(gen q i ^ n)⁻¹`. -/
theorem normalForm_iterate_stepInv (q : ℕ) (i : Gen) (n : ℕ) (x : Coordinates) :
    normalForm q ((stepInv q i)^[n] x) = normalForm q x * (gen q i ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', normalForm_stepInv, ih, mul_assoc,
        ← mul_inv_rev, ← pow_succ']

/-! ## Computable multiplication -/

/-- Computable right multiplication: `mulC q x y` applies to `x`, in
normal-form order, the iterated steps spelling `y`'s pc word
`g₀^a g₁^b g₂^c g₃^d g₄^e`. -/
def mulC (q : ℕ) (x y : Coordinates) : Coordinates :=
  (step q 4)^[(y.2.2.2.2 : ℕ)]
    ((step q 3)^[(y.2.2.2.1 : ℕ)]
      ((step q 2)^[(y.2.2.1 : ℕ)]
        ((step q 1)^[(y.2.1 : ℕ)]
          ((step q 0)^[(y.1 : ℕ)] x))))

/-- **Multiplication bridge.** `mulC` realizes multiplication in the presented
group through the normal form. -/
theorem normalForm_mulC (q : ℕ) (x y : Coordinates) :
    normalForm q (mulC q x y) = normalForm q x * normalForm q y := by
  obtain ⟨a, b, c, d, e⟩ := y
  simp only [mulC]
  rw [normalForm_iterate_step, normalForm_iterate_step, normalForm_iterate_step,
    normalForm_iterate_step, normalForm_iterate_step]
  simp only [normalForm, mul_assoc]

/-! ## Computable inverse -/

/-- Computable inverse: the descending inverse sweep applied to the identity
coordinate spells `(g₀^a g₁^b g₂^c g₃^d g₄^e)⁻¹`. -/
def invC (q : ℕ) (x : Coordinates) : Coordinates :=
  (stepInv q 0)^[(x.1 : ℕ)]
    ((stepInv q 1)^[(x.2.1 : ℕ)]
      ((stepInv q 2)^[(x.2.2.1 : ℕ)]
        ((stepInv q 3)^[(x.2.2.2.1 : ℕ)]
          ((stepInv q 4)^[(x.2.2.2.2 : ℕ)] (0, 0, 0, 0, 0)))))

/-- **Inversion bridge.** `invC` realizes inversion in the presented group
through the normal form. -/
theorem normalForm_invC (q : ℕ) (x : Coordinates) :
    normalForm q (invC q x) = (normalForm q x)⁻¹ := by
  obtain ⟨a, b, c, d, e⟩ := x
  simp only [invC]
  rw [normalForm_iterate_stepInv, normalForm_iterate_stepInv, normalForm_iterate_stepInv,
    normalForm_iterate_stepInv, normalForm_iterate_stepInv, normalForm_zero, one_mul]
  conv_rhs => rw [normalForm]
  group

/-! ## The three group laws, by transport along `normalForm` -/

theorem mulC_assoc (q : ℕ) (hq : q = 1 ∨ q = 2) (x y z : Coordinates) :
    mulC q (mulC q x y) z = mulC q x (mulC q y z) := by
  apply normalForm_injective q hq
  simp only [normalForm_mulC, mul_assoc]

theorem one_mulC (q : ℕ) (hq : q = 1 ∨ q = 2) (x : Coordinates) :
    mulC q (0, 0, 0, 0, 0) x = x := by
  apply normalForm_injective q hq
  rw [normalForm_mulC, normalForm_zero, one_mul]

theorem invC_mulC (q : ℕ) (hq : q = 1 ∨ q = 2) (x : Coordinates) :
    mulC q (invC q x) x = (0, 0, 0, 0, 0) := by
  apply normalForm_injective q hq
  rw [normalForm_mulC, normalForm_invC, normalForm_zero, inv_mul_cancel]

/-! ## The computable group wrapper -/

/-- Type synonym for the coordinate space, carrying the presentation
parameter `q`. Being a `def` (not `abbrev`) it does **not** inherit the ambient
`Fin 5`-product algebraic instances, so we may install the presented-group
structure on it without clashes, while `DecidableEq`/`Fintype` are transported
back explicitly. -/
def Coordinate (_q : ℕ) : Type := Coordinates

instance (q : ℕ) : DecidableEq (Coordinate q) :=
  inferInstanceAs (DecidableEq Coordinates)

instance (q : ℕ) : Fintype (Coordinate q) :=
  inferInstanceAs (Fintype Coordinates)

instance (q : ℕ) : Mul (Coordinate q) := ⟨mulC q⟩

instance (q : ℕ) : One (Coordinate q) := ⟨(0, 0, 0, 0, 0)⟩

instance (q : ℕ) : Inv (Coordinate q) := ⟨invC q⟩

/-- The computable presented-group structure on `Coordinate q`, for either
target parameter `q ∈ {1,2}`. The multiplication is definitionally `mulC q`
(kernel-reducible); the group axioms are transported along the injective
normal form. -/
@[reducible] def coordinateGroup (q : ℕ) (hq : q = 1 ∨ q = 2) : _root_.Group (Coordinate q) :=
  _root_.Group.ofLeftAxioms (mulC_assoc q hq) (one_mulC q hq) (invC_mulC q hq)

instance : _root_.Group (Coordinate 1) := coordinateGroup 1 (Or.inl rfl)

instance : _root_.Group (Coordinate 2) := coordinateGroup 2 (Or.inr rfl)

/-- The normal form as a **multiplicative** equivalence `Coordinate q ≃* Group q`
for either target parameter. Packages the (`noncomputable`) normal-form
bijection with the `mulC` multiplication bridge. -/
noncomputable def normalFormMulEquiv (q : ℕ) (hq : q = 1 ∨ q = 2) :
    Coordinate q ≃* Group q :=
  { (Equiv.ofBijective (normalForm q) (normalForm_bijective q hq) :
        Coordinate q ≃ Group q) with
    map_mul' := fun x y => normalForm_mulC q x y }

@[simp] theorem normalFormMulEquiv_apply (q : ℕ) (hq : q = 1 ∨ q = 2)
    (x : Coordinate q) : normalFormMulEquiv q hq x = normalForm q x := rfl

/-- Convenience: the computable model of `SmallGroup(3125,68)`. -/
noncomputable def coordinateMulEquiv68 : Coordinate 1 ≃* G68 :=
  normalFormMulEquiv 1 (Or.inl rfl)

/-- Convenience: the computable model of `SmallGroup(3125,69)`. -/
noncomputable def coordinateMulEquiv69 : Coordinate 2 ≃* G69 :=
  normalFormMulEquiv 2 (Or.inr rfl)

/-! ## Kernel smoke tests (small `decide`, no `native_decide`) -/

-- A concrete inverse computed in the kernel.
example : invC 1 (1, 0, 0, 0, 0) = (4, 0, 0, 0, 0) := by decide

-- `invC` is a genuine right inverse for `mulC`, for each parameter.
example : mulC 1 (invC 1 (1, 2, 3, 4, 2)) (1, 2, 3, 4, 2) = (0, 0, 0, 0, 0) := by decide

example : mulC 2 (invC 2 (2, 1, 3, 0, 4)) (2, 1, 3, 0, 4) = (0, 0, 0, 0, 0) := by decide

-- Associativity of `mulC` on a concrete triple.
example :
    mulC 1 (mulC 1 (1, 1, 0, 0, 0) (0, 1, 1, 0, 0)) (0, 0, 1, 1, 0) =
      mulC 1 (1, 1, 0, 0, 0) (mulC 1 (0, 1, 1, 0, 0) (0, 0, 1, 1, 0)) := by decide

-- The wrapper's group operations reduce in the kernel through the instances.
-- (Every operand is ascribed to `Coordinate 1` so `*`/`⁻¹`/`1` use the presented
-- group's instances, not the ambient `Fin 5`-product ones.)
example :
    @Mul.mul (Coordinate 1) _ (invC 1 (1, 0, 0, 0, 0)) (1, 0, 0, 0, 0)
      = ((0, 0, 0, 0, 0) : Coordinate 1) := by
  decide

end LeanDring.P5Presentation
