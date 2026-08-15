/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.Exponent
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.ZMod.QuotientGroup

/-!
# The hyperplane count for finite abelian groups of exponent `5`

The self-contained, reusable counting core behind `NormalIndexFiveClosed`, the
sharp form of the Frattini-closure fact that makes the 676-subgroup inventory of
the order-`5⁵` groups provably complete. Two theorems:

* `card_prime_order_subgroups` — in *any* finite group `P` whose exponent divides
  a prime `p`, the number of subgroups of order `p` is `(|P| - 1)/(p - 1)`
  (stated multiplicatively, `(p - 1) * N = |P| - 1`). The nontrivial elements
  partition into the order-`p` subgroups, each contributing `p - 1` generators.

* `card_index_five_subgroups` — for a finite **abelian** group `Q` of exponent
  dividing `5`, the number of **index-`5`** subgroups is `(|Q| - 1)/4`. The
  order-reversing duality `Subgroup Q ≃o (Subgroup (Q →* ℂˣ))ᵒᵈ`
  (`CommGroup.subgroupOrderIsoSubgroupMonoidHom`) turns index-`5` subgroups of `Q`
  into order-`5` subgroups of the (equinumerous, equal-exponent) dual `Q →* ℂˣ`,
  where the first theorem applies.

`card_index_five_subgroups` is exactly the count the Frattini-certification
pipeline needs for the Frattini quotient `Q = H ⧸ Φ(H)`: an index-`5` subgroup of
`H` containing `Φ(H)` is a hyperplane of that quotient, so the count bounds how
many maximal subgroups `H` can have.
-/

namespace LeanDring.P5Presentation

open scoped Pointwise

/-! ## A finite-type nonidentity count -/

/-- The number of elements different from a fixed `a` in a finite type is
`|α| - 1`. -/
theorem card_ne_eq {α : Type*} [Finite α] (a : α) :
    Nat.card {x : α // x ≠ a} = Nat.card α - 1 := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  have h := Fintype.card_subtype_compl (α := α) (p := fun x => x = a)
  rw [Fintype.card_subtype_eq a] at h
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact h

/-! ## The order-`p` subgroup count -/

/-- **The order-`p` subgroup count.** In a finite group `P` all of whose elements
have order dividing a prime `p` (`Monoid.exponent P ∣ p`), the nontrivial elements
partition into the subgroups of order `p`, each with exactly `p - 1` generators;
hence `(p - 1) · #{order-`p` subgroups} = |P| - 1`. -/
theorem card_prime_order_subgroups {P : Type*} [Group P] [Finite P] {p : ℕ}
    [Fact p.Prime] (hexp : Monoid.exponent P ∣ p) :
    (p - 1) * Nat.card {K : Subgroup P // Nat.card K = p} = Nat.card P - 1 := by
  classical
  haveI : Fintype P := Fintype.ofFinite P
  -- Every nontrivial element has order exactly `p`.
  have horder : ∀ x : P, x ≠ 1 → orderOf x = p := by
    intro x hx
    have hdvd : orderOf x ∣ p := dvd_trans (Monoid.order_dvd_exponent x) hexp
    rcases (Nat.dvd_prime (Fact.out (p := p.Prime))).mp hdvd with h1 | hp
    · exact absurd (orderOf_eq_one_iff.mp h1) hx
    · exact hp
  -- Order-`p` subgroups of `P`, and the "generator" map from nontrivial elements.
  set S := {K : Subgroup P // Nat.card K = p} with hS
  let f : {x : P // x ≠ 1} → S :=
    fun x => ⟨Subgroup.zpowers x.1, by rw [Nat.card_zpowers, horder x.1 x.2]⟩
  -- The fiber over `K` is the `p - 1` nontrivial elements of `K`.
  have hfiber : ∀ K : S, Nat.card {x : {x : P // x ≠ 1} // f x = K} = p - 1 := by
    intro K
    have hKcard : Nat.card (K.1 : Subgroup P) = p := K.2
    -- fiber ≃ nontrivial elements of the subgroup `K.1`
    have e : {x : {x : P // x ≠ 1} // f x = K} ≃ {y : (K.1 : Subgroup P) // y ≠ 1} := by
      refine
        { toFun := fun x => ⟨⟨x.1.1, ?_⟩, ?_⟩
          invFun := fun y => ⟨⟨y.1.1, ?_⟩, ?_⟩
          left_inv := ?_
          right_inv := ?_ }
      · -- `x.1.1 ∈ K.1` since `zpowers x.1.1 = K.1`
        have hz : Subgroup.zpowers x.1.1 = K.1 := congrArg Subtype.val x.2
        rw [← hz]; exact Subgroup.mem_zpowers _
      · -- `x.1.1 ≠ 1` as an element of `K.1`
        exact fun h => x.1.2 (congrArg Subtype.val h)
      · -- `y.1.1 ≠ 1` in `P`
        exact fun h => y.2 (Subtype.ext h)
      · -- `f ⟨y.1.1, _⟩ = K`
        apply Subtype.ext
        change Subgroup.zpowers (y.1.1 : P) = K.1
        have hle : Subgroup.zpowers (y.1.1 : P) ≤ K.1 := by
          rw [Subgroup.zpowers_le]; exact y.1.2
        have hne : (y.1.1 : P) ≠ 1 := fun h => y.2 (Subtype.ext h)
        have hcz : Nat.card (Subgroup.zpowers (y.1.1 : P)) = p := by
          rw [Nat.card_zpowers, horder _ hne]
        exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcz, hKcard])
      · intro x; rfl
      · intro y; rfl
    rw [Nat.card_congr e, card_ne_eq (1 : (K.1 : Subgroup P)), hKcard]
  -- Sum the fibers.
  have hsig : Nat.card {x : P // x ≠ 1} = ∑ _K : S, (p - 1) := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
    exact Finset.sum_congr rfl (fun K _ => hfiber K)
  rw [card_ne_eq (1 : P)] at hsig
  rw [hsig, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, smul_eq_mul,
    Nat.mul_comm]

/-! ## The index-`5` count via duality -/

open CommGroup in
/-- **The index-`5` hyperplane count.** For a finite abelian group `Q` of exponent
dividing `5`, the number of index-`5` subgroups is `(|Q| - 1)/4`
(as `4 · N = |Q| - 1`). The order-reversing duality
`Subgroup Q ≃o (Subgroup (Q →* ℂˣ))ᵒᵈ` sends an index-`5` subgroup of `Q` to an
order-`5` subgroup of the equinumerous, equal-exponent dual `Q →* ℂˣ`, where
`card_prime_order_subgroups` counts them. -/
theorem card_index_five_subgroups (Q : Type*) [CommGroup Q] [Finite Q]
    (hexp : Monoid.exponent Q ∣ 5) :
    4 * Nat.card {H : Subgroup Q // Nat.card (Q ⧸ H) = 5} = Nat.card Q - 1 := by
  classical
  haveI : Fintype Q := Fintype.ofFinite Q
  -- Enough roots of unity in ℂ for the exponent of `Q`.
  haveI : NeZero ((Monoid.exponent Q : ℂ)) :=
    ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite⟩
  haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent Q) :=
    IsSepClosed.hasEnoughRootsOfUnity ℂ _
  -- The dual group `D = Q →* ℂˣ`.
  set D := Q →* ℂˣ with hD
  haveI : Finite D := by
    have : Nat.card D = Nat.card Q := card_monoidHom_of_hasEnoughRootsOfUnity Q ℂ
    exact Nat.finite_of_card_ne_zero (by rw [this]; exact Nat.card_pos.ne')
  -- `|D| = |Q|`.
  have hcardD : Nat.card D = Nat.card Q := card_monoidHom_of_hasEnoughRootsOfUnity Q ℂ
  -- `D` has exponent dividing `5` (it is isomorphic to `Q`).
  have hexpD : Monoid.exponent D ∣ 5 := by
    have hiso : D ≃* Q := (monoidHom_mulEquiv_of_hasEnoughRootsOfUnity Q ℂ).some
    rw [Monoid.exponent_eq_of_mulEquiv hiso]; exact hexp
  -- The order-reversing duality bijection `Subgroup Q ≃ Subgroup D`.
  let e := subgroupOrderIsoSubgroupMonoidHom Q ℂ
  let eEquiv : Subgroup Q ≃ Subgroup D :=
    e.toEquiv.trans (OrderDual.ofDual (α := Subgroup D))
  have heCard : ∀ H : Subgroup Q, Nat.card (eEquiv H) = Nat.card (Q ⧸ H) := by
    intro H
    exact card_subgroupOrderIsoSubgroupMonoidHom (M := ℂ) H
  -- Index-`5` subgroups of `Q` ≃ order-`5` subgroups of `D`.
  have hsub : {H : Subgroup Q // Nat.card (Q ⧸ H) = 5} ≃
      {Φ : Subgroup D // Nat.card Φ = 5} :=
    eEquiv.subtypeEquiv (fun H => by rw [← heCard H])
  -- Count on the dual and transport.
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hcount := card_prime_order_subgroups (P := D) hexpD
  rw [show (5 : ℕ) - 1 = 4 from rfl, hcardD] at hcount
  rw [Nat.card_congr hsub]
  exact hcount

end LeanDring.P5Presentation
