/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import Mathlib.GroupTheory.Sylow
import LeanDring.Theory.DRing.Marks

-- Several statements below do not mention the section's `[Fintype _]` /
-- group binders, but their proofs need them for instance synthesis, so the
-- binders cannot be `omit`ted.  The linters' suggested rewrite to `[Finite _]`
-- plus `Fintype.ofFinite` is a genuine refactor, not a cleanup.
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

/-!
# Marks of the transitive `G`-sets

**EVEN-ORDER LAYER.** Inside the root module's build closure and audit:
no `sorry`, three standard axioms. Everything in this file is proved
unconditionally — it carries no named `Prop` hypothesis.

The second step of the Boltje integrality programme.

Boltje's Cor. 2.5 is proved by downward induction on
`m(f) = max {|K|: K ∈ supp f}`: one peels the top-order orbits off `f`
by subtracting `ρ_G(α · [G/H])`, and the induction turns on two facts
about the marks of a transitive `G`-set, both proved here:

* `fix_coset_eq_zero_of_forall` — `|(G/H)^K| = 0` unless `K` is
  subconjugate to `H`; in particular the marks of `[G/H]` vanish at every
  `K` with `|H| < |K|`, so subtracting the peel-off term does not disturb
  the strictly larger part of the support;
* `fix_coset_self` — `|(G/H)^H| = [N_G(H): H]`, the value that appears
  as the modulus of Boltje's congruence, and the reason the coefficient
  `α` in the peel-off step is an integer exactly when the congruence
  holds.

Everything rests on `mem_fixedPoints_coset_iff`: the coset `gH` is
`K`-fixed exactly when `g⁻¹Kg ≤ H`.

No `sorry`, no custom axiom.
-/

namespace LeanDring

namespace Even

open FinGSet MulAction

variable {G : Type*} [Group G] [Fintype G]


/-- **The fixed cosets of `K` acting on `G/H`.** The coset `gH` is fixed
by `K` exactly when `g⁻¹Kg ≤ H`, equivalently `K ≤ gHg⁻¹`. -/
theorem mem_fixedPoints_coset_iff (H K : Subgroup G) (g : G) :
    (QuotientGroup.mk g : G ⧸ H) ∈ fixedPoints K (G ⧸ H) ↔
      ∀ k ∈ K, g⁻¹ * k * g ∈ H := by
  simp only [mem_fixedPoints]
  constructor
  · intro hfix k hk
    have h1 : (QuotientGroup.mk (k⁻¹ * g) : G ⧸ H) = QuotientGroup.mk g :=
      hfix ⟨k⁻¹, inv_mem hk⟩
    have h2 := QuotientGroup.eq.mp h1
    simpa [mul_assoc] using h2
  · rintro hall ⟨k, hk⟩
    change (QuotientGroup.mk (k * g) : G ⧸ H) = QuotientGroup.mk g
    refine QuotientGroup.eq.mpr ?_
    have := hall k⁻¹ (inv_mem hk)
    simpa [mul_assoc] using this

/-- **The marks of `[G/H]` vanish off the subconjugates of `H`.**  If no
conjugate of `K` sits inside `H`, then `K` fixes no coset. -/
theorem fix_coset_eq_zero_of_forall (H K : Subgroup G)
    (hno : ∀ g : G, ∃ k ∈ K, g⁻¹ * k * g ∉ H) :
    fix K (coset G H) = 0 := by
  rw [fix, Nat.card_eq_zero]
  left
  refine ⟨fun x => ?_⟩
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective x.1
  obtain ⟨k, hk, hkn⟩ := hno g
  refine hkn ?_
  have hx : (QuotientGroup.mk g : G ⧸ H) ∈ fixedPoints K (G ⧸ H) := hg ▸ x.2
  exact (mem_fixedPoints_coset_iff H K g).mp hx k hk

/-- **Order obstruction.**  If `|H| < |K|` then `K` fixes no coset of `H`:
conjugation would embed `K` into `H`. -/
theorem fix_coset_eq_zero_of_card_lt (H K : Subgroup G)
    (hlt : Nat.card H < Nat.card K) : fix K (coset G H) = 0 := by
  refine fix_coset_eq_zero_of_forall H K fun g => ?_
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hinj : Function.Injective (fun k : K => (⟨g⁻¹ * (k : G) * g, hcon k k.2⟩ : H)) := by
    intro a b hab
    have h : g⁻¹ * (a : G) * g = g⁻¹ * (b : G) * g := congrArg Subtype.val hab
    refine Subtype.ext ?_
    have := congrArg (fun x => g * x * g⁻¹) h
    simpa [mul_assoc] using this
  exact absurd (Nat.card_le_card_of_injective _ hinj) (by omega)

/-- **The diagonal mark.**  `|(G/H)^H| = [N_G(H): H]` — the modulus of
Boltje's congruence at `H`, and the value the peel-off coefficient is
divided by. -/
theorem fix_coset_self (H : Subgroup G) :
    fix H (coset G H) = (H.subgroupOf (Subgroup.normalizer H)).index :=
  Nat.card_congr (Sylow.fixedPointsMulLeftCosetsEquivQuotient H)

end Even

end LeanDring

/-! ## Axiom audit -/

#print axioms LeanDring.Even.mem_fixedPoints_coset_iff
#print axioms LeanDring.Even.fix_coset_eq_zero_of_forall
#print axioms LeanDring.Even.fix_coset_eq_zero_of_card_lt
#print axioms LeanDring.Even.fix_coset_self
