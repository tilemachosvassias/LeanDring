/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Even.BurnsideMarks

-- Several statements below do not mention the section's `[Fintype _]` /
-- group binders, but their proofs need them for instance synthesis, so the
-- binders cannot be `omit`ted.  The linters' suggested rewrite to `[Finite _]`
-- plus `Fintype.ofFinite` is a genuine refactor, not a cleanup.
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

/-!
# The markGhost ring of `B(G)` and the peel-off step

**EVEN-ORDER LAYER.** Inside the root module's build closure and audit:
no `sorry`, three standard axioms. Everything in this file is proved
unconditionally — it carries no named `Prop` hypothesis.

The third step of the Boltje integrality programme.

The project had `BurnsideRing.mark H: B(G) →+* ℤ` for each subgroup `H`
separately, but nothing assembling them. This file adds

* `markGhost` — the assembled mark homomorphism `ρ_G: B(G) → (Subgroup G → ℤ)`,
  `b ↦ (K ↦ |b^K|)`, and
* `transitive H` — the class of `G/H`, the basis element the induction
  peels off,

and then the step that drives Boltje's Cor. 2.5:

* `ghost_transitive_eq_zero_of_card_lt` — `ρ_G([G/H])` vanishes at every
  `K` with `|H| < |K|`;
* `ghost_transitive_self` — `ρ_G([G/H])(H) = [N_G(H): H]`;
* `peel` — if `f` vanishes above order `n`, if `|H| = n`, and if
  `[N_G(H): H] ∣ f H`, then `f - α·ρ_G([G/H])` still vanishes above `n`
  **and** now vanishes at `H`, with `α:= f H / [N_G(H): H]`.

`peel` is the induction step of Cor. 2.5: repeated application clears
level `n` one conjugacy class at a time, and the congruence hypothesis of
Cor. 2.5 is exactly what supplies the divisibility `[N_G(H): H] ∣ f H`
at the top of the support.

No `sorry`, no custom axiom.
-/

namespace LeanDring

namespace Even

open FinGSet

variable {G : Type*} [Group G] [Fintype G]


/-- The class of the transitive `G`-set `G/H` in the Burnside ring. -/
noncomputable def transitive (H : Subgroup G) : BurnsideRing G :=
  GrothendieckRing.of (Skel.mk (coset G H))

/-- **The assembled mark homomorphism** `ρ_G: B(G) → (Subgroup G → ℤ)`.
Boltje's criterion characterizes its image; the project previously had
only the individual `mark K`. -/
noncomputable def markGhost (b : BurnsideRing G) : Subgroup G → ℤ :=
  fun K => BurnsideRing.mark K b

@[simp] theorem markGhost_apply (b : BurnsideRing G) (K : Subgroup G) :
    markGhost b K = BurnsideRing.mark K b := rfl

@[simp] theorem markGhost_zero : markGhost (0 : BurnsideRing G) = 0 := by
  funext K; simp [markGhost]

theorem markGhost_sub (a b : BurnsideRing G) : markGhost (a - b) = markGhost a - markGhost b := by
  funext K; simp [markGhost]

theorem markGhost_zsmul (n : ℤ) (b : BurnsideRing G) : markGhost (n • b) = n • markGhost b := by
  funext K; simp [markGhost]

/-- The marks of `[G/H]` are the fixed-point counts of `G/H`. -/
theorem markGhost_transitive (H K : Subgroup G) :
    markGhost (transitive H) K = (fix K (coset G H) : ℤ) := by
  simp [markGhost, transitive, BurnsideRing.mark_of]

/-- **`ρ_G([G/H])` vanishes above `|H|`** — so subtracting a multiple of
it cannot disturb the part of a markGhost function living in strictly larger
order. -/
theorem ghost_transitive_eq_zero_of_card_lt (H K : Subgroup G)
    (hlt : Nat.card H < Nat.card K) : markGhost (transitive H) K = 0 := by
  rw [markGhost_transitive, fix_coset_eq_zero_of_card_lt H K hlt]
  rfl

/-- **`ρ_G([G/H])(H) = [N_G(H): H]`** — the modulus of Boltje's
congruence at `H`. -/
theorem ghost_transitive_self (H : Subgroup G) :
    markGhost (transitive H) H = ((H.subgroupOf (Subgroup.normalizer H)).index : ℤ) := by
  rw [markGhost_transitive, fix_coset_self H]

/-- **The peel-off step of Boltje's Cor. 2.5.**

Given `f` vanishing above order `n`, a subgroup `H` of order exactly `n`,
and the divisibility `[N_G(H): H] ∣ f H` that the congruence supplies,
subtracting `α · ρ_G([G/H])` with `α = f H / [N_G(H): H]` keeps `f`
vanishing above `n` and additionally kills it at `H`.

Iterating this over the conjugacy classes at level `n` clears the whole
level, which is what makes the downward induction on
`m(f) = max {|K|: f K ≠ 0}` go through. -/
theorem peel (f : Subgroup G → ℤ) (n : ℕ)
    (hf : ∀ K : Subgroup G, n < Nat.card K → f K = 0)
    (H : Subgroup G) (hH : Nat.card H = n)
    (hdvd : ((H.subgroupOf (Subgroup.normalizer H)).index : ℤ) ∣ f H) :
    ∃ α : ℤ,
      (∀ K : Subgroup G, n < Nat.card K →
        (f - α • markGhost (transitive H)) K = 0) ∧
      (f - α • markGhost (transitive H)) H = 0 := by
  obtain ⟨α, hα⟩ := hdvd
  refine ⟨α, fun K hK => ?_, ?_⟩
  · have h1 : f K = 0 := hf K hK
    have h2 : markGhost (transitive H) K = 0 :=
      ghost_transitive_eq_zero_of_card_lt H K (by omega)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h1, h2, mul_zero, sub_zero]
  · have h2 : markGhost (transitive H) H =
      ((H.subgroupOf (Subgroup.normalizer H)).index : ℤ) := ghost_transitive_self H
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h2, hα]
    ring

end Even

end LeanDring

/-! ## Axiom audit -/

#print axioms LeanDring.Even.markGhost_transitive
#print axioms LeanDring.Even.ghost_transitive_eq_zero_of_card_lt
#print axioms LeanDring.Even.ghost_transitive_self
#print axioms LeanDring.Even.peel
