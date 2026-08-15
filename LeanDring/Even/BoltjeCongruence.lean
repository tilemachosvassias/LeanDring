/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Even.BurnsideGhost
import LeanDring.Even.SubgroupMoebius

-- Several statements below do not mention the section's `[Fintype _]` /
-- group binders, but their proofs need them for instance synthesis, so the
-- binders cannot be `omit`ted.  The linters' suggested rewrite to `[Finite _]`
-- plus `Fintype.ofFinite` is a genuine refactor, not a cleanup.
set_option linter.unusedFintypeInType false

/-!
# Boltje's congruence, and why it feeds the peel-off step

**EVEN-ORDER LAYER.** Inside the root module's build closure and audit:
no `sorry`, three standard axioms. The results here are
verified *implications*; their hypotheses are named `Prop`s (see §7.6 of
the paper).

The fourth step of the Boltje integrality programme, and the one that makes the
first three cohere.

Boltje's Cor. 2.5 characterizes the image of `ρ_G: B(G) → B̂(G)` by

`∑_{H ≤ I ≤ N_G(H)} μ(H,I) · f_I ≡ 0  mod  [N_G(H): H]`   for all `H ≤ G`,

which is `BoltjeCongruenceAt` below. The (ii) ⟹ (i) direction is a
downward induction whose step is `Even.peel`, and that step needs
`[N_G(H): H] ∣ f H` — not the congruence, but a plain divisibility.
`dvd_of_congruenceAt` supplies it: **at the top of the support the
congruence collapses to exactly that divisibility**, because every `I`
strictly above `H` in the interval has `|H| < |I|` and so contributes
`f I = 0`, leaving the single term `μ(H,H)·f H = f H`.

That is the join between the four steps: the Möbius function of
`LeanDring/Even/SubgroupMoebius.lean` states the congruence, the mark computations
of `LeanDring/Even/BurnsideMarks.lean` make the subtraction harmless above the
current level, and this file turns the congruence into the divisibility
that `Even.peel` (`LeanDring/Even/BurnsideGhost.lean`) consumes.

What is still missing for Cor. 2.5 itself is the *assembly*: iterating
`peel` across the conjugacy classes at one level, then strong-inducting
downward on `m(f)`. That needs orbit representatives of the maximal-order
support, and — to keep the congruence available at each stage — Boltje's
Prop. 2.1, that `ρ_G` of a basis element already satisfies the
congruences.

No `sorry`, no custom axiom.
-/

namespace LeanDring

namespace Even

open FinGSet
open scoped LeanDring.Even.Subgroup

variable {G : Type*} [Group G] [Fintype G]


/-- **Boltje's congruence at `H`** (Cor. 2.5(ii)):
`∑_{H ≤ I ≤ N_G(H)} μ(H,I)·f_I ≡ 0 mod [N_G(H): H]`. -/
def BoltjeCongruenceAt (f : Subgroup G → ℤ) (H : Subgroup G) : Prop :=
  ((H.subgroupOf (Subgroup.normalizer H)).index : ℤ) ∣
    ∑ I ∈ Finset.Icc H (Subgroup.normalizer H), Subgroup.mu H I * f I

/-- A proper subgroup is strictly smaller. -/
theorem card_lt_card_of_lt {H I : Subgroup G} (h : H < I) :
    Nat.card H < Nat.card I := by
  have hss : (H : Set G) ⊂ (I : Set G) := SetLike.coe_ssubset_coe.mpr h
  exact Set.ncard_lt_ncard hss (Set.toFinite _)

/-- **The congruence collapses at the top of the support.**

If `f` vanishes above order `n` and `|H| = n`, then every `I` strictly
above `H` contributes `0` to Boltje's sum, so the congruence at `H` says
precisely `[N_G(H): H] ∣ f H` — the hypothesis `Even.peel` consumes. -/
theorem dvd_of_congruenceAt (f : Subgroup G → ℤ) (n : ℕ)
    (hf : ∀ K : Subgroup G, n < Nat.card K → f K = 0)
    (H : Subgroup G) (hH : Nat.card H = n)
    (hcong : BoltjeCongruenceAt f H) :
    ((H.subgroupOf (Subgroup.normalizer H)).index : ℤ) ∣ f H := by
  have hmem : H ∈ Finset.Icc H (Subgroup.normalizer H) :=
    Finset.mem_Icc.mpr ⟨le_refl H, Subgroup.le_normalizer⟩
  have hsum : ∑ I ∈ Finset.Icc H (Subgroup.normalizer H), Subgroup.mu H I * f I
      = Subgroup.mu H H * f H := by
    refine Finset.sum_eq_single_of_mem H hmem (fun I hI hne => ?_)
    have hle : H ≤ I := (Finset.mem_Icc.mp hI).1
    have hlt : H < I := lt_of_le_of_ne hle (Ne.symm hne)
    rw [hf I (by rw [← hH]; exact card_lt_card_of_lt hlt), mul_zero]
  rw [Subgroup.mu_self, one_mul] at hsum
  rw [BoltjeCongruenceAt] at hcong
  rwa [hsum] at hcong

end Even

end LeanDring

/-! ## Axiom audit -/

#print axioms LeanDring.Even.card_lt_card_of_lt
#print axioms LeanDring.Even.dvd_of_congruenceAt
