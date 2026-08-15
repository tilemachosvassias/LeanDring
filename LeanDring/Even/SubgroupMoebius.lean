/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Order.Interval.Finset.Defs

/-!
# The Möbius function of the subgroup lattice

**EVEN-ORDER LAYER.** Inside the root module's build closure and audit:
no `sorry`, three standard axioms. Everything in this file is proved
unconditionally — it carries no named `Prop` hypothesis.

The first step of the Boltje integrality programme. Boltje's congruence
([Boltje04] Cor. 2.8) — the
criterion characterizing the image of the mark homomorphism, and the one
open input of the whole even-order conductor lane — reads

`∑_{H ≤ I ≤ N_G(H)} μ_{H,I} · f_I ≡ 0  mod  [N_G(H): H]`,

so it cannot even be *stated* without a Möbius function on the subgroup
lattice. Mathlib has the general incidence algebra and its `mu`
(`Mathlib.Combinatorics.Enumerative.IncidenceAlgebra`), but **not** the
`LocallyFiniteOrder (Subgroup G)` instance that `mu` needs: as of this
writing `IncidenceAlgebra.mu ℤ (α:= Subgroup G)` fails to elaborate.
That gap is what this file closes.

It turns out to be cheap. `Subgroup G` is finite whenever `G` is (embed
it in `Set G`), and Mathlib derives a `LocallyFiniteOrder` from a
`Fintype` on a preorder. So the instance is three lines, and the whole
Mathlib Möbius API — `mu_self`, `mu_apply`, `moebius_inversion_top`, … —
becomes available on subgroups.

Both instances are `scoped`, so importing this file does not silently
install a noncomputable `Fintype (Subgroup G)` everywhere.

## Main results

* `Subgroup.instFintype`, `Subgroup.instLocallyFiniteOrder` — the missing
  instances (scoped);
* `Subgroup.mu` — the Möbius function of the subgroup lattice;
* `Subgroup.sum_mu_Icc` — its defining property,
  `∑_{I ∈ [H,K]} μ(H,I) = δ_{H,K}`, which is the shape Boltje's induction
  consumes.

No `sorry`, no custom axiom.
-/

namespace LeanDring

namespace Even

-- `IncidenceAlgebra.mu` on the subgroup lattice needs decidability of the order
-- relation; supplying it classically is what makes `mu` elaborate here at all
-- (see the note above). Stating explicit `Decidable` instances instead would be
-- a refactor of that elaboration, not a cleanup.
set_option linter.style.openClassical false
open scoped Classical
open Finset IncidenceAlgebra

variable {G : Type*} [Group G]

namespace Subgroup

/-- The subgroup lattice of a finite group is finite. Noncomputable, and
`scoped`: it is a fact about the lattice, not a decision procedure, and
should not be installed globally. -/
noncomputable scoped instance instFintype [Finite G] : Fintype (Subgroup G) :=
  have : Finite (Subgroup G) :=
    Finite.of_injective (SetLike.coe : Subgroup G → Set G) SetLike.coe_injective
  Fintype.ofFinite _

/-- **The instance Mathlib is missing.** With it, the whole incidence
algebra — in particular `IncidenceAlgebra.mu` — applies to the subgroup
lattice. -/
noncomputable scoped instance instLocallyFiniteOrder [Finite G] :
    LocallyFiniteOrder (Subgroup G) :=
  Fintype.toLocallyFiniteOrder

/-- **The Möbius function of the subgroup lattice**, `μ(H,K)`. This is
the `μ_{H,I}` of Boltje's congruence and of Müller's Lemma 3.4. -/
noncomputable def mu [Finite G] (H K : Subgroup G) : ℤ :=
  IncidenceAlgebra.mu ℤ H K

@[simp] theorem mu_self [Finite G] (H : Subgroup G) : mu H H = 1 :=
  IncidenceAlgebra.mu_self (𝕜 := ℤ) H

theorem mu_eq_neg_sum_Ico [Finite G] {H K : Subgroup G} (hne : H ≠ K) :
    mu H K = -∑ I ∈ Finset.Ico H K, mu H I :=
  IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne (𝕜 := ℤ) hne

/-- **The defining property, in the form Boltje's induction uses**: the
Möbius function sums to `1` over a degenerate interval and to `0` over
any other. Equivalently `μ * ζ = δ` at `(H,K)`. -/
theorem sum_mu_Icc [Finite G] {H K : Subgroup G} (hle : H ≤ K) :
    ∑ I ∈ Finset.Icc H K, mu H I = if H = K then 1 else 0 := by
  by_cases hHK : H = K
  · subst hHK
    simp
  · rw [if_neg hHK, ← Finset.Ico_insert_right hle,
      Finset.sum_insert Finset.right_notMem_Ico, mu_eq_neg_sum_Ico hHK]
    ring

/-- The same statement with the `if` discharged in the non-degenerate
case, which is how the peel-off step of the induction reads it. -/
theorem sum_mu_Icc_of_ne [Finite G] {H K : Subgroup G} (hle : H ≤ K)
    (hne : H ≠ K) : ∑ I ∈ Finset.Icc H K, mu H I = 0 := by
  rw [sum_mu_Icc hle, if_neg hne]

end Subgroup

end Even

end LeanDring

/-! ## Axiom audit -/

#print axioms LeanDring.Even.Subgroup.mu_self
#print axioms LeanDring.Even.Subgroup.sum_mu_Icc
#print axioms LeanDring.Even.Subgroup.sum_mu_Icc_of_ne
