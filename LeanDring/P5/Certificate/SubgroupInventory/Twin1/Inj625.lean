/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryTransA

/-!
# O(n) transversal-injectivity route for the order-5 K-stratum (|R| = 625)

The default `decide` for `Function.Injective (fun i => reduceAux q gK (R i))`
(`Fintype.decidableInjectiveFintype`) recomputes the canonical form `reduceAux` at
every one of the `625² ≈ 390k` index pairs, which puts it out of the kernel's
reach.

`injective_of_isChain_cKey` replaces that quadratic proof by a **linear** one:
map each coordinate vector to its mixed-radix key `cKey : Coordinates → ℕ` (a
base-5 encoding), and check that the key-image of the transversal is *strictly
increasing along adjacent entries only* — `List.IsChain (· < ·)`, an `O(n)` kernel
`decide`.  A strictly-increasing chain is `Pairwise (· < ·)` (transitivity), hence
its entries are pairwise distinct, hence the underlying function is injective
(`List.nodup_ofFn`).  No `cKey`-injectivity lemma is needed: `<` is irreflexive, so
`cKey a < cKey b` already forces `a ≠ b`.

The transversal data is emitted **sorted by `cKey`** so the chain check holds.  The
one remaining `reduceAux` cost is the `625` evaluations building `List.ofFn`
(idempotent on the pre-reduced transversal).
-/

namespace LeanDring.P5Presentation

open List

/-- Mixed-radix (base-5) key of a coordinate vector — a `Coordinates → ℕ`
encoding used only to certify distinctness of transversal elements in `O(n)`. -/
def cKey (v : Coordinates) : ℕ :=
  v.1.val * 625 + v.2.1.val * 125 + v.2.2.1.val * 25 + v.2.2.2.1.val * 5 + v.2.2.2.2.val

/-- **Linear injectivity certificate.** If the `cKey`-image of `List.ofFn f` is a
strictly-increasing adjacent chain, then `f` is injective.  The chain hypothesis is
a single `O(n)` `decide`; strictness gives pairwise-distinct keys, hence distinct
values, hence injectivity. -/
theorem injective_of_isChain_cKey {n : ℕ} (f : Fin n → Coordinates)
    (h : IsChain (· < ·) ((List.ofFn f).map cKey)) :
    Function.Injective f := by
  have hp : Pairwise (· < ·) ((List.ofFn f).map cKey) := isChain_iff_pairwise.mp h
  have hp2 : Pairwise (fun a b => cKey a < cKey b) (List.ofFn f) := pairwise_map.mp hp
  have hnd : (List.ofFn f).Nodup :=
    hp2.imp (fun {a b} hab heq => absurd (heq ▸ hab) (lt_irrefl _))
  exact nodup_ofFn.mp hnd

end LeanDring.P5Presentation
