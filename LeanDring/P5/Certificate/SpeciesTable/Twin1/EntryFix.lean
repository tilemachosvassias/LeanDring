/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore
import LeanDring.P5.Certificate.ComputableModel.Twin1.Cgs

/-!
# The two non-decidable inputs of the species-entry machinery (generic)

`transversalEquiv` / `species_basisElt_of_transversal` (`Twin1/EntryCore.lean`) consume two
non-`decide` hypotheses per `(H,K)` family:

* **`hfix`** — every supplied representative `t i` names an `H`-fixed coset of
  `K`, i.e. `⟦t i⟧ ∈ fixedPoints H (G ⧸ K)`.  As *data* we only sift the
  **generators** of `H`: for each generator `g`, `t⁻¹·g·t ∈ K` (a cheap
  `siftB`).  This file proves the closure upgrade **once**: per-generator
  conjugation-into-`K` ⟹ `H`-fixedness of the coset (`mem_fixedPoints_of_gens`),
  together with its converse (`conj_mem_of_fixedPoints`) so the fixedness
  predicate becomes a decidable `siftB`-`Bool`.

* **`hcard`** — the completeness count `|T| = |(G/K)^H|`.  It is certified by a
  *cardinality* argument: supply a **full coset transversal** `R : Fin n → G`
  of `K` in `G` (`fun i ↦ ⟦R i⟧` bijective — injective-mod-`K` plus the index
  count `n = [G:K]`), and read the fixed-point count off as the **filter** of
  `R` by `H`-fixedness (`card_fixedPoints_eq_filter`).  The emitted fixed
  sub-transversal is exactly that filtered sublist, so the count equality is a
  kernel `decide` over the `[G:K]` cosets — **no `3125`-carrier scan** when
  `[G:K]` is small (the order-`25` `A`-block has `[G:K] = 125`).

Everything here is GENERIC over a finite group `G`; the `Coordinate q`
instantiation (siftB-decidable predicate, emitted transversals) is downstream.
-/

namespace LeanDring

open MulAction Finset

universe u

variable {G : Type u} [Group G]

/-! ## Piece 1 — the `hfix` generator-closure upgrade -/

/-- **Conjugation-into-`K` is closed.** If `t⁻¹·g·t ∈ K` for every `g` in a
generating set `S`, then `t⁻¹·h·t ∈ K` for every `h ∈ ⟨S⟩`.  (The map
`h ↦ t⁻¹·h·t` is a homomorphism, so this is a plain closure induction — the same
idiom as `normalizes_closure`.) -/
theorem conj_mem_of_closure (K : Subgroup G) (S : Set G) (t : G)
    (hS : ∀ g ∈ S, t⁻¹ * g * t ∈ K) :
    ∀ h ∈ Subgroup.closure S, t⁻¹ * h * t ∈ K := by
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem y hy => exact hS y hy
  | one => simp only [mul_one, inv_mul_cancel]; exact K.one_mem
  | mul a b _ _ ha hb =>
      rw [show t⁻¹ * (a * b) * t = (t⁻¹ * a * t) * (t⁻¹ * b * t) by group]
      exact K.mul_mem ha hb
  | inv a _ ha =>
      rw [show t⁻¹ * a⁻¹ * t = (t⁻¹ * a * t)⁻¹ by group]
      exact K.inv_mem ha

/-- **The coset `⟦t⟧` is `H`-fixed** as soon as `t⁻¹·h·t ∈ K` for every `h ∈ H`.
This is the semantic content that `hfix` needs; combined with
`conj_mem_of_closure` it reduces to per-generator `siftB` checks. -/
theorem mem_fixedPoints_of_forall (H K : Subgroup G) (t : G)
    (hcond : ∀ h : H, t⁻¹ * (h : G) * t ∈ K) :
    (QuotientGroup.mk t : G ⧸ K) ∈ fixedPoints H (G ⧸ K) := by
  rw [mem_fixedPoints]
  intro a
  change ((a : G) * t : G ⧸ K) = (t : G ⧸ K)
  refine QuotientGroup.eq.mpr ?_
  have hmem := hcond a⁻¹
  rw [Subgroup.coe_inv] at hmem
  rw [mul_inv_rev, mul_assoc]
  simpa [mul_assoc] using hmem

/-- **`hfix` from generators (packaged).** `H = ⟨S⟩` and per-generator
conjugation-into-`K` give the `H`-fixedness of `⟦t⟧`. -/
theorem mem_fixedPoints_of_gens (H K : Subgroup G) (S : Set G)
    (hHS : H = Subgroup.closure S) (t : G)
    (hS : ∀ g ∈ S, t⁻¹ * g * t ∈ K) :
    (QuotientGroup.mk t : G ⧸ K) ∈ fixedPoints H (G ⧸ K) := by
  apply mem_fixedPoints_of_forall
  intro h
  subst hHS
  exact conj_mem_of_closure K S t hS (h : G) h.2

/-- **Converse:** an `H`-fixed coset conjugates all of `H` into `K`
(`t⁻¹·h·t ∈ K`).  With `mem_fixedPoints_of_forall` this makes the fixedness
predicate an iff, hence a decidable `siftB`-`Bool` after restricting to
generators. -/
theorem conj_mem_of_fixedPoints (H K : Subgroup G) (t : G)
    (hfix : (QuotientGroup.mk t : G ⧸ K) ∈ fixedPoints H (G ⧸ K)) :
    ∀ h : H, t⁻¹ * (h : G) * t ∈ K := by
  rw [mem_fixedPoints] at hfix
  intro h
  have hh := hfix h⁻¹
  rw [show (h⁻¹ : H) • (QuotientGroup.mk t : G ⧸ K)
      = (QuotientGroup.mk ((h⁻¹ : H) * t : G) : G ⧸ K) from rfl] at hh
  have := QuotientGroup.eq.mp hh
  rw [Subgroup.coe_inv, mul_inv_rev, inv_inv] at this
  rw [mul_assoc]
  simpa [mul_assoc] using this

variable [Fintype G]

/-! ## Piece 2 — the `hcard` completeness count via a full transversal -/

/-- **The fixed-point count as a filter over a full transversal.** If
`fun i ↦ ⟦R i⟧` is a bijection `Fin n ≃ G/K` (a full coset transversal of `K`
in `G`), then the number of `H`-fixed cosets is the number of transversal
indices whose coset is `H`-fixed.  Turning the RHS predicate into a `siftB`
`Bool` (via `mem_fixedPoints_of_forall` / `conj_mem_of_fixedPoints`) makes the
count a kernel `decide` over the `[G:K]` cosets — the certificate for `hcard`. -/
theorem card_fixedPoints_eq_filter (H K : Subgroup G) {n : ℕ} (R : Fin n → G)
    (hbij : Function.Bijective (fun i => (QuotientGroup.mk (R i) : G ⧸ K)))
    [DecidablePred fun i => (QuotientGroup.mk (R i) : G ⧸ K) ∈ fixedPoints H (G ⧸ K)] :
    Fintype.card (fixedPoints H (G ⧸ K))
      = (Finset.univ.filter
          fun i => (QuotientGroup.mk (R i) : G ⧸ K) ∈ fixedPoints H (G ⧸ K)).card := by
  classical
  let e : Fin n ≃ (G ⧸ K) := Equiv.ofBijective _ hbij
  -- fixedPoints as a subtype, pulled back along `e`
  have hcard1 : Fintype.card (fixedPoints H (G ⧸ K))
      = Fintype.card {i : Fin n // (QuotientGroup.mk (R i) : G ⧸ K)
          ∈ fixedPoints H (G ⧸ K)} := by
    apply Fintype.card_congr
    refine (Equiv.subtypeEquiv e (fun i => ?_)).symm
    change ((QuotientGroup.mk (R i) : G ⧸ K) ∈ fixedPoints H (G ⧸ K)) ↔ (e i ∈ _)
    rw [show e i = (QuotientGroup.mk (R i) : G ⧸ K) from Equiv.ofBijective_apply _ hbij i]
  rw [hcard1, Fintype.card_subtype]

/-- **`hcard` builder.** From a full transversal `R` (bijective mod `K`) whose
`H`-fixed indices number exactly `m`, the fixed-point count is `m` — the
hypothesis `species_basisElt_of_transversal` / `transversalEquiv` expects for a
size-`m` supplied fixed transversal. -/
theorem card_fixedPoints_eq_of_filter_card (H K : Subgroup G) {n : ℕ} (R : Fin n → G)
    (hbij : Function.Bijective (fun i => (QuotientGroup.mk (R i) : G ⧸ K)))
    [DecidablePred fun i => (QuotientGroup.mk (R i) : G ⧸ K) ∈ fixedPoints H (G ⧸ K)]
    {m : ℕ}
    (hm : (Finset.univ.filter
        fun i => (QuotientGroup.mk (R i) : G ⧸ K) ∈ fixedPoints H (G ⧸ K)).card = m) :
    Fintype.card (fixedPoints H (G ⧸ K)) = m := by
  rw [card_fixedPoints_eq_filter H K R hbij, hm]

omit [Fintype G] in
/-- **A full coset transversal from injectivity + the index count.** An
injective-mod-`K` family `R : Fin n → G` with `n = [G:K]` is automatically a
bijection `Fin n ≃ G/K` — the surjectivity is free by cardinality.
This is the `hbij` input of `card_fixedPoints_eq_filter`, reduced to a
`decide`-able injectivity plus a single numeric index count. -/
theorem transversalMod_bijective (K : Subgroup G) [Fintype (G ⧸ K)] {n : ℕ} (R : Fin n → G)
    (hcard : Fintype.card (G ⧸ K) = n)
    (hinj : Function.Injective fun i => (QuotientGroup.mk (R i) : G ⧸ K)) :
    Function.Bijective fun i => (QuotientGroup.mk (R i) : G ⧸ K) :=
  (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hinj, by rw [Fintype.card_fin, hcard]⟩

end LeanDring
