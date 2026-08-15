# v_task79 — the Mackey species formula for `ind^G_H` in Lean,
# and the `N_G(H)/H`-average

Date 2026-08-08.  `lean_dring/LeanDring/Even/ConductorAtSpecies.lean`
extended by §11 (~250 lines).  0 `sorry`, 0 errors, 0 warnings, no custom
axiom; full serial `lake build` clean (4718 jobs).

**Status: step (1) of the three named steps of v_task78 is DONE.  The
remaining surface is Boltje integrality → assembly.**

## The method (why it was cheaper than estimated)

v_task78 predicted 250–400 lines for the bijection of index sets

`(G / L^G)^K ≅ Σ_{q ∈ (G/H)^K} (H / L)^{K^q}`  (`L ≤ H`)

with matching weights across two `Quotient.out` sections.  That route is
a *dependent* sigma equivalence — the fibre type depends on `q` through
the conjugated subgroup `K^{s(q)}` — and the round-trip proofs would have
had to transport along equalities of `q`.

It was avoided.  Müller's coset sum is first traded for a sum over **all
of `G`**, at the cost of one factor `|M|`:

```lean
open scoped Classical in
noncomputable def condWeight (M K : Subgroup G) (l : M →* ℂˣ) (k : K) (g : G) : ℂ :=
  if h : ∀ u : K, g⁻¹ * (u : G) * g ∈ M then ((l ⟨g⁻¹ * (k : G) * g, h k⟩ : ℂˣ) : ℂ) else 0

theorem sum_condWeight (M K : Subgroup G) [Fintype ↥M] (l : M →* ℂˣ) (k : K) :
    ∑ g : G, condWeight M K l k g =
      (Nat.card ↥M : ℂ) * DRing.species K k (DRing.basisElt M l)
```

Its proof is one application of the section splitting

```lean
noncomputable def cosetSplit (M : Subgroup G) : G ≃ (G ⧸ M) × ↥M   -- g ↦ (gM, s(gM)⁻¹ g)
theorem sum_cosetSplit (M : Subgroup G) [Fintype ↥M] (f : G → ℂ) :
    ∑ g : G, f g = ∑ q : G ⧸ M, ∑ m : ↥M, f (q.out * (m : G))
```

plus two facts: each `K`-fixed coset contributes exactly its `|M|`
elements, all with the *same* weight (conjugating the argument by
`m ∈ M` multiplies `λ` by `λ(m)⁻¹λ(m) = 1`, since `ℂˣ` is commutative),
and each non-fixed coset contributes `0` (`mem_fixCoset_iff`:
`q ∈ (G/M)^K ↔ ∀ u ∈ K, s(q)⁻¹ u s(q) ∈ M`).

In this element-wise form the Mackey regrouping is the **same** splitting
applied once more, at `M = H`: `g = s(q)·y` with `q ∈ G/H`, `y ∈ H`.  No
dependent types, one section layer, and the two `|L|`-factors cancel
because `|L^G| = |L|` (`Subgroup.card_subtype`).

## What was proven

```lean
/-- `K^{s(q)} = s(q)⁻¹ K s(q) ≤ H` for a `K`-fixed coset `q` of `G ⧸ H`. -/
noncomputable def indSub (K : Subgroup G) (q : FixCosetOf K H) : Subgroup ↥H :=
  (conjHom H K q).range
noncomputable def indElt (K : Subgroup G) (k : K) (q : FixCosetOf K H) : ↥(indSub H K q) :=
  ⟨conjHom H K q k, ⟨k, rfl⟩⟩

/-- **The Mackey formula on a basis element.** -/
theorem species_dringInd_basisElt_mackey (K : Subgroup G) (k : K) (L : Subgroup ↥H)
    (l : L →* ℂˣ) :
    DRing.species K k (dringInd H (DRing.basisElt L l)) =
      ∑ q : FixCosetOf K H,
        DRing.species (indSub H K q) (indElt H K k q) (DRing.basisElt L l)

/-- **The Mackey formula on all of `D(H)`** (additivity on the basis). -/
theorem species_dringInd (K : Subgroup G) (k : K) (y : DRing ↥H) :
    DRing.species K k (dringInd H y) =
      ∑ q : FixCosetOf K H, DRing.species (indSub H K q) (indElt H K k q) y
```

i.e. `φ^G_{K,k}(ind^G_H y) = ∑_{q ∈ (G/H)^K} φ^H_{K^{s(q)}, k^{s(q)}}(y)`.

The specialization the witness needs — conjugation by `s(q)` is an
injective endomorphism of the finite group `H`, hence an automorphism, so
`K^{s(q)} = H`:

```lean
theorem indSub_self_eq_top (q : FixCosetOf H H) : indSub H H q = ⊤

/-- **The `N_G(H)/H`-average.** -/
theorem species_dringInd_self (h : ↥H) (y : DRing ↥H) :
    DRing.species H h (dringInd H y) =
      ∑ q : FixCosetOf H H,
        DRing.species (⊤ : Subgroup ↥H) ⟨conjRepOf H H h q, Subgroup.mem_top _⟩ y
```

The index set `FixCosetOf H H` is `N_G(H)/H`: the file already proves
`mem_fixCosetOf_of_mem_normalizer` and `isGoodCoset_iff_mem` (§4), so the
`H`-fixed cosets of `G ⧸ H` are exactly the cosets of `H` contained in
`N_G(H)`, and `conjRepOf H H h q = h^{s(q)}`.

Supporting declarations: `condWeight_of_forall`,
`condWeight_of_not_forall`, `mem_fixCoset_iff`, `cosetSplit`,
`sum_cosetSplit`, `sum_condWeight`, `coe_indElt`, and a local
priority-2000 `Fintype (G ⧸ M)` instance
(`instFintypeQuotSubgroup`) so that all element-wise sums elaborate with
one fixed instance.

## What this buys

Together with `species_dringInd_eq_zero_of_not_subconj` (v_task78),
*every* species value of an induced element is now determined:

* zero at every `(K,k)` with no `G`-conjugate of `K` inside `H`;
* the `N_G(H)/H`-average of `φ^H` on the `H`-column;
* the general Mackey sum in between.

In particular the factor `(N_G(H, h₀H') : H)` — invisible to the
`H`-column of the species table, twisted or not (v_task77's verdict) — is
now explicit: it is the number of terms of the `N_G(H)/H`-average that
survive the fusion condition.

## What remains

Unchanged from v_task78 minus step (1):

1. **Boltje integrality** — `ind^G_H` of the `ℚ`-idempotent multiple
   `(H : H')·e^{D(H)}_{(H,h₀H')}` is `ℤ`-integral.  Genuine mathematics;
   Müller cites it, does not prove it.  The naive `ℤ`-form
   `∑_λ λ(h₀)⁻¹ [H,λ]` has `ℤ[ζ]`-coefficients; the Galois-orbit sum
   repairs the coefficients but multiplies the isolated value by the
   orbit length, and the division back *is* Boltje's congruence.
2. **Assembly** of `SpeciesIsolatingWitness` from 1 + §9 + §10 + §11,
   hence `ConductorAtSpecies` via `conductorAtSpecies_of`, hence
   `ConductorPairDictionary`.

`SpeciesConductorLowerBound` in general still waits on the same input.
`ConductorPairDictionary` is **not** a theorem; `isIndexValue_iff`,
`BCSeparation`, `ATSeparation` were left untouched.  Unconditional cases
of the dictionary remain those of v_task76/77 (trivial pair, top pair,
self-normalizing `H` for the lower half).

## Verification

```
taskset -c 0 lake build LeanDring.Even.ConductorAtSpecies   # 0 err, 0 warn
taskset -c 0 lake build                                     # clean, serial, 4718 jobs
```

Axiom audit (in-file `#print axioms`) for the seven new audited
declarations `mem_fixCoset_iff`, `sum_cosetSplit`, `sum_condWeight`,
`species_dringInd_basisElt_mackey`, `species_dringInd`,
`indSub_self_eq_top`, `species_dringInd_self`:

```
[propext, Classical.choice, Quot.sound]
```

No new imports.  `sorry` count in the file: 0 (repo-wide, outside the
unbuilt exploratory scratch: 0).  The file is still not
imported by the root module.
