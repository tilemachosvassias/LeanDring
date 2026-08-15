# v_task78 — `ind^G_H : D(H) →+ D(G)` in Lean, and the
# subconjugacy vanishing along induction

Date 2026-08-08.  `lean_dring/LeanDring/Even/ConductorAtSpecies.lean`
extended by §10 (~140 lines).  0 `sorry`, 0 errors, 0 warnings, no custom
axiom; full serial `lake build` clean (4718 jobs).

**Status: the missing machinery now EXISTS as a Lean map, with its
defining property proven; the Mackey species formula and Boltje
integrality — hence the witness — are NOT done.  The dictionary did not
close.**

## What was built

### 1. The map (done)

`D(H)` has the free `ℤ`-basis `basisOfCharPairClass` (v_task73), indexed
by `H`-conjugacy classes of character pairs of `H`.  So `ind^G_H` is
defined by `Module.Basis.constr` on that basis:

```lean
noncomputable def indChar {K : Subgroup ↥H} (l : K →* ℂˣ) : ↥(K.map H.subtype) →* ℂˣ
noncomputable def indPair (p : CharPair ↥H ℂˣ) : DRing G :=
  DRing.basisElt (p.1.map H.subtype) (indChar H p.2)
noncomputable def dringInd (H : Subgroup G) [Fintype ↥H] : DRing ↥H →+ DRing G
```

`indChar` transports `λ` along `K ≃* K.map H.subtype`
(`Subgroup.equivMapOfInjective`, `indChar_apply`).  Well-definedness is
`isConjPair_map`: an `H`-conjugacy `(K,λ) ∼_a (K',λ')` (with `a ∈ H`) is
in particular a `G`-conjugacy of the pushed pairs, by the *same*
conjugator viewed in `G`; hence `indPair_congr`, and by
`DRing.basisElt_eq_iff` the value on a class is independent of the
representative.

Defining property, proven:

```lean
theorem dringInd_basisElt (K : Subgroup ↥H) (l : K →* ℂˣ) :
    dringInd H (DRing.basisElt K l) = DRing.basisElt (K.map H.subtype) (indChar H l)
theorem dringInd_basisElt_one (K : Subgroup ↥H) :          -- Burnside compatibility
    dringInd H (DRing.basisElt K 1) = DRing.basisElt (K.map H.subtype) 1
```

Note this is genuinely Müller's `ind`: `basisElt K l` *is* the class of
the monomial `G`-set induced from `λ` (`MonGSet.induced`), and
`[K,λ]_H ↦ [K^G, λ^G]_G` is transitivity of induction along `K ≤ H ≤ G`.
The construction is by the universal property of the free basis rather
than by building `G ×_H X` as a monomial `G`-set; the two agree on the
basis by definition, which is what every downstream computation uses.

### 2. Species of an induced element (partially done)

```lean
theorem species_dringInd_basisElt (K : Subgroup G) (k : K) (L : Subgroup ↥H) (l : L →* ℂˣ) :
    DRing.species K k (dringInd H (DRing.basisElt L l)) =
      ∑ q : FixCosetOf K (L.map H.subtype), (indChar H l (conjRepOf (L.map H.subtype) K k q) : ℂ)
```

— i.e. Müller's formula for `D(G)` at the pushed pair, immediate from
`dringInd_basisElt`.  The **genuine Mackey formula**

`φ^G_{K,k}(ind^G_H y) = ∑_{q ∈ (G/H)^K} φ^H_{K^q, k^q}(y)`

was **not** proven.  It is exactly the regrouping the task anticipated,
but the regrouping is a *bijection of index sets*, not a rearrangement of
one sum: one needs

`(G / L^G)^K  ≅  Σ_{q ∈ (G/H)^K} (H / L)^{K^q}`   (`L ≤ H`)

with the weights matching, i.e. `s_G(qp)⁻¹ k s_G(qp)` mapped to
`s_H(p)⁻¹ (s_G(q)⁻¹ k s_G(q)) s_H(p)` modulo the choice of
`Quotient.out` sections at two levels.  In Lean that is two layers of
`Quotient.out` bookkeeping plus a `Sigma`-equivalence; estimated
250–400 lines and the dominant cost of the next session.  It was not
attempted here because, without it, nothing downstream changes, and with
it, the witness still needs Boltje (below).

The **one consequence of induction obtainable without Mackey** was proven
in full:

```lean
theorem species_dringInd_eq_zero_of_not_subconj (K : Subgroup G) (k : K)
    (hsub : ∀ g : G, ∃ u : K, g⁻¹ * (u : G) * g ∉ H) (y : DRing ↥H) :
    DRing.species K k (dringInd H y) = 0
```

**every species whose subgroup is not subconjugate to `H` annihilates the
entire image of `ind^G_H`.**  Proof: the kernel of
`φ_{K,k} ∘ ind^G_H` is an additive subgroup of `D(H)`; it contains every
`basisElt L l`, because `dringInd_basisElt` turns that into
`[L^G, λ^G]` with `L^G ≤ H`, and the index set of Müller's formula
(`K`-fixed cosets of `G/L^G`) is then empty
(`species_basisElt_eq_zero_of_not_subconj`); and the basis elements
generate `D(H)` additively (`exists_basisElt_decomposition`).

This is the *vanishing half* of Müller's Satz 2.3.3 witness argument, for
the species outside `H` — proven unconditionally, and reusable verbatim
once the witness element is available.

### 3. The witness (NOT done)

`SpeciesIsolatingWitness` was not attempted, and the reason is now sharp
rather than a guess.  Given `x = ind^G_H(z)`, §10 kills the species at
subgroups not subconjugate to `H`.  What remains is:

* the species at subgroups *inside* `H` — these need the Mackey formula
  above to be expressed in terms of `φ^H`, and then the orthogonality of
  §9 to be applied inside `D(H)`;
* the choice of `z`: over `ℚ` it is `(H:H')·e^{D(H)}_{(H,h₀H')}`, whose
  naive `ℤ`-form `∑_λ λ(h₀)⁻¹ [H,λ]` has coefficients in `ℤ[ζ]`, not `ℤ`.
  Summing the full Galois orbit repairs the coefficients (they become
  traces of roots of unity, hence rational integers — the v_task71/74
  technique), but then the *value* at `φ_{H,h₀}` is multiplied by the
  orbit length, so the resulting `n` is the wrong one unless the orbit
  sum is again divided — and the divisibility that permits the division
  is precisely **Boltje's congruence**.  There is no shortcut around it:
  the integrality of `(N_G(H,h₀H') : H')·e_{(H,h₀H')}` is a theorem about
  the image of `ind`, not about any single explicit `ℤ`-combination.

So the honest decomposition of the remaining surface is now three named
steps, in dependency order:

1. **Mackey** (`φ^G(ind y) = ∑_{q} φ^H(y)`) — pure combinatorics of
   fixed cosets, no new mathematics, ~1 session.
2. **Boltje integrality** — `ind^G_H` of the `ℚ`-idempotent multiple is
   `ℤ`-integral.  Genuine mathematics; Müller cites it, does not prove it.
3. Assembly of `SpeciesIsolatingWitness` from 1 + 2 + §9 + §10, and hence
   `ConductorAtSpecies` via `conductorAtSpecies_of`.

`SpeciesConductorLowerBound` in general also waits on 1 + 2 (v_task77's
verdict, unchanged: the missing factor `(N_G(H,h₀H') : H)` is invisible
to the `H`-column and lives in the inverse table).

## Stage 3 (dictionary assembly / propagation): not reached

`ConductorPairDictionary` is **not** a theorem.  `conductorPairDictionary'`
still consumes `ConductorAtSpecies`, which still consumes both halves.
`isIndexValue_iff` is therefore unchanged, and no upgrade to
`BCSeparation`/`ATSeparation` was possible; their hypotheses were left
untouched (checking them would have been vacuous work).

Unconditional cases of the dictionary remain exactly those of v_task76/77:
the trivial pair, the top pair, and every self-normalizing `H` for the
lower half.

## Verification

```
taskset -c 0 lake build LeanDring.Even.ConductorAtSpecies   # 0 err, 0 warn
taskset -c 0 lake build                                     # clean, serial, 4718 jobs
```

Axiom audit (in-file `#print axioms`) for the eight new declarations
`indChar_apply`, `indChar_one`, `isConjPair_map`, `indPair_congr`,
`dringInd_basisElt`, `species_dringInd_basisElt`,
`dringInd_basisElt_one`, `species_dringInd_eq_zero_of_not_subconj`:

```
[propext, Classical.choice, Quot.sound]
```

No new imports.  `sorry` count in the file: 0 (repo-wide, outside the
unbuilt exploratory scratch: 0).  The file is still not
imported by the root module.
