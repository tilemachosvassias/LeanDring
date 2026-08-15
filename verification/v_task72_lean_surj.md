# v_task72 — `SpeciesPairSeparation` discharged (item (1) of the dictionary)

Date 2026-08-08.  New file:
`lean_dring/LeanDring/Even/SpeciesSeparation.lean` (≈235 lines).
Doc-only touch-ups in `Even/ConductorDictionaryGalois.lean` (two comment
blocks; no proof changed).

**Result: `SpeciesPairSeparation` is a theorem.**
`Even.speciesPairSeparation : SpeciesPairSeparation.{u}`, and the assembly is
now hypothesis-free: `Even.fullyFused_of_intPoint'`.
0 `sorry`, 0 errors, 0 warnings, no custom axiom.

---

## 1. What the Prop actually says (and why the briefed route was the wrong one)

The task brief proposed a surjectivity/dimension-counting route (every
`p : D(G) →+* ℂ` is a species; species count = ℤ-rank; Dedekind bound).  That is
**not** what `SpeciesPairSeparation` demands.  Its statement in
`Even/ConductorDictionaryGalois.lean:424` is a *separation* (injectivity)
statement, not a surjectivity one:

```lean
def SpeciesPairSeparation : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (H : Subgroup G) (h k : H),
    DRing.species H h = DRing.species H k →
      ∃ g ∈ Subgroup.normalizer H, (g * (h : G) * g⁻¹) * (k : G)⁻¹ ∈ ⁅H, H⁆
```

No ring hom `D(G) →+* ℂ` other than a species ever appears; there is no
tensor product, no rank, no dimension count.  So no `rank D(G) = #pair classes`
lemma was needed, and none was introduced.  (Surjectivity of the species map
onto `Hom(D(G), ℂ)` remains *out of scope* — it is not part of the remaining
dictionary surface either, see §5.)

## 2. The proof (Müller's basis elements + Dedekind + finite-abelian duality)

Test the hypothesis on the induced basis elements `[H, λ]` of
`Theory/DRing/Induced.lean` — `G/H` twisted by a linear character
`λ : ↥H →* ℂˣ` — where Müller's formula (`DRing.species_basisElt`, already
sorry-free) reads

  `φ_{H,m}[H, λ] = ∑_{q ∈ (G/H)^H} λ(s(q)⁻¹ · m · s(q))`,  `s = Quotient.out`.

| step | lemma | content |
|---|---|---|
| index set | `Even.FixCoset H := fixedPoints ↥H (G ⧸ H)` | the `H`-fixed cosets |
| **`inv_out_mem_normalizer`** | `q : FixCoset H → (s(q))⁻¹ ∈ N_G(H)` | `u • q = q ∀u ∈ H` gives `s(q)⁻¹ H s(q) ⊆ H`, then `Subgroup.mem_normalizer_fintype`.  *This is where `N_G(H)` in the conclusion comes from.* |
| `conjRep H m q` | `⟨s(q)⁻¹ m s(q), sectionConj_mem …⟩ : ↥H` | the summand's argument |
| `one_mem_fixCoset`, `oneFixCoset` | the identity coset is `H`-fixed | its `s(q)` lies in `H` |
| **`of_conjRep_one`** | `of (conjRep H m 1̄) = of m` in `Abelianization ↥H` | `s(1̄) ∈ H`, and conjugation is trivial in the abelianization |
| **`species_basisElt_self`** | `φ_{H,m}[H,λ] = ∑_{q} λ(conjRep H m q)` | `species_basisElt` + `Fintype.sum_equiv (Equiv.refl _)` (the index types are defeq) |
| **`evalChar` / `evalChar_injective`** | `a ↦ ev_a : A →* ((A →* ℂˣ) →* ℂˣ)` is injective for finite abelian `A` | Mathlib `CommGroup.forall_apply_eq_apply_iff` (ℂ algebraically closed ⇒ `HasEnoughRootsOfUnity`) |
| **`speciesPairSeparation`** | the theorem | see below |

Assembly.  Each `λ : ↥H →* ℂˣ` factors through `A := Abelianization ↥H`, so the
hypothesis becomes: the two families `q ↦ ev_{f q}` and `q ↦ ev_{g q}` of
characters of the dual group `A →* ℂˣ`, with
`f q = of(s(q)⁻¹ h s(q))`, `g q = of(s(q)⁻¹ k s(q))`, have equal value-sums at
every point of the dual group.  That is *exactly* the hypothesis of
`count_eq_of_sum_eq` — **Dedekind's linear independence of characters**,
already proven in `Theory/DRing/SpeciesInjectivity.lean:57` (the dualisation
`element ↦ evaluation character` is the only new idea needed to reuse it).
Hence equal multiplicities.  The character `ev_{of k}` occurs on the `g`-side
(identity coset, `of_conjRep_one`), so it occurs on the `f`-side: some fixed
coset `q` has `ev_{f q} = ev_{of k}`, so `f q = of k` by duality, so
`(s(q)⁻¹ h s(q)) · k⁻¹ ∈ commutator ↥H`, so — via the existing
`map_commutator_subtype` — `(g h g⁻¹) k⁻¹ ∈ ⁅H,H⁆` with `g := s(q)⁻¹ ∈ N_G(H)`.
∎

Note this proves the *harder* direction only; the converse
(`species_congr_coset` + `DRing.species_conj`) was already in the repo, so
"`φ_{H,h} = φ_{U,u} ↔ conjugate`" is now available in both directions at a
common `H`.

## 3. Downstream

```lean
theorem fullyFused_of_intPoint' (H : Subgroup G) (h : H) {p : DRing G →+* ℤ}
    (hp : complexify (DRing G) p = DRing.species H h) : FullyFused H h
```
— no hypotheses.  Together with v_task71 (`adamsStable_of_intPoint`, already
hypothesis-free), **item (2) of the v_task68 chain is completely
unconditional**: an integer point that is a species is Adams-stable and its
pair class is fully fused.

## 4. Verification

Serial, one `taskset -c 0` process at a time:

```
cd lean_dring
taskset -c 0 lake build LeanDring.Even.SpeciesSeparation   # 0 err, 0 warn
taskset -c 0 lake build                                     # 4718 jobs, OK
```

Axiom audit — all seven new declarations
(`evalChar_injective`, `inv_out_mem_normalizer`, `one_mem_fixCoset`,
`of_conjRep_one`, `species_basisElt_self`, `speciesPairSeparation`,
`fullyFused_of_intPoint'`) report

```
[propext, Classical.choice, Quot.sound]
```

New Mathlib imports: `Mathlib.GroupTheory.FiniteAbelian.Duality`,
`Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed`.
The file is in the exploratory layer (not imported by the root module), like
`ConductorDictionaryGalois.lean`; build it by name.

## 5. Remaining surface for `ConductorPairDictionary`

Down from two named Props to **one**:

1. ~~`SpeciesPairSeparation`~~ — **proven** (this task).
2. **The conductor computation** — `conductor = (N_G(H, hH') : H')` (Müller
   Satz 2.3.3) together with "every integer point of `D(G)` *is* a species".
   This second half is the genuine surjectivity statement the brief described
   (species exhaust `Hom(D(G), ℂ)`), and it needs the primitive idempotents of
   `D(G) ⊗ ℚ` — i.e. the rank/dimension count the brief sketched.  With
   item (1) now a theorem, the Dedekind half of that count
   (`count_eq_of_sum_eq`, `species_injective`) is in place; what is missing is
   a finite-free-basis statement for `D(G)` (`basisElt` is defined and its
   species formula proven, but *linear independence / spanning* of the
   `[K, λ]` is not).  That is the natural next task.
