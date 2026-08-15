# Paper ↔ Lean theorem correspondence

Repository: `lean_dring` (Lean 4.32.0 + Mathlib `v4.32.0`).
Last updated: **2026-08-15**.

## Scope of this document

This document covers the paper's Sections 2–5 (foundations, order-`p⁴` rigidity,
the Gauss-sum twin argument, the order-`5⁵` counterexample) together with odd
order, the Gauss sign and abelian 2-groups — 41 entries, all backed by
`LeanDring.Paper` aliases.

**It does not yet cover Sections 6–7** (the even-order layer: cancellation for
`C₂ × H`, and the recognition theorem for the finite simple groups), which
account for 16 further numbered results. Those results *are* formalized —
`LeanDring/Even/`, 39 modules, `sorry`-free, inside the build closure — and the
relevant declarations are named inline in the paper's own prose, but they have
no `LeanDring.Paper` alias and therefore no entry here. Their status, and the
external inputs they carry as explicit named `Prop`s, are set out in the paper
instead (Section 7.6, "What is proved, and under what hypotheses", and
Section 8). Adding alias entries for them is open work.

Every entry's **Lean declaration** field names a declaration in
`LeanDring/MainResults.lean` or its verification-facing companion
`LeanDring/CertificateAnchors.lean` — both namespace `LeanDring.Paper`. They
restate each result with its full signature and prints its axiom set. The
**Internal name** field is the declaration that actually carries the proof; the
**File** field is where to read it (all paths relative to this repository's
root, i.e. to `lean_dring/`).

Verify all entries at once with:

```bash
cd lean_dring
lake env lean LeanDring/MainResults.lean
lake env lean LeanDring/CertificateAnchors.lean
```

Every printed axiom set is a subset of `[propext, Classical.choice, Quot.sound]`.

## Status legend

| status | meaning |
|---|---|
| **Proved** | unconditional, kernel-checked in Lean; no external input |
| **Proved (external classification)** | Lean-checked given the classical classification of groups of order `p⁴`, which is cited, not formalized |
| **[COMPUTED]** | established by an exact external computation (GAP); *not* a Lean theorem |

---

## 1. Main theorem — failure of D-ring rigidity at order `p⁵`

- **Main theorem: `D(SmallGroup(3125,68)) ≅ D(SmallGroup(3125,69))`** — **Proved**<br>
  restated as `Paper.dring_isomorphism_of_5_5_twins`<br>
  proved by `P5Presentation.dring_equiv_coordinate12` in `LeanDring/P5/Certificate/RingIsomorphism/Twin1/Assembly.lean`

- **…transported to the presented groups `Group 1/2`** — **Proved**<br>
  restated as `Paper.dring_isomorphism_of_presented_5_5_twins`<br>
  proved by `MonRing.congr` ∘ `P5Presentation.normalFormMulEquiv` in `LeanDring/Even/Functorial.lean`

- **The odd-order passage `B(G⁽¹⁾) ≅ B(G⁽²⁾)`** — **Proved**<br>
  restated as `Paper.burnside_isomorphism_of_5_5_twins`<br>
  proved by `OddOrder.burnsideEquivOfOddOrder` in `LeanDring/Theory/OddOrder/OddOrder.lean`

- **The `2724 × 2724` species-table entry match** — **Proved**<br>
  restated as `Paper.species_table_entry_match_coordinate12`<br>
  proved by `P5Presentation.master` in `LeanDring/P5/Certificate/RingIsomorphism/MatchAll.lean`

- **Row-by-row column match under σ** — **Proved**<br>
  restated as `Paper.row_column_match_coordinate12`<br>
  proved by `P5Presentation.hmatch` in `LeanDring/P5/Certificate/RingIsomorphism/Twin1/Assembly.lean`

- **The row equivalence σ on character-pair classes** — **Proved**<br>
  restated as `Paper.charPairClassEquiv_coordinate12`<br>
  proved by `P5Presentation.sigmaEquiv` in `LeanDring/P5/Certificate/RingIsomorphism/Twin2/Sigma.lean`

- **σ selects the aligned row** — **Proved**<br>
  restated as `Paper.classElt_charPairClassEquiv_orbitRep`<br>
  proved by `P5Presentation.classElt_sigmaEquiv_orbRepClass` in `LeanDring/P5/Certificate/RingIsomorphism/Twin2/Sigma.lean`

- **`Coordinate 1/2` ≅ `SmallGroup(3125,68)/(69)`** — **[COMPUTED]** (caveat ii) — GAP; no Lean declaration

- **`SmallGroup(3125,68) ≇ SmallGroup(3125,69)` as groups** — **[COMPUTED]** (caveat iii) — GAP; no Lean declaration

> **Caveat (ii) — presentation identification.** The Lean development proves the
> ring isomorphism for the two groups it *constructs* from an explicit
> fifteen-relator pc presentation (`Coordinate 1`, `Coordinate 2`). That these
> are GAP's `SmallGroup(3125,68)` and `(3125,69)` is an exact external
> computation, not a formalized statement.
>
> **Caveat (iii) — non-isomorphy.** `IsEmpty (Coordinate 1 ≃* Coordinate 2)` is
> **not** formalized. The two groups differ only in `f₂⁵ = f₅` versus
> `f₂⁵ = f₅²`; their non-isomorphy is `[COMPUTED]` (GAP) and is a documented
> fact of the literature — the pair is one of the Eick–Müller Brauer pairs,
> independently verifiable from the SmallGroups library. The counterexample
> statement "there exist non-isomorphic groups with isomorphic D-rings" therefore
> combines one Lean theorem with one external computation, and the paper must say
> so.

## 2. The completeness capstones and the abstract glue

- **The 2724 orbit-representative columns are a complete column family (`Coordinate 1`)** — **Proved**<br>
  restated as `Paper.speciesColsComplete_coordinate1`<br>
  proved by `DRing.speciesColsComplete_coordinate1` in `LeanDring/P5/Certificate/SpeciesTable/Twin1/SpeciesComplete.lean`

- **…(`Coordinate 2`)** — **Proved**<br>
  restated as `Paper.speciesColsComplete_coordinate2`<br>
  proved by `DRing.Q2.speciesColsComplete_coordinate2` in `LeanDring/P5/Certificate/SpeciesTable/Twin2/SpeciesComplete.lean`

- **Complete columns + row match ⟹ `D(G) ≅ D(Coordinate 1)`** — **Proved**<br>
  restated as `Paper.dringEquiv_of_rowMatch_coordinate1`<br>
  proved by `DRing.dringEquiv_of_rowMatch_coordinate1` in `LeanDring/P5/Certificate/SpeciesTable/Twin1/SpeciesComplete.lean`

- **…⟹ `D(G) ≅ D(Coordinate 2)`** — **Proved**<br>
  restated as `Paper.dringEquiv_of_rowMatch_coordinate2`<br>
  proved by `DRing.Q2.dringEquiv_of_rowMatch_coordinate2` in `LeanDring/P5/Certificate/SpeciesTable/Twin2/SpeciesComplete.lean`

## 3. The cell-discharge lemmas — the trusted-computation interface

- **Coincident-column cells discharge by `rfl` on the fast code** — **Proved**<br>
  restated as `Paper.species_eq_of_data_eq`<br>
  proved by `P5Presentation.species_eq_of_data_eq` in `LeanDring/P5/Certificate/SpeciesTable/EntrySupport.lean`

- **Divergent-column cells discharge by one kernel `decide` on the cyclotomic fast codes** — **Proved**<br>
  restated as `Paper.species_eq_of_fastcode_eq`<br>
  proved by `P5Presentation.species_eq_of_fastcode_eq` in `LeanDring/P5/Certificate/SpeciesTable/EntrySupport.lean`

The second lemma is the single point at which exact computation enters the
`5⁵` species-table *cell comparison* (the census layers — subgroups,
conjugacy classes, characters — carry their own kernel `decide`s): all
residual `decide`-discharged cells pass through it, reflecting to
equality in `ℂ` via `P5CyclotomicCode.sumPowers_eq_iff_value_eq`. There is no
`native_decide` anywhere in the development, so the reflection happens in the
kernel, not in compiled code.

## 4. The certified census of the two groups

- **The presented group has `5⁵ = 3125` elements** — **Proved**<br>
  restated as `Paper.card_coordinates`<br>
  proved by `P5Presentation.card_coordinates` in `LeanDring/P5/Certificate/Presentation/Presentation.lean`

- **The computable model *is* the presented group: `Coordinate q ≃* Group q`** — **Proved**<br>
  restated as `Paper.normalFormMulEquiv`<br>
  proved by `P5Presentation.normalFormMulEquiv` in `LeanDring/P5/Certificate/ComputableModel/Twin1/ComputableGroup.lean`

- **Subgroup inventory complete (`Coordinate 1`)** — **Proved**<br>
  restated as `Paper.subgroupInventory_complete_coordinate1`<br>
  proved by `P5Presentation.allSubs_complete` in `LeanDring/P5/Certificate/SubgroupInventory/Twin1/FratDischarge.lean`

- **Subgroup inventory complete (`Coordinate 2`)** — **Proved**<br>
  restated as `Paper.subgroupInventory_complete_coordinate2`<br>
  proved by `P5Presentation.Q2.allSubs_complete` in `LeanDring/P5/Certificate/SubgroupInventory/Twin2/FratDischarge.lean`

- **676 subgroups, by base rank `[1,156,306,181,31,1]`** — **Proved**<br>
  restated as `Paper.subgroupCount_coordinate1`<br>
  proved by `P5Presentation.allBases_card`, `…allBases_strata` in `LeanDring/P5/Certificate/SubgroupInventory/Twin1/AllSubgroups.lean`

- **148 subgroup conjugacy classes, exhaustive (`Coordinate 1`)** — **Proved**<br>
  restated as `Paper.subgroupClasses_complete_coordinate1`<br>
  proved by `P5Presentation.reps_complete` in `LeanDring/P5/Certificate/ConjugacyClasses/Twin1/ConjClasses.lean`

- **…pairwise non-conjugate (`Coordinate 1`)** — **Proved**<br>
  restated as `Paper.subgroupClasses_distinct_coordinate1`<br>
  proved by `P5Presentation.reps_pairwise_nonconj` in `LeanDring/P5/Certificate/ConjugacyClasses/Twin1/ConjClasses.lean`

- **…exhaustive (`Coordinate 2`)** — **Proved**<br>
  restated as `Paper.subgroupClasses_complete_coordinate2`<br>
  proved by `P5Presentation.Q2.reps_complete` in `LeanDring/P5/Certificate/ConjugacyClasses/Twin2/ConjClasses.lean`

- **…pairwise non-conjugate (`Coordinate 2`)** — **Proved**<br>
  restated as `Paper.subgroupClasses_distinct_coordinate2`<br>
  proved by `P5Presentation.Q2.reps_pairwise_nonconj` in `LeanDring/P5/Certificate/ConjugacyClasses/Twin2/ConjClasses.lean`

- **Certified character lists complete, 5236 total (`Coordinate 1`)** — **Proved**<br>
  restated as `Paper.characterCount_complete_coordinate1`<br>
  proved by `P5Presentation.charsAt_complete_all` in `LeanDring/P5/Certificate/Characters/Twin1/CharCompleteFinal.lean`

- **…(`Coordinate 2`)** — **Proved**<br>
  restated as `Paper.characterCount_complete_coordinate2`<br>
  proved by `P5Presentation.Q2.charsAt_complete_all2` in `LeanDring/P5/Certificate/Characters/Twin2/CharCompleteFull.lean`

- **2724 normalizer-orbit representatives** — **Proved**<br>
  restated as `Paper.pairClassTotal_coordinate1`<br>
  proved by `P5Presentation.pairClassTotal` in `LeanDring/P5/Certificate/ConjugacyClasses/Twin1/NormOrbits.lean`

- **Orbit-rep index ↔ pair class is a bijection (`Coordinate 1`)** — **Proved**<br>
  restated as `Paper.pairClassIndex_bijective_coordinate1`<br>
  proved by `P5Presentation.orbRepClass_bijective` in `LeanDring/P5/Certificate/ConjugacyClasses/Twin1/PairClassInj.lean`

- **…(`Coordinate 2`)** — **Proved**<br>
  restated as `Paper.pairClassIndex_bijective_coordinate2`<br>
  proved by `P5Presentation.Q2.orbRepClass_bijective` in `LeanDring/P5/Certificate/ConjugacyClasses/Twin2/PairClassInj.lean`

- **`#CharPairClass(Coordinate 1) = 2724`** — **Proved**<br>
  restated as `Paper.card_charPairClass_coordinate1`<br>
  proved by `P5Presentation.card_charPairClass_coordinate1` in `LeanDring/P5/Certificate/ConjugacyClasses/Twin1/PairClassInj.lean`

- **`#CharPairClass(Coordinate 2) = 2724`** — **Proved**<br>
  restated as `Paper.card_charPairClass_coordinate2`<br>
  proved by `P5Presentation.Q2.card_charPairClass_coordinate2` in `LeanDring/P5/Certificate/ConjugacyClasses/Twin2/PairClassInj.lean`

- **`rank_ℤ D(Coordinate 1) = 2724`** — **Proved**<br>
  restated as `Paper.rank_dring_coordinate1`<br>
  proved by `P5Presentation.rank_dring_coordinate1` in `LeanDring/P5/Certificate/ConjugacyClasses/Twin1/PairClassInj.lean`

- **`rank_ℤ D(Coordinate 2) = 2724`** — **Proved**<br>
  restated as `Paper.rank_dring_coordinate2`<br>
  proved by `P5Presentation.Q2.rank_dring_coordinate2` in `LeanDring/P5/Certificate/ConjugacyClasses/Twin2/PairClassInj.lean`

The semantic content of the census is carried by the *completeness* and
*bijectivity* entries (`allSubs_complete`, `reps_complete`,
`charsAt_complete_all`, `orbRepClass_bijective`). The bare counts
(`allBases_card`, `pairClassTotal`) are `decide` over embedded data and say
nothing about the abstract group on their own; the paper should cite the
semantic entries.

## 5. Order-`p⁴` rigidity

- **The exceptional twins (xii)/(xiii) are species-separated, `p ≥ 5`** — **Proved**<br>
  restated as `Paper.exceptional_p4_twins_separated`<br>
  proved by `P4.isEmpty_tableIso_model_model` in `LeanDring/P4/TwinFinal.lean`

- **The 105/105 pairwise separation of the fifteen order-`p⁴` models** — **Proved**<br>
  restated as `Paper.p4_pairwise_species_distinct`<br>
  proved by `P4.p4_pairwise_species_distinct` in `LeanDring/P4/SweepComplete.lean`

- **The exceptional root-of-unity equation has no solution (the mod-8 `ζ₈ₚ` contradiction)** — **Proved**<br>
  restated as `Paper.order_p4_exceptional_case_impossible`<br>
  proved by `P4.value_equation_impossible` in `LeanDring/P4/Endgame.lean`

- **Species tables classify groups of order `p⁴`** — **Proved (external classification)** (caveat i)<br>
  restated as `Paper.p4_species_classifies`<br>
  proved by `P4.p4_species_classifies` in `LeanDring/P4/Capstone.lean`

> **Caveat (i) — the order-`p⁴` classification wrapper.** The Lean statement
> quantified over *arbitrary* groups of order `p⁴` carries the explicit
> hypothesis `P4Classification p d`: "every group of order `p⁴` is isomorphic to
> one of the fifteen formalized models". That is the classical classification
> (Hölder 1893; Adler–Garlow–Wheland, arXiv:1611.00461). It is **cited, not
> formalized** — the sole external mathematical input at this layer. The
> machine-checked claim is the exhaustive separation of the fifteen Lean models;
> the passage to arbitrary groups uses the cited classification.

## 6. Odd order, Gauss sign, abelian 2-groups

- **Müller's odd-order theorem: `D(G) ≅ D(G')` ⟹ `B(G) ≅ B(G')` for odd order** — **Proved**<br>
  restated as `Paper.burnsideEquivOfOddOrder`<br>
  proved by `OddOrder.burnsideEquivOfOddOrder` in `LeanDring/Theory/OddOrder/OddOrder.lean`

- **Gauss's sign theorem: `g(p) = √p` (`p ≡ 1 mod 4`), `i√p` (`p ≡ 3 mod 4`)** — **Proved**<br>
  restated as `Paper.gauss_eq`<br>
  proved by `GaussSign.gauss_eq` in `LeanDring/Theory/Gauss/GaussSignTheorem.lean`

- **`D ⇒ B` for cyclic 2-groups** — **Proved**<br>
  restated as `Paper.burnsideEquivOfCyclicTwoGroup`<br>
  proved by `AbelianTwo.burnsideEquivOfCyclicTwoGroup` in `LeanDring/Theory/DRing/AbelianTwo.lean`

`GaussSign.gauss_eq` and `GaussSign.rootNumber_χℂ_eq_one`
(`LeanDring/Theory/Gauss/GaussRootNumber.lean`) are not in Mathlib and are the two
upstreamable results of this development.

## 7. Foundations

- **The species table is a complete invariant** — **Proved**<br>
  restated as `Paper.species_injective`<br>
  proved by `DRing.species_injective` in `LeanDring/Theory/DRing/SpeciesInjectivity.lean`

- **Marks determine elements of `B(G)`** — **Proved**<br>
  restated as `Paper.mark_injective`<br>
  proved by `BurnsideRing.mark_injective` in `LeanDring/Theory/DRing/MarkInjectivity.lean`

- **`rank_ℤ D(G) = #{(K,λ)}/conjugacy`** — **Proved**<br>
  restated as `Paper.rank_dring`<br>
  proved by `DRing.rank_dring` in `LeanDring/Theory/DRing/FreeBasis.lean`

Further foundational results cited in passing by the paper and registered in
`LeanDring/AxiomAudit.lean` but not re-exported: `FinGSet.isIso_of_fix_eq`,
`DRing.basisElt_eq_iff`, `MonGSet.isIso_induced_iff_conjPair`,
`MonGSet.census_congr`, `DRing.burnsideEquivOfPsiEquivariant`,
`DRing.burnsideEquivOfPsiTwoEquivariant`, `DRing.basisOfCharPairClass`,
`DRing.range_eta_eq_fix_psi_two`, `DRing.SpeciesTableIso.card_subgroups_eq`,
`CyclotomicCode.reduce_eq_iff_eval_eq`.

## 8. Superseded

| item | note |
|---|---|
| `P5Presentation.p5_dring_iso_of_speciesMatch` (`LeanDring/P5/Certificate/Support/Counterexample.lean`) | The pre-2026-07-27 conditional route: the `5⁵` isomorphism granted a `HasSpeciesMatch` hypothesis supplied by GAP. Superseded by the unconditional `dring_equiv_coordinate12`. Retained as an abstract bridge lemma; still audited. |

## Summary of external inputs

The paper's claims rest on exactly three things outside Lean:

1. the classical classification of groups of order `p⁴` (caveat i) — a cited
   theorem of the literature;
2. the identification of the Lean pc-presentations with GAP's
   `SmallGroup(3125,68)` / `(3125,69)` (caveat ii) — an exact computation;
3. the non-isomorphy of those two groups (caveat iii) — an exact computation.

Everything else in this document is kernel-checked with axiom set contained in
`[propext, Classical.choice, Quot.sound]`.
