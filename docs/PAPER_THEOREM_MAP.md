# Paper ↔ Lean theorem correspondence

Repository: `lean_dring` (Lean 4.32.0 + Mathlib `v4.32.0`).
Last updated: **2026-08-13**.

## Scope of this table

This table covers the paper's Sections 2–5 (foundations, order-`p⁴` rigidity,
the Gauss-sum twin argument, the order-`5⁵` counterexample) together with odd
order, the Gauss sign and abelian 2-groups — 41 entries, all backed by
`LeanDring.Paper` aliases.

**It does not yet cover Sections 6–7** (the even-order layer: cancellation for
`C₂ × H`, and the recognition theorem for the finite simple groups), which
account for 16 further numbered results. Those results *are* formalized —
`LeanDring/Even/`, 39 modules, `sorry`-free, inside the build closure — and the
relevant declarations are named inline in the paper's own prose, but they have
no `LeanDring.Paper` alias and therefore no row here. Their status, and the
external inputs they carry as explicit named `Prop`s, are set out in the paper
instead (Section 7.6, "What is proved, and under what hypotheses", and
Section 8). Adding alias rows for them is open work.

Every row's **Lean declaration** column names a declaration in
`LeanDring/MainResults.lean` or its verification-facing companion
`LeanDring/CertificateAnchors.lean` — both namespace `LeanDring.Paper`. They
restate each result with its full signature and prints its axiom set. The
**Internal name** column is the declaration that actually carries the proof; the
**File** column is where to read it (all paths relative to this repository's
root, i.e. to `lean_dring/`).

Verify the whole table at once with:

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

| Paper result | Lean declaration | Internal name | File | Status |
|---|---|---|---|---|
| Main theorem: `D(SmallGroup(3125,68)) ≅ D(SmallGroup(3125,69))` | `Paper.dring_isomorphism_of_5_5_twins` | `P5Presentation.dring_equiv_coordinate12` | `LeanDring/P5/Certificate/RingIsomorphism/Twin1/Assembly.lean` | **Proved** |
| …transported to the presented groups `Group 1/2` | `Paper.dring_isomorphism_of_presented_5_5_twins` | `MonRing.congr` ∘ `P5Presentation.normalFormMulEquiv` | `LeanDring/Even/Functorial.lean` | **Proved** |
| The odd-order passage `B(G⁽¹⁾) ≅ B(G⁽²⁾)` | `Paper.burnside_isomorphism_of_5_5_twins` | `OddOrder.burnsideEquivOfOddOrder` | `LeanDring/Theory/OddOrder/OddOrder.lean` | **Proved** |
| The `2724 × 2724` species-table entry match | `Paper.species_table_entry_match_coordinate12` | `P5Presentation.master` | `LeanDring/P5/Certificate/RingIsomorphism/MatchAll.lean` | **Proved** |
| Row-by-row column match under σ | `Paper.row_column_match_coordinate12` | `P5Presentation.hmatch` | `LeanDring/P5/Certificate/RingIsomorphism/Twin1/Assembly.lean` | **Proved** |
| The row equivalence σ on character-pair classes | `Paper.charPairClassEquiv_coordinate12` | `P5Presentation.sigmaEquiv` | `LeanDring/P5/Certificate/RingIsomorphism/Twin2/Sigma.lean` | **Proved** |
| σ selects the aligned row | `Paper.classElt_charPairClassEquiv_orbitRep` | `P5Presentation.classElt_sigmaEquiv_orbRepClass` | `LeanDring/P5/Certificate/RingIsomorphism/Twin2/Sigma.lean` | **Proved** |
| `Coordinate 1/2` ≅ `SmallGroup(3125,68)/(69)` | — | — | GAP | **[COMPUTED]** (caveat ii) |
| `SmallGroup(3125,68) ≇ SmallGroup(3125,69)` as groups | — | — | GAP | **[COMPUTED]** (caveat iii) |

> **Caveat (ii) — presentation identification.** The Lean development proves the
> ring isomorphism for the two groups it *constructs* from an explicit
> fifteen-relator pc presentation (`Coordinate 1`, `Coordinate 2`). That these
> are GAP's `SmallGroup(3125,68)` and `(3125,69)` is an exact external
> computation, not a formalized statement.
>
> **Caveat (iii) — non-isomorphy.** `IsEmpty (Coordinate 1 ≃* Coordinate 2)` is
> **not** formalized. The two groups differ only in `f₂⁵ = f₅` versus
> `f₂⁵ = f₅²`; their non-isomorphy is `[COMPUTED]` (GAP). The counterexample
> statement "there exist non-isomorphic groups with isomorphic D-rings" therefore
> combines one Lean theorem with one external computation, and the paper must say
> so.

## 2. The completeness capstones and the abstract glue

| Paper result | Lean declaration | Internal name | File | Status |
|---|---|---|---|---|
| The 2724 orbit-representative columns are a complete column family (`Coordinate 1`) | `Paper.speciesColsComplete_coordinate1` | `DRing.speciesColsComplete_coordinate1` | `LeanDring/P5/Certificate/SpeciesTable/Twin1/SpeciesComplete.lean` | **Proved** |
| …(`Coordinate 2`) | `Paper.speciesColsComplete_coordinate2` | `DRing.Q2.speciesColsComplete_coordinate2` | `LeanDring/P5/Certificate/SpeciesTable/Twin2/SpeciesComplete.lean` | **Proved** |
| Complete columns + row match ⟹ `D(G) ≅ D(Coordinate 1)` | `Paper.dringEquiv_of_rowMatch_coordinate1` | `DRing.dringEquiv_of_rowMatch_coordinate1` | `LeanDring/P5/Certificate/SpeciesTable/Twin1/SpeciesComplete.lean` | **Proved** |
| …⟹ `D(G) ≅ D(Coordinate 2)` | `Paper.dringEquiv_of_rowMatch_coordinate2` | `DRing.Q2.dringEquiv_of_rowMatch_coordinate2` | `LeanDring/P5/Certificate/SpeciesTable/Twin2/SpeciesComplete.lean` | **Proved** |

## 3. The cell-discharge lemmas — the trusted-computation interface

| Paper result | Lean declaration | Internal name | File | Status |
|---|---|---|---|---|
| Coincident-column cells discharge by `rfl` on the fast code | `Paper.species_eq_of_data_eq` | `P5Presentation.species_eq_of_data_eq` | `LeanDring/P5/Certificate/SpeciesTable/EntrySupport.lean` | **Proved** |
| Divergent-column cells discharge by one kernel `decide` on the cyclotomic fast codes | `Paper.species_eq_of_fastcode_eq` | `P5Presentation.species_eq_of_fastcode_eq` | `LeanDring/P5/Certificate/SpeciesTable/EntrySupport.lean` | **Proved** |

The second lemma is the single point at which exact computation enters the
`5⁵` species-table *cell comparison* (the census layers — subgroups,
conjugacy classes, characters — carry their own kernel `decide`s): all
residual `decide`-discharged cells pass through it, reflecting to
equality in `ℂ` via `P5CyclotomicCode.sumPowers_eq_iff_value_eq`. There is no
`native_decide` anywhere in the development, so the reflection happens in the
kernel, not in compiled code.

## 4. The certified census of the two groups

| Paper result | Lean declaration | Internal name | File | Status |
|---|---|---|---|---|
| The presented group has `5⁵ = 3125` elements | `Paper.card_coordinates` | `P5Presentation.card_coordinates` | `LeanDring/P5/Certificate/Presentation/Presentation.lean` | **Proved** |
| The computable model *is* the presented group: `Coordinate q ≃* Group q` | `Paper.normalFormMulEquiv` | `P5Presentation.normalFormMulEquiv` | `LeanDring/P5/Certificate/ComputableModel/Twin1/ComputableGroup.lean` | **Proved** |
| Subgroup inventory complete (`Coordinate 1`) | `Paper.subgroupInventory_complete_coordinate1` | `P5Presentation.allSubs_complete` | `LeanDring/P5/Certificate/SubgroupInventory/Twin1/FratDischarge.lean` | **Proved** |
| Subgroup inventory complete (`Coordinate 2`) | `Paper.subgroupInventory_complete_coordinate2` | `P5Presentation.Q2.allSubs_complete` | `LeanDring/P5/Certificate/SubgroupInventory/Twin2/FratDischarge.lean` | **Proved** |
| 676 subgroups, by base rank `[1,156,306,181,31,1]` | `Paper.subgroupCount_coordinate1` | `P5Presentation.allBases_card`, `…allBases_strata` | `LeanDring/P5/Certificate/SubgroupInventory/Twin1/AllSubgroups.lean` | **Proved** |
| 148 subgroup conjugacy classes, exhaustive (`Coordinate 1`) | `Paper.subgroupClasses_complete_coordinate1` | `P5Presentation.reps_complete` | `LeanDring/P5/Certificate/ConjugacyClasses/Twin1/ConjClasses.lean` | **Proved** |
| …pairwise non-conjugate (`Coordinate 1`) | `Paper.subgroupClasses_distinct_coordinate1` | `P5Presentation.reps_pairwise_nonconj` | `LeanDring/P5/Certificate/ConjugacyClasses/Twin1/ConjClasses.lean` | **Proved** |
| …exhaustive (`Coordinate 2`) | `Paper.subgroupClasses_complete_coordinate2` | `P5Presentation.Q2.reps_complete` | `LeanDring/P5/Certificate/ConjugacyClasses/Twin2/ConjClasses.lean` | **Proved** |
| …pairwise non-conjugate (`Coordinate 2`) | `Paper.subgroupClasses_distinct_coordinate2` | `P5Presentation.Q2.reps_pairwise_nonconj` | `LeanDring/P5/Certificate/ConjugacyClasses/Twin2/ConjClasses.lean` | **Proved** |
| Certified character lists complete, 5236 total (`Coordinate 1`) | `Paper.characterCount_complete_coordinate1` | `P5Presentation.charsAt_complete_all` | `LeanDring/P5/Certificate/Characters/Twin1/CharCompleteFinal.lean` | **Proved** |
| …(`Coordinate 2`) | `Paper.characterCount_complete_coordinate2` | `P5Presentation.Q2.charsAt_complete_all2` | `LeanDring/P5/Certificate/Characters/Twin2/CharCompleteFull.lean` | **Proved** |
| 2724 normalizer-orbit representatives | `Paper.pairClassTotal_coordinate1` | `P5Presentation.pairClassTotal` | `LeanDring/P5/Certificate/ConjugacyClasses/Twin1/NormOrbits.lean` | **Proved** |
| Orbit-rep index ↔ pair class is a bijection (`Coordinate 1`) | `Paper.pairClassIndex_bijective_coordinate1` | `P5Presentation.orbRepClass_bijective` | `LeanDring/P5/Certificate/ConjugacyClasses/Twin1/PairClassInj.lean` | **Proved** |
| …(`Coordinate 2`) | `Paper.pairClassIndex_bijective_coordinate2` | `P5Presentation.Q2.orbRepClass_bijective` | `LeanDring/P5/Certificate/ConjugacyClasses/Twin2/PairClassInj.lean` | **Proved** |
| `#CharPairClass(Coordinate 1) = 2724` | `Paper.card_charPairClass_coordinate1` | `P5Presentation.card_charPairClass_coordinate1` | `LeanDring/P5/Certificate/ConjugacyClasses/Twin1/PairClassInj.lean` | **Proved** |
| `#CharPairClass(Coordinate 2) = 2724` | `Paper.card_charPairClass_coordinate2` | `P5Presentation.Q2.card_charPairClass_coordinate2` | `LeanDring/P5/Certificate/ConjugacyClasses/Twin2/PairClassInj.lean` | **Proved** |
| `rank_ℤ D(Coordinate 1) = 2724` | `Paper.rank_dring_coordinate1` | `P5Presentation.rank_dring_coordinate1` | `LeanDring/P5/Certificate/ConjugacyClasses/Twin1/PairClassInj.lean` | **Proved** |
| `rank_ℤ D(Coordinate 2) = 2724` | `Paper.rank_dring_coordinate2` | `P5Presentation.Q2.rank_dring_coordinate2` | `LeanDring/P5/Certificate/ConjugacyClasses/Twin2/PairClassInj.lean` | **Proved** |

The semantic content of the census is carried by the *completeness* and
*bijectivity* rows (`allSubs_complete`, `reps_complete`,
`charsAt_complete_all`, `orbRepClass_bijective`). The bare counts
(`allBases_card`, `pairClassTotal`) are `decide` over embedded data and say
nothing about the abstract group on their own; the paper should cite the
semantic rows.

## 5. Order-`p⁴` rigidity

| Paper result | Lean declaration | Internal name | File | Status |
|---|---|---|---|---|
| The exceptional twins (xii)/(xiii) are species-separated, `p ≥ 5` | `Paper.exceptional_p4_twins_separated` | `P4.isEmpty_tableIso_model_model` | `LeanDring/P4/TwinFinal.lean` | **Proved** |
| The 105/105 pairwise separation of the fifteen order-`p⁴` models | `Paper.p4_pairwise_species_distinct` | `P4.p4_pairwise_species_distinct` | `LeanDring/P4/SweepComplete.lean` | **Proved** |
| The exceptional root-of-unity equation has no solution (the mod-8 `ζ₈ₚ` contradiction) | `Paper.order_p4_exceptional_case_impossible` | `P4.value_equation_impossible` | `LeanDring/P4/Endgame.lean` | **Proved** |
| Species tables classify groups of order `p⁴` | `Paper.p4_species_classifies` | `P4.p4_species_classifies` | `LeanDring/P4/Capstone.lean` | **Proved (external classification)** (caveat i) |

> **Caveat (i) — the order-`p⁴` classification wrapper.** The Lean statement
> quantified over *arbitrary* groups of order `p⁴` carries the explicit
> hypothesis `P4Classification p d`: "every group of order `p⁴` is isomorphic to
> one of the fifteen formalized models". That is the classical classification
> (Hölder 1893; Adler–Garlow–Wheland, arXiv:1611.00461). It is **cited, not
> formalized** — the sole external mathematical input at this layer. The
> machine-checked claim is the exhaustive separation of the fifteen Lean models;
> the passage to arbitrary groups uses the cited classification.

## 6. Odd order, Gauss sign, abelian 2-groups

| Paper result | Lean declaration | Internal name | File | Status |
|---|---|---|---|---|
| Müller's odd-order theorem: `D(G) ≅ D(G')` ⟹ `B(G) ≅ B(G')` for odd order | `Paper.burnsideEquivOfOddOrder` | `OddOrder.burnsideEquivOfOddOrder` | `LeanDring/Theory/OddOrder/OddOrder.lean` | **Proved** |
| Gauss's sign theorem: `g(p) = √p` (`p ≡ 1 mod 4`), `i√p` (`p ≡ 3 mod 4`) | `Paper.gauss_eq` | `GaussSign.gauss_eq` | `LeanDring/Theory/Gauss/GaussSignTheorem.lean` | **Proved** |
| `D ⇒ B` for cyclic 2-groups | `Paper.burnsideEquivOfCyclicTwoGroup` | `AbelianTwo.burnsideEquivOfCyclicTwoGroup` | `LeanDring/Theory/DRing/AbelianTwo.lean` | **Proved** |

`GaussSign.gauss_eq` and `GaussSign.rootNumber_χℂ_eq_one`
(`LeanDring/Theory/Gauss/GaussRootNumber.lean`) are not in Mathlib and are the two
upstreamable results of this development.

## 7. Foundations

| Paper result | Lean declaration | Internal name | File | Status |
|---|---|---|---|---|
| The species table is a complete invariant | `Paper.species_injective` | `DRing.species_injective` | `LeanDring/Theory/DRing/SpeciesInjectivity.lean` | **Proved** |
| Marks determine elements of `B(G)` | `Paper.mark_injective` | `BurnsideRing.mark_injective` | `LeanDring/Theory/DRing/MarkInjectivity.lean` | **Proved** |
| `rank_ℤ D(G) = #{(K,λ)}/conjugacy` | `Paper.rank_dring` | `DRing.rank_dring` | `LeanDring/Theory/DRing/FreeBasis.lean` | **Proved** |

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

Everything else in this table is kernel-checked with axiom set contained in
`[propext, Classical.choice, Quot.sound]`.
